//Compute n_{Q,i}
compute_n := function(i,d,p);
	return Ceiling( (p-1-i)*d /p);
end function;

//numbers n = -1 mod p with -a \geq n \geq -b 
negative_ones := function(a,b,p);
    return Ceiling(b/p)-Ceiling((a-1)/p);
end function;

//dim H^0(P^1,\ker V(n Q))
dim_kerVX := function(n,p); 
    return n - Ceiling(n/p);
end function;
    
//is a + d*k = 1 mod p for k<=i, for use in computing T
check_mults := function(a,d,i,p);
    k :=( (1-a)* Modinv(d,p)) mod p ;
    return not (k gt i);
end function;

//lower bounds over P^1: compute L(\pi,P^1) exactly
lower_bound := function(d,p);
    lowerbound:= 0;
    optimum:=0;
    
    for i in [0..p-1] do
        //dim of space
        domain:=0;
        
        //relations
        relations := 0;
        
        ai := compute_n(i,d,p);
        for j in [0..i] do
            domain:=domain+dim_kerVX(compute_n(j,d,p),p);
            relations := relations + negative_ones(compute_n(j,d,p)+1,ai + (i-j) * d,p);
    	end for;
        if domain-relations gt lowerbound then
            lowerbound := domain-relations; 
            optimum := i;   
    	end if;
            
    end for;
    //redprint "Opt",optimum;    
    return lowerbound;
end function;

pole_order := function(i,d,p);
	return Ceiling( (p-1-i)*d /p);
end function;

//for multiple poles, replace d+1 by sum of d's +1
compute_genus := function(d,p);
    return Integers()!((d+1-2) * (p-1)/2);
end function;

//need to treat choosing from 0 things as 1
modified_binomial := function(n,m);
    if n eq 0 then
        return 1;
    end if;
    return Binomial(n,m);
end function;

//function f defining extension, d, prime p, K coefficient field
//order the basis of differentials at t^{-2} dt, t^{-3} dt, ..., t^{-2} dt y, t^{-3} dt y, ...
build_matrix := function(f,d,FF);
    t := FF.1;  //generator of function field
    p := Characteristic(FF);
    g := compute_genus(d,p);
    elements := [ ]; //ordered going across columns one by one.  
    Q := Zeroes(t)[1]; //the point (0,0)

    indexes := [ ]; //the index of where the y^i differentials start
    count := 0;
    for i in [0..(p-1)] do
        Append(~indexes, count+1 ); // add one because of 1-based array indexing.  This is the only thing that will be changed when switching to C's 0-based indexing
        count := count + Max(pole_order(i,d,p)-1,0);
    end for;
    //we're building the matrix one column at a time, except we really are doing the transpose.  Some efficiency could be gained by building it in a different order using random access to an array instead of appending
// in that case, the indexes will be quite helpful

    if count ne g then
        print "Genus seems incompatible",count,g;
    end if;

    //build rows
    for i in [0..p-1] do
        for m in [2..pole_order(i,d,p)] do
            //get the part of Cartier( t^(-m) dt y^i) involving y^j
            for j in [0..p-1] do
                if j le i then
                    basic_expression := (-1)^(i-j) * f^(i-j) * modified_binomial(i,j) *t^(-m) ; //improvement: compute these all at once to avoid duplicating work
                    pseries:= Expand(basic_expression,Q:RelPrec:=d*p);  //write as power series centered at Q=0,  RelPrec says how many positive terms to compute
                    for k in [2..pole_order(j,d,p)] do
                        Append(~elements,Coefficient(pseries,p-1-p*k)); //coefficient of t^k dt y^j in Cartier( t^(-m) dt y^i )
                    end for;
                else
                    for k in [2..pole_order(j,d,p)] do
                        Append(~elements,0);  //automatically nothing here
                    end for;
                end if;
            end for;
        end for;
    end for;
    
    return elements;
end function;

//Compute the a-number of y^p -y = f, where f has a pole of degree d at 0
anumber := function(f,d,FF);
    elements := build_matrix(f,d,FF);
    g := compute_genus(d,Characteristic(FF));
    A := Transpose(Matrix(g,g,elements));
    return g-Rank(A);
end function;


rand_poly:=function(t,d,p) ;
    K:=GF(p);
    poly := t^(-d) ; //issue: what is t
    for i in [1..d-1] do
        if (i mod p ne 0) then
            poly := poly + Random(K)*t^(-i);
        end if;
    end for;
    return poly;
end function;

for p in PrimesInInterval(3,23) do
    K := GF(p);
    R<t> := FunctionField(K);
    for deg in [2*p-1 .. p^2-2 by p] do

        minimal_found := false;
        while minimal_found eq false do

            h:=rand_poly(t,deg,p);
            minimal_found := anumber(h,deg,R) eq lower_bound(deg,p);

        end while;
        fprintf "listofpolynomials.txt", "%3o \n", h;
        printf "minimal found for p = %3o and d = %3o \n",p,deg;
    end for;
end for;
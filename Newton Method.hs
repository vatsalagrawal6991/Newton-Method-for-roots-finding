import System.Random (randomRs,mkStdGen)
{-///////////////////////////////////////////////////////////////////////////////////////////////////////
********************Problem 1 - Listing and Sorting*****************************************
-}
{-**************************************************************************************
1.1) Tail recursive reversal of list
-}
tailReversal a =    case a of
                              []->[]
                              [x]->[x]
                              (x:l)-> reversal l [x]

reversal a c = let  (d:l)=a
               in   if a==[]
                    then c
                    else reversal l (d:c)
{-Proof- 
specs -        reversal a c = c if a is empty; 
                              reversal l (d:c) when a is of form (d:l)

Invariant -    At any iteration of loop say k and list size n,k<n we have 
               tailReversal a =  tailReversal x ++ c  , here x is list with n-k last elemnts of a
               also, length c + length x = length a
     
     Base Case:at k=0 we have 
               tailReversal a =  tailReversal x ++ c
               we have c as empty and x have n elements 
               Thus tailReversal a =  tailReversal x
               Thus Base Case Proved 
     IH :      Let for any k<n step our invariant is true 
               i.e tailReversal a =  tailReversal x ++ c 
     IS :      Now for any step k+1 we have 
               tailReversal x' ++ c'
               Now as x' is of length n-k-1 and c of size k+1
               also we have c as w:c (list form)
               Thus our equation can become tailReversal x' ++[w]++ c
               Now if we add w to x' by adding it into front as we have removed it from front of list which form x'
               we have tailReversal x ++ c
               This is same as IH 
               thus our inductive hypothesis hold true and we have proved tailReversal a =  tailReversal x ++ c 

Time analysis: T(n)=     1 for n=0
                         T(n-1)+1 for n>0
               on solving this we have general equation as T(n)=T(n-k)+k
               putting k=0 we have T(n)=O(n)
               Thus we have T(n)=O(n)
-}


{-*******************************************************************************************************
1.2) Tail recursive merge function (of Merge sort (Merge list and sort them))
-}
tailMerge a b
               | a==[] = b
               | b==[] = a
               | otherwise = merge a b []

merge a b e    | a==[] = e++b
               | b==[] = e++a
               | otherwise =  let  (y:z)=a
                                   (x:w)=b
                              in   if y == x
                                   then merge z w (e++[y]++[x])
                                   else if y < x
                                        then merge z b (e++[y])
                                   else merge a w (e++[x])

{-Proof- 
specs -        merge a b e =  e++b if a is empty;
                              e++a if b is empty;
                              [] if both empty 
                              merge z w (e++[y]++[x]) when y==x 
                              merge z b (e++[y]) when y<x
                              merge a w (e++[x]) when x>y  where a is of form (y:z) and b of (x:w)

Invariant -    At any iteration of loop say k and list a size n1 and b size n2 ,k<n1+n2 we have 
               tailMerge a b =  e++ tailMerge m n  , here e is of size k and also c is sorted
               also, length a + length b = length e + length m +length n
     
     Base Case:at k=0 we have 
               tailmerge a b=  e ++ tailMerge m n 
               we have e as empty and m n have same elements as a b 
               Thus tailmerge a b=  tailMerge m n
               Thus Base Case Proved 
     IH :      Let for any k<n1+n2 step our invariant is true 
               i.e tailmerge a b=  e ++ tailMerge m n  
     IS :      Now for any step k+1 we have 
               e' ++ tailMerge m' n' 
               i.e e' ++ lexiographic ordering of merge of m' and n'
               Now as e' is of length k+1 and m'+n' of size n1+n2-k-1
               also we have e' as of form e++[x] or e++[x]++[x]  (list form)
               Thus our equation can become e++[x]++tailMerge m' n'
               Now as per case 1 if we have head of m greater than head of n then x will be head of n 
               Thus we have e++ tailMerge m n
               Now as per case 2 if we have head of m less than head of n then x will be head of m 
               Thus we have e++ tailMerge m n
               Now as per case 2 if we have head of m equal head of n then x will be head of m and n both
               Thus we have e++ tailMerge m n
               This is same as IH for all 3 cases
               thus our inductive hypothesis hold true and we have proved tailmerge a b=  e ++ tailMerge m n

Time analysis: T(n1+n2)=      1 for n1=0 or n2=0
                              T(n1+n2-1)+1 for n1>0, n2>0
               on solving this we have general equation as T(n)=T(n1+n2-k)+k
               putting k=0 we have T(n1+n2)=O(n1+n2)
               Thus we have T(n1+n2)=O(n1+n2)
-}



{-******************************************************************************************
1.3) Tail recursive Fibonnaci 
-}

tailFibo n     | n==0 = 0
               | n==1 = 1
               | otherwise = fibo n 1 2 1

fibo n b c d = if c==n
               then d
               else fibo n d (c+1) (d+b)

{-Proof- 
specs -        fibbo n b c d =d if c==n;
                              fibo n d (c+1) (d+b) otherwise; 

Invariant -    At any iteration of loop say k and number n ,k<n we have 
               tailFibo n =  x*fibo(k)+y*fibo(k-1) here x and y are some varable integer which increase as k increase
               or in simple words tailFibo k+1 = tailFibo K + tailFibo k-1
               Note tailFibo(k)=d and tailFibo(k-1)=b
     
     Base Case:at k=1 we have 
               tailFibo k+1 = tailFibo K + tailFibo k-1
               tailFibo k+1 = 1
               tailFibo K + tailFibo k-1 = 0 +1=1
               Thus tailFibo k+1 = tailFibo K + tailFibo k-1
               Thus Base Case Proved 
     IH :      Let for any k<n step our invariant is true 
               i.e tailFibo n =  x*tailFibo(k)+y*tailFibo(k-1)
               and   tailFibo k+1 = tailFibo K + tailFibo k-1
     IS :      Now for any step k+1 we have 
               tailFibo n =  x'*tailFibo(k+1)+y'*tailFibo(k)
               and   tailFibo k+2 = tailFibo K + tailFibo k+1 
               Now x'*tailFibo(k+1)+y'*tailFibo(k)=x'*(tailFibo(k)+tailFibo(k-1))+y'*tailFibo(k)
               = (x'+y')tailFibo(k)+x'tailFibo(k-1)
               This is same as IH tailFibo n =  x*tailFibo(k)+y*tailFibo(k-1)
               thus our inductive hypothesis hold true and we have proved

Time analysis: T(n)=     1 for n=0
                         T(n-1)+1 for n>0
               on solving this we have general equation as T(n)=T(n-k)+k
               putting k=0 we have T(n)=O(n)
               Thus we have T(n)=O(n)
-}


{-******************************************************************************************************
1.4) Tail recursive insertion sort
-}
tailInsertion a =   case a of
                              []->[]
                              [x]->[x]
                              (x:z)->sorting z [x]

sorting a c=   let  (d:l)=a
               in   if a==[]
                    then c
                    else sorting l (insertion d c [])

insertion d c f =   let (e:l2)=c
                    in   if c==[]
                         then f++[d]
                         else if d<=e
                              then f++[d]++c
                         else insertion d l2 (f++[e])

{-Proof- 
specs -        sorting a c=   c if a==[];
                              sorting l (insertion d c []) otherwise where a is of form (d:l); 

Invariant -    At any iteration of loop say k and length n ,k<n we have 
               sorting a [] =  sorting x c here 
               length x + length c = length a
               and c is sorted containg starting k elemts of n and a is unsorted containg last  n-k elements
     
     Base Case:at k=0 we have 
               sorting a [] =  sorting x c 
               c is null here
               so that length a = length x
               Thus sorting a [] =  sorting x c 
               Thus Base Case Proved 
     IH :      Let for any k<n step our invariant is true 
               i.e sorting a [] =  sorting x c here 
               length x + length c = length a
               and c is sorted containg starting k elemts of n and a is unsorted containg last  n-k elements
     IS :      Now for any step k+1 we have 
               sorting a [] =  sorting x' c'
               but c is sorted as there is one element in c' which when take out from c' it will become c 
               and that element is inserted by considering all elemnet in c
               Thus our  sorting a [] =  sorting x' c'= sorting x c 
               thus our inductive hypothesis hold true and we have proved

Time analysis: T(n)=     1 for n=0
                         T(n-1)+n for n>0
               on solving this we have general equation as T(n)=T(n-k)+n+n-1+n-2.........+n-K+1
               putting k=0 we have T(n)=O(n^2)
               Thus we have T(n)=O(n^2)
-}



{-*************************************************************************************************************
1.5) recursive quick sort
-}

recursiveQuick a =  case a of
                              [] -> []
                              [x] -> [x]
                              (y:z)->   let (b,c)=partition z y [] []
                                        in recursiveQuick b ++ [y] ++ recursiveQuick c

partition a y b c= case a of
                              []->(b,c)
                              (x:w) ->  if x<=y
                                   then partition w y (x:b) c
                                   else partition w y b (x:c)


{-Proof- 
specs -        recursiveQuick a=   [] if a==[];
                                   recursiveQuick b ++ [y] ++ recursiveQuick c  if a= (y:z)
                                        b and c are partition on pivot y
     
     Base Case:at a=[] we have 
               we have recursiveQuick =[]
               also as a is null so sorting will also result null  
               Thus Base Case Proved 
     IH :      Let for any k<n step our algo is true, n is length of a
               i.e recursiveQuick x is true  and x is of length k
               recursiveQuick x= recursiveQuick b' ++ [y] ++ recursiveQuick c'
     IS :      Now for any step n>k we have 
               recursiveQuick a=   recursiveQuick b ++ [y] ++ recursiveQuick c
               here y is put at correct position due to the partition and b an c are of length less than n 
               so by our IH recursiveQuick b and recursiveQuick c will give correct sorted list and y is placed at right position
               in this sorted list between 2 sorted partition and partition left to it has element value less than it and right one has element more than it
               Thus our  recursiveQuick a will give corrrect sorted array
               thus our inductive hypothesis hold true and we have proved

Time analysis: T(n)
          average case=       1 for n=0
                              T(n/2)+T(n/2)+n for n>0
                              on solving this we have general equation as T(n)=T k(n/2^k)+k(n/2^k)+kn
                              putting k=0 we have T(n)=O(n*logn)
                              Thus we have T(n)=O(n*logn)
          Worst case=         1 for n=0
                              T(n-1)+n for n>0
                              on solving this we have T(n)=O(n^2)
                              Thus we have T(n)=O(n^2)
-}

{-**************************************************************************************************************
1.6) recursive binary search
-}

recursiveBinary a b c d= let m = quot (c+d) 2
                         in   if c==d
                              then if (a!!c)==b
                                   then "match at index "++show m
                                   else "not match"
                              else if c<d
                                   then if (a!!m)==b
                                        then "match at index "++show m
                                        else if (a!!m)< b
                                             then recursiveBinary a b (m+1) d
                                        else recursiveBinary a b c (m-1)
                              else  "not match"



{-Proof- 
specs -        recursiveBinary a=  found if c==d & a at c = b;
                                   not found if c==d & a at c != b
                                   found if c<d && a at m = b 
                                   recursiveBinary a b (m+1) d if c<d && a at m < b 
                                   recursiveBinary a b c (m-1) if c<d && a at m < b
                                   no found if c>d
                                   
     
     Base Case:at c==d we have
               only one elemnt in list a and if it equal b 
               then found otherwise not found 
               this is satisfied by our specs  
               found if c==d & a at c = b;
               not found if c==d & a at c != b 
               Thus Base Case Proved 
     IH :      Let for any k<n our algo is true, k is length of d-c+1
               i.e recursiveBinary a' b' c' d' is true and give correct answer
     IS :      Now for any step n>k we have 
               recursiveBinary a b c d =     recursiveBinary a b (m+1) d if c<d && a at m < b 
                                             recursiveBinary a b c (m-1) if c<d && a at m < b
               Case 1: when m<b
               we have recursiveBinary a b (m+1) d 
               now d-m-1+1 is less than n 
               Thus by Ih it gives correct answer
               also for all other elennt other than in range m+1 and d, they are less than b and m
               Case 2: when m>b
               we have recursiveBinary a b c (m-1)
               now m-1-d+1 is less than n 
               Thus by Ih it gives correct answer
               also for all other elennt other than in range m-1 and b, they are greater than b and m
               Thus our  recursiveBinary will give corrrect answer
               thus our inductive hypothesis hold true and we have proved

Time analysis: T(n)=1 for n=0
                    T(n/2)+1/+n for n>0
               on solving this we have general equation as T(n)=T (n/2^k)+k
               putting k=0 we have T(n)=O(logn)
               Thus we have T(n)=O(logn)
          
-}


{-///////////////////////////////////////////////////////////////////////////////////////////////////////////
********************Problem 2 - Primality Testing*****************************************
-}

prime n q =    let  b=randomgen n q 
                         --b=quot (n-1) q
               in
                    if n<=1 || q>n
                    then show n++" Is Not Prime"
                    else if n==2 || n==3
                         then show n++" Is Prime"
                    else primek n q b 0.0 1

primek n q b p a=   if    (p<=1.0 && a<=q) && b/=[]
                    then if isp n r n==r
                              --isp n (a*b) n==b
                         then primek n q bs (p+(1/fromInteger q)) (a+1)
                              --primek n q b (p+(1/fromInteger q)) (a+1)
                         else show n++" Is Not Prime"
                    else show n++" Is Prime"
                    where (r:bs)=b

isp n b c =    if    c==1
               then  mod b n
               else if mod c 2 ==0
                    then isp n (mod (b*b) n) (quot c 2)
               else mod (b*isp n (mod (b*b) n) (quot c 2)) n

randomgen n q =let  h1= fromIntegral (n*q)::Int
                    h2= fromIntegral q::Int
               in   take h2 (randomRs (2,n-1) (mkStdGen h1)) 

{-////////////////////////////////////////////////////////////////////////////////////////////////////
********************Problem 3 - High Order Function*****************************************
-}

{-**************************************************************************************************************
1) Newton Method
-}

newton f g e  =if a<=e
               then p
               else newton f p e
               where     p=g-((f g)/(diffe f g))
                         a=   if p-g>=0
                              then p-g
                              else g-p

diffe f g = (f (g+d) - f g)/d
               where d=0.0000001

--f x = (x^2)-10

{-Proof- 
specs -        run the algo atleat one time 
               newton f g e = newton f p e  if |p-g|<=e
                              p              otherwise
                              where p = g-((f g)/(diffe f g))
     
Invariant -    for each iteration of loop our p value approaches near to actual real value 
               for any k th step let our guess be p 
               then 
               newton f g e = newton f p e  
               and p will be in between actual value+g and actual value-g
 
     Base Case:at g==actual answer we want and accuracy is more than e
               in this case our algo will run once to calulate new guess value 
               but by newtons method it will give original value only 
               so g-new value =0
               this will obviously will be less than e 
               Thus Base Case Proved 
     IH :      Let for any k step our algo is correct
               i.e newton f g e = newton f p e and 
               and p will be in between actual value+g and actual value-g
     IS :      Now for any step n>k we have 
               new value = p-((f p)/(diffe f p))
               Obviously theis value will also be more closer to root and will be in between actual value+g and actual value-g
               also it might be the case that it will be in between actual value+p and actual value-p
               This is proved by Neton method
               Thus our newton will give corrrect answer
               thus our inductive hypothesis hold true and we have proved

Time analysis: T(n) = T(n+1)+1
               Thus we have T(n)=O(n)
          
-}


{-**************************************************************************************************************
2) Double Summation function
-}
summation f a b c d =    if b<a || d<c
                         then 0
                         else double f b c d + summation f a (b-1) c d

double f b c d =    if d>=c
                    then f b d + double f b c (d-1)
                    else 0

--f b d = b+d 

{-Proof- 
specs -        summation f a b c d=     double f b c d + summation f a (b-1) c d if b>=a
                                        0   if b<a
               double f b c d =         f b d + double f b c (d-1) if d>=c
                                        0 if d<c
 
     Base Case:if b==a or d==c  
               then our ans should be f a c
               Now from our algo we have 
               summation f a b c d=     double f b c d + summation f a (b-1) c d
               summation f a (b-1) c d =0
               double f b c d =f a c
               Thus Base Case Proved 
     IH :      Let for any b' <b and d' <d our algo is correct
               i.e summation f a b' c d'=     double f b' c d' + summation f a (b'-1) c d' is correct
     IS :      Now for any b>b' and d>d' we have 
               summation f a b c d=     double f b c d + summation f a (b-1) c d
               now clearly if b'=b-1 and d'=d-1 
               then summation f a b c d = summation f a b' c d' + summation f b b c d + summation f a b' d d 
               Now by our IH step summation f a b' c d' is true 
               and summation f b b c d is summation of f with b as constant and varyiny c to d 
               and summation f a b' d d is keeping d constant and varying a to b'
               Thus our summation f a b c d  match the mathematical specs in the question
               thus our inductive hypothesis hold true and we have proved our algo

Time analysis: T(n1,n2)  = T(n1-1)+T(n2)
               T (n2)    = O(n2)
               T(n1,n2)  = T(n1-1)+O(n2)
               where n1 = b-a+1 and n2=d-c+1
               Thus we have T(n1,n2)=O(n2)*O(n1)
               Thus T(n1,n2)=O(n2*n1)
          
-}

{-
******************************************************END**************************************
-}
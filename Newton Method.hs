import System.Random (randomRs,mkStdGen)

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

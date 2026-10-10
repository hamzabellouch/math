import Mathlib
import OAI.Combinatorics.UniformKServer.RawTable

namespace OAI

                              
section

namespace UniformKServer.RawPath
open RawArithmetic RawTable RawWords

theorem history_nil (g : List ℕ) : history [] g=[] := rfl

theorem history_cons (r j : ℕ) (w g : List ℕ) :
    history (r::w) (j::g)=(r,j)::history w g := by
  simp [history,List.range_succ_eq_map,List.map_map,Function.comp_def]

def weight (T : List ℕ) : List ℕ → List ℕ → List (ℕ×ℕ) → ℕ
  | _,_,[]=>1
  | p,c,(r,j)::h=>entry T p c r j*weight T (p++[r]) (c.set j r) h

def movement (n : ℕ) (d : List Q) : List ℕ → List (ℕ×ℕ) → ℚ
  | _,[]=>0
  | c,(r,j)::h=>value (dist n d (c.getD j 0) r)+movement n d (c.set j r) h

theorem fold_weight (n : ℕ) (d : List Q) (T p c : List ℕ) (m : ℕ) (q : Q) (h : List (ℕ×ℕ)) :
    (h.foldl (pathStep n d T) ((p,c),(m,q))).2.1=m*weight T p c h := by
  induction h generalizing p c m q with
  | nil=>simp [weight]
  | cons rj h ih=>
    obtain ⟨r,j⟩:=rj
    simp only [List.foldl_cons,pathStep,ih,weight]
    exact Nat.mul_assoc _ _ _

theorem fold_movement (n : ℕ) (d : List Q) (T p c : List ℕ) (m : ℕ) (q : Q) (h : List (ℕ×ℕ)) :
    value (h.foldl (pathStep n d T) ((p,c),(m,q))).2.2=value q+movement n d c h := by
  induction h generalizing p c m q with
  | nil=>simp [movement]
  | cons rj h ih=>
    obtain ⟨r,j⟩:=rj
    simp only [List.foldl_cons,pathStep,ih,movement,value_add]
    exact add_assoc _ _ _

theorem term_value (n : ℕ) (d : List Q) (T p c w g : List ℕ) :
    value (term n d T p c w g) =
      (weight T p c (history w g):ℚ)*movement n d c (history w g) := by
  simp [term,path,value_mul,value_natural,fold_weight,fold_movement]

theorem cost_value (n : ℕ) (d : List Q) (c w g : List ℕ) :
    value (cost n d c w g)=movement n d c (history w g) := by
  simp [cost,path,fold_movement]

theorem value_sum (xs : List Q) : value (xs.foldr add (natural 0))=(xs.map value).sum := by
  induction xs <;> simp [*]

theorem total_value (n k : ℕ) (d : List Q) (T p c w : List ℕ) :
    value (total n k d T p c w) =
      ((words k w.length).map fun g=>
        (weight T p c (history w g):ℚ)*movement n d c (history w g)).sum := by
  simp only [total,value_sum,List.map_map,Function.comp_def,term_value]

theorem expected_value (n k b : ℕ) (d : List Q) (T p c w : List ℕ) :
    value (expected n k b d T p c w)=value (total n k d T p c w)/(2:ℚ)^(b*w.length) := by
  have h : 2^(b*w.length)-1+1=2^(b*w.length) := by have:=Nat.two_pow_pos (b*w.length);omega
  simp only [expected,value_divide,←Nat.cast_one (R:=ℚ),←Nat.cast_add,h,Nat.cast_pow,Nat.cast_ofNat]

end UniformKServer.RawPath

end

                                       
section

   
                                                                              
                                                                              
                                                                               
                                                                             
                                                      
  
namespace UniformKServer

end UniformKServer


end

end OAI

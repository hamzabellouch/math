import Mathlib
import OAI.Combinatorics.UniformKServer.BitPaths
import OAI.Combinatorics.UniformKServer.Epochs

namespace OAI

                                    
section

namespace UniformKServer.PathExpansion
variable {S R : Type*} {k b : ℕ}

def traces (k : ℕ) : List R → List (List (R×Fin k))
  | []=>[[]]
  | r::w=>(List.ofFn fun j : Fin k => (traces k w).map ((r,j)::·)).flatten

def weight (N : S→R→Fin k→ℕ) (next : S→R→Fin k→S) : S→List (R×Fin k)→ℕ
  | _,[]=>1
  | s,(r,j)::h=>N s r j*weight N next (next s r j) h

def movement (next : S→R→Fin k→S) (charge : S→R→Fin k→ℝ) : S→List (R×Fin k)→ℝ
  | _,[]=>0
  | s,(r,j)::h=>charge s r j+movement next charge (next s r j) h

theorem sum_cons {A : Type*} [AddCommMonoid A] (r : R) (w : List R)
    (f : List (R×Fin k)→A) :
    ((traces k (r::w)).map f).sum=
      ∑ j : Fin k,((traces k w).map fun h=>f ((r,j)::h)).sum := by
  simp [traces,List.map_flatten,List.map_ofFn,List.map_map,List.sum_flatten,List.sum_ofFn,Function.comp_def]

theorem sum_weight (N : S→R→Fin k→ℕ) (hN : ∀s r,∑j,N s r j=2^b)
    (next : S→R→Fin k→S) (s : S) (w : List R) :
    ((traces k w).map fun h=>weight N next s h).sum=(2^b)^w.length := by
  induction w generalizing s with
  | nil=>simp [traces,weight]
  | cons r w ih=>
    rw [sum_cons]
    simp only [weight,List.sum_map_mul_left,ih]
    rw [←Finset.sum_mul,hN]
    simp [pow_succ,mul_comm]

theorem sum_weight_cost (N : S→R→Fin k→ℕ) (hN : ∀s r,∑j,N s r j=2^b)
    (next : S→R→Fin k→S) (charge : S→R→Fin k→ℝ) (s : S) (w : List R) :
    ((traces k w).map fun h=>(weight N next s h:ℝ)*movement next charge s h).sum=
      ((2:ℝ)^b)^w.length*BitSampling.rowCost (b:=b) N next charge s w := by
  induction w generalizing s with
  | nil=>simp [traces,weight,movement,BitSampling.rowCost]
  | cons r w ih=>
    rw [sum_cons]
    have hcast (s : S) : ((traces k w).map fun h=>(weight N next s h:ℝ)).sum=((2:ℝ)^b)^w.length := by
      have h := congrArg (fun a : ℕ => (a:ℝ)) (sum_weight N hN next s w)
      simpa only [Nat.cast_list_sum,List.map_map,Function.comp_def,Nat.cast_pow,Nat.cast_ofNat] using h
    have hs (j : Fin k) :
        ((traces k w).map fun h=>(weight N next s ((r,j)::h):ℝ)*movement next charge s ((r,j)::h)).sum=
        (N s r j:ℝ)*(((2:ℝ)^b)^w.length*charge s r j+
          ((2:ℝ)^b)^w.length*BitSampling.rowCost (b:=b) N next charge (next s r j) w) := by
      simp only [weight,movement,Nat.cast_mul]
      have he (h : List (R×Fin k)) :
          (N s r j:ℝ)*(weight N next (next s r j) h:ℝ)*
            (charge s r j+movement next charge (next s r j) h)=
          ((N s r j:ℝ)*charge s r j)*(weight N next (next s r j) h:ℝ)+
            (N s r j:ℝ)*((weight N next (next s r j) h:ℝ)*movement next charge (next s r j) h) := by ring
      simp_rw [he]
      rw [List.sum_map_add,List.sum_map_mul_left,List.sum_map_mul_left,hcast,ih]
      ring
    simp_rw [hs]
    simp only [List.length_cons,pow_succ,BitSampling.rowCost,Nat.cast_pow,Nat.cast_ofNat]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hb : (2:ℝ)^b≠0 := by positivity
    field_simp

end UniformKServer.PathExpansion

end


end OAI

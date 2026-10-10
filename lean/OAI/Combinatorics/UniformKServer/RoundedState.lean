import Mathlib
import OAI.Combinatorics.UniformKServer.IntegerParks
import OAI.Combinatorics.UniformKServer.FiniteProbability

namespace OAI

                                   
section

/-! A fixed finite state space for the causal rounding kernels. It records
only bounded integer subtree counts, not an assumed distribution. -/
noncomputable section
namespace UniformKServer.TreeRounding
open Finset TreeAncestry
open scoped Classical
variable {n k : ℕ} {S : Shape n}

theorem rounded_le {a : Allocation S k} {x : Vertex n→ℤ} (hx : Rounded a x) (u : Vertex n) :
    x u≤k := by
  have hs : (∑ v∈subtree S u,(intPark S x v:ℝ))≤∑ v : Vertex n,(intPark S x v:ℝ) := by
    exact sum_le_univ_sum_of_nonneg (fun v=>by exact_mod_cast rounded_park_nonneg hx v)
  rw [intPark_subtree hx] at hs
  have ht : (∑ v : Vertex n,(intPark S x v:ℝ))=k := by exact_mod_cast intPark_total hx
  rw [ht] at hs
  exact_mod_cast hs

def bounded (x : Vertex n→Fin (k+1)) : Vertex n→ℤ := fun v=>(x v).val

abbrev State (S : Shape n) (k : ℕ) := {p : (Vertex n→Fin (k+1)) × (Fin k→Vertex n) //
  (∀ f : Vertex n→ℝ,(∑ i,f (p.2 i))=∑ v,(intPark S (bounded p.1) v:ℝ)*f v) ∧
    ∀ i,0 < intPark S (bounded p.1) (p.2 i)}

def State.value (s : State S k) : Vertex n→ℤ := bounded s.val.1

def State.realization (s : State S k) : Realization (k:=k) (S:=S) s.value :=
  ⟨s.val.2,s.property.1,s.property.2⟩

def stateOf (a : Allocation S k) (x : Vertex n→ℤ) (hx : Rounded a x)
    (R : Realization (k:=k) (S:=S) x) : State S k := by
  let c : Vertex n→Fin (k+1) := fun v=>⟨(x v).toNat,by have h₁ := rounded_nonneg hx v; have h₂ := rounded_le hx v; omega⟩
  have he : bounded c=x := by funext v; exact Int.toNat_of_nonneg (rounded_nonneg hx v)
  exact ⟨(c,R.tuple),by rw [he]; exact ⟨R.sum,R.positive⟩⟩

theorem stateOf_value (a : Allocation S k) (x : Vertex n→ℤ) (hx : Rounded a x)
    (R : Realization (k:=k) (S:=S) x) :
    (stateOf a x hx R).value=x := by
  funext v
  exact Int.toNat_of_nonneg (rounded_nonneg hx v)

theorem stateOf_tuple (a : Allocation S k) (x : Vertex n→ℤ) (hx : Rounded a x)
    (R : Realization (k:=k) (S:=S) x) :
    (stateOf a x hx R).realization.tuple=R.tuple := rfl

structure Distribution (a : Allocation S k) where
  law : FiniteProbability.Law (State S k)
  rounded : ∀ s,0<law.weight s → Rounded a s.value
  mean : ∀ v,law.expect (fun s=>(s.value v:ℝ))=a.amount v

end UniformKServer.TreeRounding

end


end

end OAI

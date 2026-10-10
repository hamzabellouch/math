import Mathlib
import OAI.Combinatorics.UniformKServer.TreeTransport

namespace OAI

                                   
section

/-! A rounded, consistent hierarchy contains exactly k integer parks. Their
literal labeled enumeration has the prescribed subtree counts. -/
noncomputable section
namespace UniformKServer.TreeRounding
open Finset TreeAncestry BalancedStar
open scoped Classical
variable {n k : ℕ} {S : Shape n}

theorem rounded_nonneg {a : Allocation S k} {x : Vertex n→ℤ}
    (hx : Rounded a x) (v : Vertex n) : 0≤x v :=
  (Int.floor_nonneg.mpr (a.nonneg v)).trans (balanced_bounds (hx.2.1 v)).1

theorem rounded_park_nonneg {a : Allocation S k} {x : Vertex n→ℤ}
    (hx : Rounded a x) (v : Vertex n) : 0 ≤ intPark S x v :=
  (Int.floor_nonneg.mpr (a.park_nonneg v)).trans (balanced_bounds (hx.2.2 v)).1

def integerAllocation (a : Allocation S k) (x : Vertex n→ℤ) (hx : Rounded a x) : Allocation S k where
  amount v := x v
  nonneg v := by exact_mod_cast rounded_nonneg hx v
  park_nonneg v := by rw [park,←cast_intPark]; exact_mod_cast rounded_park_nonneg hx v
  root := by rw [hx.1]; simp

theorem intPark_total {a : Allocation S k} {x : Vertex n→ℤ} (hx : Rounded a x) :
    (∑ v : Vertex n,intPark S x v)=k := by
  have ht := TreeParking.total (integerAllocation a x hx)
  simp only [integerAllocation,park,←cast_intPark] at ht
  exact_mod_cast ht

theorem intPark_subtree {a : Allocation S k} {x : Vertex n→ℤ} (hx : Rounded a x)
    (u : Vertex n) : (∑ v∈subtree S u,(intPark S x v:ℝ))=x u := by
  simpa only [integerAllocation,park,←cast_intPark] using subtree_total (integerAllocation a x hx) u

theorem intPark_nat_total {a : Allocation S k} {x : Vertex n→ℤ} (hx : Rounded a x) :
    (∑ v : Vertex n,(intPark S x v).toNat)=k := by
  have h : (∑ v : Vertex n,((intPark S x v).toNat:ℤ))=(k:ℤ) := by
    simp only [Int.toNat_of_nonneg (rounded_park_nonneg hx _)]
    exact intPark_total hx
  exact_mod_cast h

structure Realization (x : Vertex n→ℤ) where
  tuple : Fin k→Vertex n
  sum : ∀ f : Vertex n→ℝ,(∑ i,f (tuple i))=∑ v,(intPark S x v:ℝ)*f v
  positive : ∀ i,0 < intPark S x (tuple i)

theorem realization_exists {a : Allocation S k} {x : Vertex n→ℤ} (hx : Rounded a x) :
    Nonempty (Realization (k:=k) (S:=S) x) := by
  let T := (v : Vertex n) × Fin (intPark S x v).toNat
  have hcard : Fintype.card T=k := by
    rw [Fintype.card_sigma]
    simpa only [Fintype.card_fin] using intPark_nat_total hx
  let e : T≃Fin k := Fintype.equivFinOfCardEq hcard
  refine ⟨⟨fun i=>(e.symm i).1,?_,?_⟩⟩
  · intro f
    calc
      (∑ i,f (e.symm i).1)=∑ t : T,f t.1 := Equiv.sum_comp e.symm (fun t=>f t.1)
      _=∑ v,(intPark S x v:ℝ)*f v := by
        rw [Fintype.sum_sigma]
        simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
        apply sum_congr rfl
        intro v _
        congr 1
        exact_mod_cast Int.toNat_of_nonneg (rounded_park_nonneg hx v)
  · intro i
    have hp : 0<(intPark S x (e.symm i).1).toNat := Nat.zero_lt_of_lt (e.symm i).2.isLt
    have hz := Int.toNat_of_nonneg (rounded_park_nonneg hx (e.symm i).1)
    omega

def realize (a : Allocation S k) (x : Vertex n→ℤ) (hx : Rounded a x) : Realization (k:=k) (S:=S) x :=
  Classical.choice (realization_exists hx)

theorem Realization.subtree {a : Allocation S k} {x : Vertex n→ℤ} (hx : Rounded a x)
    (R : Realization (k:=k) (S:=S) x) (u : Vertex n) :
    LaminarTransport.mass (TreeAncestry.subtree S u) R.tuple=x u := by
  rw [LaminarTransport.mass,R.sum]
  simp only [LaminarTransport.bit,mul_ite,mul_one,mul_zero,←sum_filter]
  simpa only [filter_mem_eq_inter,univ_inter] using intPark_subtree hx u

theorem Realization.valid {a : Allocation S k} {x : Vertex n→ℤ} (hx : Rounded a x)
    (R : Realization (k:=k) (S:=S) x) (i : Fin k) : 0<park S a.amount (R.tuple i) := by
  have hp := R.positive i
  have hb := (balanced_bounds (hx.2.2 (R.tuple i))).2
  by_contra he
  have hz := le_antisymm (not_lt.mp he) (a.park_nonneg _)
  rw [hz,Int.ceil_zero] at hb
  omega

end UniformKServer.TreeRounding

end


end

end OAI

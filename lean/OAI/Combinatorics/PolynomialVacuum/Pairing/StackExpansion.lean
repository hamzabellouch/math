import OAI.Combinatorics.PolynomialVacuum.Pairing.TransferPowers
import OAI.Combinatorics.PolynomialVacuum.Cylinder.StackProperties

namespace OAI

namespace PolynomialVacuumAlgebra
open Classical PolynomialVacuumCylinder

private theorem prod_sum_sum {J A B : Type*} [Fintype J] [Fintype A] [Fintype B]
    (f : J → A → B → ℂ) :
    (∏j,∑a,∑b,f j a b)=∑a : J → A,∑b : J → B,∏j,f j (a j) (b j) := by
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact Fintype.prod_sum _

noncomputable def stackVertical (N H : ℕ) (inp : Fin (N+1) → Spin)
    (r : Fin H → (Fin (N+1) → Spin)) : Fin (H+1) → ZMod (N+1) → Spin :=
  fun j => cylinderState N ((Fin.cons inp r : Fin (H+1) → (Fin (N+1) → Spin)) j)
noncomputable def stackInternal (N H : ℕ) (a : Fin H → (Fin (N+1) → Spin)) :
    Fin H → ZMod (N+1) → Spin := fun j => cylinderState N (a j)

noncomputable def physicalStackWeight (N H : ℕ) (κ : ℂ) (inp : Fin (N+1) → Spin)
    (r a k : Fin H → (Fin (N+1) → Spin)) : ℂ :=
  (∏j : Fin H,κ^charge (cylinderState N (a j) 1)) *
    stackLocalWeight (stackVertical N H inp r) (stackInternal N H a) (stackInternal N H k)

private theorem stack_weight_product (N H : ℕ) (κ : ℂ) (inp : Fin (N+1) → Spin)
    (r a k : Fin H → (Fin (N+1) → Spin)) :
    (∏j : Fin H,κ^charge (a j (Fin.last N))*∏i : Fin (N+1),
      honeycombPiece (r j i,a j i)
        (a j (i-1),(Fin.cons inp r : Fin (H+1) → (Fin (N+1) → Spin)) j.castSucc i) (k j i))=
    physicalStackWeight N H κ inp r a k := by
  unfold physicalStackWeight stackLocalWeight
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  have haux : cylinderState N (a j) 1=a j (Fin.last N) := by
    rw [← rowCoordinate_last N,cylinderState_coordinate]
  rw [haux]
  congr 1
  rw [← stack_row_weight]
  rw [← (rowCoordinate N).prod_comp]
  simp only [stackVertical,stackInternal,Fin.cons_succ,cylinderState_coordinate,cylinderState_next]

 

theorem physicalTransfer_pow_currents (N H : ℕ) (κ : ℂ) (out inp : Fin (N+1) → Spin) :
    (physicalTransfer (N+1) κ^H) out inp=
      ∑r : Fin H → (Fin (N+1) → Spin),
      if matrixPathEnd inp r=out then
        ∑a : Fin H → (Fin (N+1) → Spin),∑k : Fin H → (Fin (N+1) → Spin),
          physicalStackWeight N H κ inp r a k
      else 0 := by
  rw [physicalTransfer_pow_local]
  apply Finset.sum_congr rfl
  intro r _
  split_ifs
  · rw [prod_sum_sum]
    simp_rw [stack_weight_product]
    apply Finset.sum_congr (by ext; simp)
    intro a _
    apply Finset.sum_congr (by ext; simp)
    intro k _
    rfl
  · rfl

end PolynomialVacuumAlgebra

end OAI

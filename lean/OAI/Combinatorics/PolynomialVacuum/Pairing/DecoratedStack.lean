import OAI.Combinatorics.PolynomialVacuum.Pairing.LayerProduct
import OAI.Combinatorics.PolynomialVacuum.Pairing.StackReindex

namespace OAI

namespace PolynomialVacuumAlgebra
open Classical PolynomialVacuumCylinder

noncomputable def decoratedTransfer (N : ℕ) (κ : ℂ) (d : (ZMod (N+1) → Spin) → ℂ) :
    Matrix (Fin (N+1) → Spin) (Fin (N+1) → Spin) ℂ :=
  fun out inp=>physicalTransfer (N+1) κ out inp*d (cylinderState N inp)

noncomputable def decoratedStackWeight {M H : ℕ} [NeZero M]
    (κ : Fin H → ℂ) (d : Fin H → (ZMod M → Spin) → ℂ) (c : StackCoordinates M H) : ℂ :=
  (∏j : Fin H,κ j^charge (c.2.1 j 1)*d j (c.1 j.castSucc))*stackLocalWeight c.1 c.2.1 c.2.2

private theorem decorated_path_weight (N H : ℕ) (κ : Fin H → ℂ)
    (d : Fin H → (ZMod (N+1) → Spin) → ℂ) (inp : Fin (N+1) → Spin)
    (r : Fin H → (Fin (N+1) → Spin)) :
    layerPathWeight (fun j=>decoratedTransfer N (κ j) (d j)) inp r=
      ∑a : Fin H → (Fin (N+1) → Spin),∑k : Fin H → (Fin (N+1) → Spin),
        decoratedStackWeight κ d (stackVertical N H inp r,stackInternal N H a,stackInternal N H k) := by
  simp only [layerPathWeight,decoratedTransfer,physicalTransfer_periodic,Finset.sum_mul]
  simp_rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro k _
  unfold decoratedStackWeight stackLocalWeight
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  have haux : cylinderState N (a j) 1=a j (Fin.last N) := by
    rw [← rowCoordinate_last N,cylinderState_coordinate]
  change (κ j^charge (a j (Fin.last N))*_)*_=(κ j^charge (cylinderState N (a j) 1)*_)*_
  rw [haux]
  have he : (∏i : Fin (N+1),honeycombPiece (r j i,a j i)
      (a j (i-1),(Fin.cons inp r : Fin (H+1) → _ ) j.castSucc i) (k j i))=
      ∏i : ZMod (N+1),localCurrentWeight
        (stackCurrent (stackVertical N H inp r) (stackInternal N H a) (stackInternal N H k)) (.up i j.val)*
      localCurrentWeight (stackCurrent (stackVertical N H inp r) (stackInternal N H a) (stackInternal N H k)) (.down i j.val) := by
    rw [← stack_row_weight,← (rowCoordinate N).prod_comp]
    simp only [stackVertical,stackInternal,Fin.cons_succ,cylinderState_coordinate,cylinderState_next]
  rw [he]
  dsimp only [stackVertical]
  ring

private theorem decorated_full_sum (N H : ℕ) (κ : Fin H → ℂ)
    (d : Fin H → (ZMod (N+1) → Spin) → ℂ) (out inp : Fin (N+1) → Spin) :
    layerProduct (fun j=>decoratedTransfer N (κ j) (d j)) out inp=
      ∑v : Fin (H+1) → (Fin (N+1) → Spin),
      if v 0=inp ∧ v (Fin.last H)=out then
        ∑a : Fin H → (Fin (N+1) → Spin),∑k : Fin H → (Fin (N+1) → Spin),
          decoratedStackWeight κ d (fun j=>cylinderState N (v j),stackInternal N H a,stackInternal N H k)
      else 0 := by
  rw [← (Fin.consEquiv (fun _ : Fin (H+1) => (Fin (N+1) → Spin))).sum_comp,Fintype.sum_prod_type]
  change _ = ∑p : Fin (N+1) → Spin,∑r : Fin H → (Fin (N+1) → Spin),
    if p=inp ∧ matrixPathEnd p r=out then
      ∑a : Fin H → (Fin (N+1) → Spin),∑k : Fin H → (Fin (N+1) → Spin),
        decoratedStackWeight κ d (stackVertical N H p r,stackInternal N H a,stackInternal N H k) else 0
  rw [Finset.sum_eq_single inp]
  · rw [layerProduct_path_sum]
    simp only [true_and,decorated_path_weight]
  · intro p _ hp
    simp only [hp,false_and,ite_false,Finset.sum_const_zero]
  · simp

 
theorem decorated_coordinates (N H : ℕ) (κ : Fin H → ℂ)
    (d : Fin H → (ZMod (N+1) → Spin) → ℂ) (out inp : Fin (N+1) → Spin) :
    layerProduct (fun j=>decoratedTransfer N (κ j) (d j)) out inp=
      ∑c : StackCoordinates (N+1) H,
        if matchesBoundary c.1 (cylinderState N inp) (cylinderState N out) then
          decoratedStackWeight κ d c else 0 := by
  rw [← (fullStackEquiv N H).sum_comp,Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  rw [decorated_full_sum]
  apply Finset.sum_congr rfl
  intro v _
  have hm : matchesBoundary ((fullStackEquiv N H) (v,(fun _ _=>Spin.zero),(fun _ _=>Spin.zero))).1
      (cylinderState N inp) (cylinderState N out) ↔ v 0=inp ∧ v (Fin.last H)=out := by
    change (cylinderStateEquiv N (v 0)=cylinderStateEquiv N inp ∧
      cylinderStateEquiv N (v (Fin.last H))=cylinderStateEquiv N out) ↔ _
    simp only [Equiv.apply_eq_iff_eq]
  by_cases h : v 0=inp ∧ v (Fin.last H)=out
  · rw [ite_eq_left h]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro k _
    have hh : matchesBoundary ((fullStackEquiv N H) (v,a,k)).1
        (cylinderState N inp) (cylinderState N out) := hm.mpr h
    rw [ite_eq_left hh]
    rfl
  · rw [ite_eq_right h]
    symm
    apply Finset.sum_eq_zero
    intro a _
    apply Finset.sum_eq_zero
    intro k _
    exact ite_eq_right (fun hh=>h (hm.mp hh))

end PolynomialVacuumAlgebra

end OAI

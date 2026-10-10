import OAI.Combinatorics.PolynomialVacuum.Cylinder.StackWeight
import OAI.Combinatorics.PolynomialVacuum.Cylinder.StackEquiv

namespace OAI

namespace PolynomialVacuumAlgebra
open Classical PolynomialVacuumCylinder

noncomputable def cylinderStateEquiv (N : ℕ) : (Fin (N+1) → Spin) ≃ (ZMod (N+1) → Spin) :=
  Equiv.arrowCongr (rowCoordinate N) (Equiv.refl Spin)
noncomputable def cylinderLayersEquiv (N H : ℕ) :
    (Fin H → (Fin (N+1) → Spin)) ≃ (Fin H → (ZMod (N+1) → Spin)) :=
  Equiv.piCongrRight (fun _ => cylinderStateEquiv N)
noncomputable def fullStackEquiv (N H : ℕ) :
    ((Fin (H+1) → (Fin (N+1) → Spin)) ×
      (Fin H → (Fin (N+1) → Spin)) × (Fin H → (Fin (N+1) → Spin))) ≃ StackCoordinates (N+1) H :=
  Equiv.prodCongr (cylinderLayersEquiv N (H+1))
    (Equiv.prodCongr (cylinderLayersEquiv N H) (cylinderLayersEquiv N H))

noncomputable def matchesBoundary {M H : ℕ} (v : Fin (H+1) → ZMod M → Spin)
    (inp out : ZMod M → Spin) : Prop := v 0=inp ∧ v (Fin.last H)=out

private theorem full_stack_sum (N H : ℕ) (out inp : Fin (N+1) → Spin) :
    (physicalTransfer (N+1) zeta^H) out inp=
      ∑v : Fin (H+1) → (Fin (N+1) → Spin),
      if v 0=inp ∧ v (Fin.last H)=out then
        ∑a : Fin H → (Fin (N+1) → Spin),∑k : Fin H → (Fin (N+1) → Spin),
          domainWeight (bandSites (N+1) H)
            (stackCurrent (fun j=>cylinderState N (v j)) (stackInternal N H a) (stackInternal N H k))
      else 0 := by
  rw [← (Fin.consEquiv (fun _ : Fin (H+1) => (Fin (N+1) → Spin))).sum_comp,Fintype.sum_prod_type]
  change _ = ∑p : Fin (N+1) → Spin,∑r : Fin H → (Fin (N+1) → Spin),
    if p=inp ∧ matrixPathEnd p r=out then
      ∑a : Fin H → (Fin (N+1) → Spin),∑k : Fin H → (Fin (N+1) → Spin),
        domainWeight (bandSites (N+1) H)
          (stackCurrent (stackVertical N H p r) (stackInternal N H a) (stackInternal N H k)) else 0
  rw [Finset.sum_eq_single inp]
  · rw [physicalTransfer_pow_currents]
    simp only [true_and,physicalStackWeight_domain]
  · intro p _ hp
    simp only [hp,false_and,ite_false,Finset.sum_const_zero]
  · simp

 

theorem physicalTransfer_pow_coordinates (N H : ℕ) (out inp : Fin (N+1) → Spin) :
    (physicalTransfer (N+1) zeta^H) out inp=
      ∑c : StackCoordinates (N+1) H,
        if matchesBoundary c.1 (cylinderState N inp) (cylinderState N out) then
          domainWeight (bandSites (N+1) H) (coordinatesCurrent c) else 0 := by
  rw [← (fullStackEquiv N H).sum_comp,Fintype.sum_prod_type]
  simp only [Fintype.sum_prod_type]
  rw [full_stack_sum]
  apply Finset.sum_congr rfl
  intro v _
  have hm : matchesBoundary ((fullStackEquiv N H) (v,(fun _ _ => Spin.zero),(fun _ _ => Spin.zero))).1
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
    have hh : ¬matchesBoundary ((fullStackEquiv N H) (v,a,k)).1
        (cylinderState N inp) (cylinderState N out) := fun hh=>h (hm.mp hh)
    exact ite_eq_right hh

end PolynomialVacuumAlgebra

end OAI

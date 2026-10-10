import OAI.Probability.SignedSweeps.FiniteSampling

namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {A B C : Type*} (e : C × B ≃ A)

def fiberPiece (g : fiberSubgroup (fun x : A => (e.symm x).1)) (c : C) : Equiv.Perm B where
  toFun b := (e.symm (g.1 (e (c,b)))).2
  invFun b := (e.symm (g.1⁻¹ (e (c,b)))).2
  left_inv b := by
    have hk : (e.symm (g.1 (e (c,b)))).1 = c := by
      simpa using g.property (e (c,b))
    change (e.symm (g.1⁻¹ (e (c, (e.symm (g.1 (e (c,b)))).2)))).2 = b
    have ht : (c, (e.symm (g.1 (e (c,b)))).2) = e.symm (g.1 (e (c,b))) :=
      Prod.ext hk.symm rfl
    rw [ht, Equiv.apply_symm_apply]
    simp
  right_inv b := by
    have hk : (e.symm (g.1⁻¹ (e (c,b)))).1 = c := by
      simpa using ((fiberSubgroup _).inv_mem g.property) (e (c,b))
    change (e.symm (g.1 (e (c, (e.symm (g.1⁻¹ (e (c,b)))).2)))).2 = b
    have ht : (c, (e.symm (g.1⁻¹ (e (c,b)))).2) = e.symm (g.1⁻¹ (e (c,b))) :=
      Prod.ext hk.symm rfl
    rw [ht, Equiv.apply_symm_apply]
    simp

def fiberSettingsEquiv : (C → Equiv.Perm B) ≃ fiberSubgroup (fun x : A => (e.symm x).1) where
  toFun p := ⟨e.permCongr (Equiv.prodCongrRight p), by
    intro x
    simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply]
    rfl⟩
  invFun g := fiberPiece e g
  left_inv p := by
    funext c
    apply Equiv.ext
    intro b
    change (e.symm ((e.permCongr (Equiv.prodCongrRight p)) (e (c,b)))).2 = _
    simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply, Equiv.prodCongrRight_apply]
  right_inv g := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    apply e.symm.injective
    simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply]
    change ((e.symm x).1, (e.symm (g.1 (e ((e.symm x).1, (e.symm x).2)))).2) = _
    rw [Prod.mk.eta, Equiv.apply_symm_apply]
    have hg : (e.symm (g.1 x)).1 = (e.symm x).1 := g.property x
    rw [← hg, Prod.mk.eta]

@[simp] lemma fiberSettingsEquiv_apply (p : C → Equiv.Perm B) (c : C) (b : B) :
    (fiberSettingsEquiv e p).1 (e (c,b)) = e (c, p c b) := by
  change (e.permCongr (Equiv.prodCongrRight p)) (e (c,b)) = _
  simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply, Equiv.prodCongrRight_apply]

end SignedSweeps
end

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
attribute [local instance] Classical.propDecidable

abbrev SwitchAddress (d : ℕ) (i : Fin d) := {j : Fin d // j ≠ i} → Fin 2

def switchCoordinates (d : ℕ) (i : Fin d) : SwitchAddress d i × Fin 2 ≃ Fin (2 ^ d) :=
  ((Equiv.prodComm _ _).trans (Equiv.funSplitAt i (Fin 2)).symm).trans (positionsEquiv d)

@[simp] lemma switchCoordinates_symm (d : ℕ) (i : Fin d) (x : Fin (2 ^ d)) :
    (switchCoordinates d i).symm x =
      ((fun j => (positionsEquiv d).symm x j.1), (positionsEquiv d).symm x i) := rfl

abbrev LayerSettings (d : ℕ) (i : Fin d) := SwitchAddress d i → Equiv.Perm (Fin 2)

def layerSettingsEquiv (d : ℕ) (i : Fin d) : LayerSettings d i ≃ coordinateSubgroup d i :=
  fiberSettingsEquiv (switchCoordinates d i)

abbrev PhysicalSettings (d : ℕ) := ∀ i : Fin d, LayerSettings d i

def physicalSettingsEquiv (d : ℕ) : PhysicalSettings d ≃ SweepSettings d :=
  Equiv.piCongrRight (layerSettingsEquiv d)

lemma sweepOperator_eq_physicalMean {d : ℕ} (lam : Partition (2 ^ d)) :
    sweepOperator lam = finiteMean ℂ (fun p : PhysicalSettings d =>
      spechtRepresentation lam (sampleSweep d (physicalSettingsEquiv d p))) := by
  rw [sweepOperator_eq_sampleMean]
  exact (finiteMean_equiv ℂ (physicalSettingsEquiv d)
    (fun a => spechtRepresentation lam (sampleSweep d a))).symm

lemma layerSettings_key (d : ℕ) (i : Fin d) (p : LayerSettings d i) (x : Fin (2 ^ d))
    (j : Fin d) (hji : j ≠ i) :
    (positionsEquiv d).symm ((layerSettingsEquiv d i p).1 x) j =
      (positionsEquiv d).symm x j :=
  congrFun ((layerSettingsEquiv d i p).property x) ⟨j, hji⟩

lemma layerSettings_bit (d : ℕ) (i : Fin d) (p : LayerSettings d i) (x : Fin (2 ^ d)) :
    (positionsEquiv d).symm ((layerSettingsEquiv d i p).1 x) i =
      p (fun j : {j : Fin d // j ≠ i} => (positionsEquiv d).symm x j.1)
        ((positionsEquiv d).symm x i) := by
  have h := fiberSettingsEquiv_apply (switchCoordinates d i) p
    ((switchCoordinates d i).symm x).1 ((switchCoordinates d i).symm x).2
  simp only [Prod.mk.eta, Equiv.apply_symm_apply] at h
  have h' := congrArg (fun y => ((switchCoordinates d i).symm y).2) h
  rw [Equiv.symm_apply_apply] at h'
  change (positionsEquiv d).symm ((layerSettingsEquiv d i p).1 x) i =
    p (fun j : {j : Fin d // j ≠ i} => (positionsEquiv d).symm x j.1)
      ((positionsEquiv d).symm x i) at h'
  exact h'

end SignedSweeps
end

end OAI

import OAI.Analysis.CircleDomains.Sobolev.RealCoordinateLines
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

/-! The actual complex axial parametrizations preserve plane area.
Fubini provides the common integrable line densities. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 def axialPlaneHomeomorph (i : Fin 2) : (ℝ × ℝ) ≃ₜ ℂ :=
    if i = 0 then (Homeomorph.prodComm ℝ ℝ).trans Complex.equivRealProdCLM.symm.toHomeomorph
    else Complex.equivRealProdCLM.symm.toHomeomorph

 theorem axialPlaneHomeomorph_apply (i : Fin 2) (p : ℝ × ℝ) :
    axialPlaneHomeomorph i p = complexCoordinateLine i p.1 p.2 := by
  unfold axialPlaneHomeomorph complexCoordinateLine realCoordinateLine
  split <;> rfl

 theorem complexCoordinatePlane_measurePreserving (i : Fin 2) :
    MeasurePreserving (axialPlaneHomeomorph i) (volume.prod volume) volume := by
  have h := (Complex.volume_preserving_equiv_real_prod.symm Complex.measurableEquivRealProd).comp
    (realCoordinatePlane_measurePreserving i)
  convert h using 1
  funext p
  exact axialPlaneHomeomorph_apply i p

 theorem integral_axial_slices {ρ : ℂ → ℝ} (hρ : Integrable ρ) (i : Fin 2) :
    (∀ᵐ y ∂volume, Integrable (fun x => ρ (complexCoordinateLine i y x)) volume) ∧
    Integrable (fun y => ∫ x, ρ (complexCoordinateLine i y x)) volume ∧
    (∫ y, ∫ x, ρ (complexCoordinateLine i y x)) = ∫ z, ρ z := by
  have hp : Integrable (fun p : ℝ × ℝ => ρ (axialPlaneHomeomorph i p)) (volume.prod volume) :=
    (complexCoordinatePlane_measurePreserving i).integrable_comp_of_integrable hρ
  simp_rw [axialPlaneHomeomorph_apply] at hp
  refine ⟨hp.prod_right_ae,hp.integral_prod_left,?_⟩
  calc
    _ = ∫ p : ℝ × ℝ, ρ (axialPlaneHomeomorph i p) ∂volume.prod volume := by
      simpa only [axialPlaneHomeomorph_apply] using (integral_prod _ hp).symm
    _ = _ := (complexCoordinatePlane_measurePreserving i).integral_comp
      (axialPlaneHomeomorph i).toMeasurableEquiv.measurableEmbedding ρ

end CircleDomainRigidity

end

end OAI

import OAI.Geometry.Immersion.ClosedSurface.ImmersionJets
import OAI.Geometry.Immersion.ClosedSurface.PhaseCoordinates
import OAI.Geometry.Immersion.ClosedSurface.FreeCharts

namespace OAI

/-! A good covector supplies the actual free coordinate system for a mode. -/

noncomputable section

namespace ClosedSurfaceR4.RealModes

open SmallModes PhaseGeometry Set
open scoped ContDiff

lemma phaseInverse_det {ξ : Base} (hξ : ξ ≠ 0) :
    (((phaseEquiv ξ hξ).symm dx).1 * ((phaseEquiv ξ hξ).symm dy).2 -
      ((phaseEquiv ξ hξ).symm dx).2 * ((phaseEquiv ξ hξ).symm dy).1) ≠ 0 := by
  have hd : ξ.1 ^ 2 + ξ.2 ^ 2 ≠ 0 := (covector_length_sq_pos hξ).ne'
  have he :
      (((phaseEquiv ξ hξ).symm dx).1 * ((phaseEquiv ξ hξ).symm dy).2 -
        ((phaseEquiv ξ hξ).symm dx).2 * ((phaseEquiv ξ hξ).symm dy).1) =
        (ξ.1 ^ 2 + ξ.2 ^ 2)⁻¹ := by
    simp only [phaseEquiv_symm_apply, dx, dy]
    field_simp
    ring
  rw [he]
  exact inv_ne_zero hd

lemma phaseInverse_dy {ξ : Base} (hξ : ξ ≠ 0) :
    (phaseEquiv ξ hξ).symm dy = (ξ.1 ^ 2 + ξ.2 ^ 2)⁻¹ • (-ξ.2, ξ.1) := by
  ext <;> simp [dy, div_eq_mul_inv, mul_comm]

/-- The normal acceleration in the new y direction is a positive scalar
multiple of the old second fundamental form in the covector's kernel. -/
theorem realSecond_phase {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {ξ : Base} (hξ : ξ ≠ 0) (p : Base)
    (hImm : Function.Injective (fderiv ℝ F ((phaseEquiv ξ hξ).symm p))) :
    realSecond (F ∘ (phaseEquiv ξ hξ).symm) p =
      ((ξ.1 ^ 2 + ξ.2 ^ 2)⁻¹) ^ 2 •
        secondQuadratic (realSecondTensor F ((phaseEquiv ξ hξ).symm p)) (-ξ.2, ξ.1) := by
  change realSecondForm (F ∘ (phaseEquiv ξ hξ).symm) dy dy p = _
  have he := realSecondForm_comp_linear hF (phaseEquiv ξ hξ).symm.toContinuousLinearMap
    dy dy p (gramDet_ne_zero_of_injective _ hImm) (phaseInverse_det hξ)
  simp only [ContinuousLinearEquiv.coe_coe] at he
  rw [he]
  rw [phaseInverse_dy, realSecondForm_quadratic hF, secondQuadratic_smul]

/-- Immersion and the good-direction condition on an open set produce the
free-mode domain required by the finite oscillatory construction. -/
theorem realModeDomain_phase {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {O : Set Base} (hO : IsOpen O) {ξ : Base} (hξ : ξ ≠ 0)
    (hImm : ∀ p ∈ O, Function.Injective (fderiv ℝ F p))
    (hgood : ∀ p ∈ O, Good (realSecondTensor F p) ξ) :
    RealModeDomain (F ∘ (phaseEquiv ξ hξ).symm) ((phaseEquiv ξ hξ) '' O) := by
  refine ⟨(phaseEquiv ξ hξ).isOpenMap O hO, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    apply gramDet_ne_zero_of_injective
    rw [fderiv_comp _ (hF.differentiable (by simp) _)
      (phaseEquiv ξ hξ).symm.differentiableAt]
    simpa only [ContinuousLinearEquiv.fderiv, ContinuousLinearMap.coe_comp,
      ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply] using
      (hImm p hp).comp (phaseEquiv ξ hξ).symm.injective
  · rintro _ ⟨p, hp, rfl⟩
    have hi : Function.Injective (fderiv ℝ F
        ((phaseEquiv ξ hξ).symm ((phaseEquiv ξ hξ) p))) := by
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using hImm p hp
    rw [realSecond_phase hF hξ _ hi, ContinuousLinearEquiv.symm_apply_apply]
    exact smul_ne_zero (pow_ne_zero 2 (inv_ne_zero (covector_length_sq_pos hξ).ne'))
      (hgood p hp).2

/-- A good phase gives all coordinate data for a supported free chart. -/
def supportedFreeChartOfPhase {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {O S : Set Base} (hO : IsOpen O) (hS : IsClosed S) (hSO : S ⊆ O)
    {ξ : Base} (hξ : ξ ≠ 0) (ψ : Base → ℝ)
    (hImm : ∀ p ∈ O, Function.Injective (fderiv ℝ F p))
    (hgood : ∀ p ∈ O, Good (realSecondTensor F p) ξ)
    (hsupp : ∀ p ∈ O, phaseEquiv ξ hξ p ∈ tsupport ψ → p ∈ S) :
    SupportedFreeChart F (fun p => ξ.1 * p.1 + ξ.2 * p.2) ψ S where
  U := O
  V := (phaseEquiv ξ hξ) '' O
  χ := phaseEquiv ξ hξ
  e := (phaseEquiv ξ hξ).symm
  openU := hO
  closedS := hS
  supportU := hSO
  smoothFe := hF.comp (phaseEquiv ξ hξ).symm.contDiff
  domain := realModeDomain_phase hF hO hξ hImm hgood
  smoothχ := (phaseEquiv ξ hξ).contDiff.contDiffOn
  maps := fun p hp => ⟨p, hp, rfl⟩
  inverse := fun _ _ => (phaseEquiv ξ hξ).symm_apply_apply _
  phase := fun _ _ => rfl
  cutoff := hsupp

end ClosedSurfaceR4.RealModes

end

end OAI

import OAI.Geometry.SurfaceImmersion.Geometry.NormalDenominatorMargins
import OAI.Geometry.SurfaceImmersion.Atlas.PhaseReparametrization
import OAI.Geometry.Immersion.ClosedSurface.DenominatorBounds

namespace OAI

/-! Explicit reciprocal margins after the linear phase change. They depend
only polynomially on the phase covector and the original geometric margins. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.RealModes
open SmallModes PhaseGeometry

lemma phase_length_sq_le {ξ : Base} {C : ℝ} (hC : 0 ≤ C) (hξ : ‖ξ‖ ≤ C) :
    ξ.1^2+ξ.2^2 ≤ 2*C^2 := by
  have h1 : |ξ.1| ≤ C := by
    exact (show |ξ.1| ≤ ‖ξ‖ by simpa only [Real.norm_eq_abs] using norm_fst_le ξ).trans hξ
  have h2 : |ξ.2| ≤ C := by
    exact (show |ξ.2| ≤ ‖ξ‖ by simpa only [Real.norm_eq_abs] using norm_snd_le ξ).trans hξ
  have hs1 := (sq_le_sq₀ (abs_nonneg ξ.1) hC).mpr h1
  have hs2 := (sq_le_sq₀ (abs_nonneg ξ.2) hC).mpr h2
  rw [sq_abs] at hs1 hs2
  linarith

lemma gramDet_phase {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {ξ : Base} (hξ : ξ ≠ 0) (p : Base) :
    NormalFrame.gramDet (coordDeriv dx (F ∘ (phaseEquiv ξ hξ).symm) p)
      (coordDeriv dy (F ∘ (phaseEquiv ξ hξ).symm) p) =
      ((ξ.1^2+ξ.2^2)⁻¹)^2 * NormalFrame.gramDet
        (coordDeriv dx F ((phaseEquiv ξ hξ).symm p))
        (coordDeriv dy F ((phaseEquiv ξ hξ).symm p)) := by
  have hdet : ((phaseEquiv ξ hξ).symm dx).1 * ((phaseEquiv ξ hξ).symm dy).2 -
      ((phaseEquiv ξ hξ).symm dx).2 * ((phaseEquiv ξ hξ).symm dy).1 =
      (ξ.1^2+ξ.2^2)⁻¹ := by
    have hn := (covector_length_sq_pos hξ).ne'
    simp only [phaseEquiv_symm_apply,dx,dy]
    field_simp
    ring
  have hh := gramDet_comp_linear hF (phaseEquiv ξ hξ).symm.toContinuousLinearMap p
  simp only [ContinuousLinearEquiv.coe_coe] at hh
  exact hh.trans (by rw [hdet])

theorem inverse_gram_phase_bound {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {ξ : Base} (hξ : ξ ≠ 0) {C K : ℝ} (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hξC : ‖ξ‖ ≤ C) (p : Base)
    (hG : ‖(NormalFrame.gramDet (coordDeriv dx F ((phaseEquiv ξ hξ).symm p))
      (coordDeriv dy F ((phaseEquiv ξ hξ).symm p)))⁻¹‖ ≤ K) :
    ‖(NormalFrame.gramDet (coordDeriv dx (F ∘ (phaseEquiv ξ hξ).symm) p)
      (coordDeriv dy (F ∘ (phaseEquiv ξ hξ).symm) p))⁻¹‖ ≤ 4*C^4*K := by
  rw [gramDet_phase hF hξ,mul_inv_rev,inv_pow,inv_inv,norm_mul,
    Real.norm_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ K*(2*C^2)^2 := mul_le_mul hG
      (pow_le_pow_left₀ (by positivity) (phase_length_sq_le hC hξC) 2) (sq_nonneg _) hK
    _ = _ := by ring

theorem inverse_normal_phase_bound {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {ξ : Base} (hξ : ξ ≠ 0) {C K : ℝ} (hC : 0 ≤ C) (_hK : 0 ≤ K)
    (hξC : ‖ξ‖ ≤ C) (p : Base)
    (hImm : Function.Injective (fderiv ℝ F ((phaseEquiv ξ hξ).symm p)))
    (hS : secondQuadratic (realSecondTensor F ((phaseEquiv ξ hξ).symm p)) (-ξ.2,ξ.1) ≠ 0)
    (hN : ‖secondQuadratic (realSecondTensor F ((phaseEquiv ξ hξ).symm p)) (-ξ.2,ξ.1)‖⁻¹ ≤ K) :
    ‖(realSecond (F ∘ (phaseEquiv ξ hξ).symm) p ⬝ᵥ
      realSecond (F ∘ (phaseEquiv ξ hξ).symm) p)⁻¹‖ ≤ 16*C^8*K^2 := by
  let S := secondQuadratic (realSecondTensor F ((phaseEquiv ξ hξ).symm p)) (-ξ.2,ξ.1)
  have hSn : 0 < ‖S‖ := norm_pos_iff.mpr hS
  have hSi : ‖(S ⬝ᵥ S)⁻¹‖ ≤ K^2 := by
    have hh := norm_inv_dot_self_le hSn le_rfl
    rw [← inv_pow] at hh
    exact hh.trans (pow_le_pow_left₀ (inv_nonneg.mpr hSn.le) hN 2)
  rw [realSecond_phase hF hξ p hImm,smul_dotProduct,dotProduct_smul]
  simp only [smul_eq_mul,mul_inv_rev,inv_pow,inv_inv,norm_mul,
    Real.norm_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ K^2*((2*C^2)^2)*((2*C^2)^2) := by
      gcongr
      · exact phase_length_sq_le hC hξC
      · exact phase_length_sq_le hC hξC
    _ = _ := by ring

end ClosedSurfaceR4.RealModes

end

end OAI

import OAI.Geometry.SurfaceImmersion.Correction.PolynomialPhaseChartInverse
import OAI.Geometry.Immersion.ClosedSurface.CoordinateMargins
import OAI.Geometry.SurfaceImmersion.Geometry.NormalDenominatorMargins

namespace OAI

/-! Quantitative Gram and transverse-normal denominators in nonlinear
first-coordinate phase charts. -/
noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.PhaseGeometry
open SmallModes RealModes

lemma inverse_chart_det_inv (e : OpenPartialHomeomorph Base Base)
    (he : ContDiff ℝ ∞ e) (hi : ContDiff ℝ ∞ e.symm) {y : Base} (hy : y ∈ e.target) :
    (coordDet (fderiv ℝ e.symm y))⁻¹ = coordDet (fderiv ℝ e (e.symm y)) := by
  have hd := congrArg coordDet (inverse_chart_derivative e he hi hy)
  rw [coordDet_comp,coordDet_id] at hd
  have hn : coordDet (fderiv ℝ e.symm y) ≠ 0 := by
    intro hz
    rw [hz,mul_zero] at hd
    exact zero_ne_one hd
  have hh := congrArg (fun t => t*(coordDet (fderiv ℝ e.symm y))⁻¹) hd
  simpa only [mul_assoc,mul_inv_cancel₀ hn,mul_one,one_mul] using hh.symm

lemma realSecond_nonlinear_chart {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (e : OpenPartialHomeomorph Base Base) (he : ContDiff ℝ ∞ e)
    (hi : ContDiff ℝ ∞ e.symm) (hphase : ∀ x, (e x).1 = φ x)
    {y : Base} (hy : y ∈ e.target)
    (hImm : Function.Injective (fderiv ℝ F (e.symm y))) :
    realSecond (F ∘ e.symm) y = (coordDet (fderiv ℝ e.symm y))^2 •
      secondQuadratic (realSecondTensor F (e.symm y))
        (-(phaseDerivative φ (e.symm y)).2,(phaseDerivative φ (e.symm y)).1) := by
  have hdet := coordDet_fderiv_ne_zero_of_local_inverse e.open_target e.open_source
    hi.contDiffOn he.contDiffOn (fun z hz => e.map_target hz) (fun z hz => e.right_inv hz) hy
  have hh := phase_length_comp_smooth hF hi (phaseDerivative φ (e.symm y)) y
    (gramDet_ne_zero_of_injective _ hImm) hdet
  rw [inverse_chart_phase_covector hφ e hi hphase hy] at hh
  have hdx : (-(dx : Base).2,(dx : Base).1) = dy := by simp [dx,dy]
  rw [hdx] at hh
  change secondQuadratic (realSecondTensor (F ∘ e.symm) y) dy = _ at hh
  change realSecondForm (F ∘ e.symm) dy dy y = _
  rw [realSecondForm_quadratic (hF.comp hi)]
  exact hh

theorem inverse_gram_nonlinear_chart_bound {F : RField 4} (hF : ContDiff ℝ ∞ F)
    (e : OpenPartialHomeomorph Base Base) (he : ContDiff ℝ ∞ e)
    (hi : ContDiff ℝ ∞ e.symm) {y : Base} (hy : y ∈ e.target)
    {D K : ℝ} (_hD : 0 ≤ D) (hK : 0 ≤ K)
    (hdet : |coordDet (fderiv ℝ e (e.symm y))| ≤ D)
    (hG : ‖(NormalFrame.gramDet (coordDeriv dx F (e.symm y))
      (coordDeriv dy F (e.symm y)))⁻¹‖ ≤ K) :
    ‖(NormalFrame.gramDet (coordDeriv dx (F ∘ e.symm) y)
      (coordDeriv dy (F ∘ e.symm) y))⁻¹‖ ≤ K*D^2 := by
  have hg := gramDet_comp_smooth hF hi y
  change _ = (coordDet (fderiv ℝ e.symm y))^2 * _ at hg
  rw [hg,mul_inv_rev,← inv_pow,norm_mul,norm_pow,inverse_chart_det_inv e he hi hy,
    Real.norm_eq_abs]
  exact mul_le_mul hG (pow_le_pow_left₀ (abs_nonneg _) hdet 2) (by positivity) hK

theorem inverse_normal_nonlinear_chart_bound {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {φ : Base → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (e : OpenPartialHomeomorph Base Base) (he : ContDiff ℝ ∞ e)
    (hi : ContDiff ℝ ∞ e.symm) (hphase : ∀ x, (e x).1 = φ x)
    {y : Base} (hy : y ∈ e.target) {D K : ℝ} (_hD : 0 ≤ D)
    (hdet : |coordDet (fderiv ℝ e (e.symm y))| ≤ D)
    (hImm : Function.Injective (fderiv ℝ F (e.symm y)))
    (hgood : Good (realSecondTensor F (e.symm y)) (phaseDerivative φ (e.symm y)))
    (hN : ‖secondQuadratic (realSecondTensor F (e.symm y))
      (-(phaseDerivative φ (e.symm y)).2,(phaseDerivative φ (e.symm y)).1)‖⁻¹ ≤ K) :
    ‖(realSecond (F ∘ e.symm) y ⬝ᵥ realSecond (F ∘ e.symm) y)⁻¹‖ ≤ K^2*D^4 := by
  let S := secondQuadratic (realSecondTensor F (e.symm y))
    (-(phaseDerivative φ (e.symm y)).2,(phaseDerivative φ (e.symm y)).1)
  have hSn : 0 < ‖S‖ := norm_pos_iff.mpr hgood.2
  have hSi : ‖(S ⬝ᵥ S)⁻¹‖ ≤ K^2 := by
    have hh := norm_inv_dot_self_le hSn le_rfl
    rw [← inv_pow] at hh
    exact hh.trans (pow_le_pow_left₀ (inv_nonneg.mpr hSn.le) hN 2)
  rw [realSecond_nonlinear_chart hF hφ e he hi hphase hy hImm,
    smul_dotProduct,dotProduct_smul]
  simp only [smul_eq_mul,mul_inv_rev,← inv_pow,norm_mul,norm_pow,
    inverse_chart_det_inv e he hi hy]
  calc
    _ ≤ K^2*D^2*D^2 := by
      gcongr
      · simpa only [Real.norm_eq_abs] using hdet
      · simpa only [Real.norm_eq_abs] using hdet
    _ = K^2*D^4 := by ring

end ClosedSurfaceR4.PhaseGeometry

end

end OAI

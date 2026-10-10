import OAI.Dynamics.TriangleBilliards.MeasurePreservation

namespace OAI

open MeasureTheory Set
open scoped ENNReal symmDiff
noncomputable section

/-! Euclidean radial smoothing in local charts, used to construct
the global operator on the triangular double. -/

open MeasureTheory Set Filter Function Metric
open scoped Topology Convolution ContDiff

noncomputable section

namespace TriangularBilliards.SpatialSmoothing

/-- An explicit smooth radial bump. It is one on the half-unit disk,
positive in the unit disk and zero outside it. -/
def raw (x : ℂ) : ℝ := (ContDiffBumpBase.ofInnerProductSpace ℂ).toFun 2 ((2 : ℝ) • x)

lemma raw_nonneg (x : ℂ) : 0 ≤ raw x :=
  ((ContDiffBumpBase.ofInnerProductSpace ℂ).mem_Icc 2 _).1

lemma raw_le_one (x : ℂ) : raw x ≤ 1 :=
  ((ContDiffBumpBase.ofInnerProductSpace ℂ).mem_Icc 2 _).2

lemma raw_radial {x y : ℂ} (h : ‖x‖ = ‖y‖) : raw x = raw y := by
  simp only [raw, ContDiffBumpBase.ofInnerProductSpace, norm_smul, h]

lemma raw_neg (x : ℂ) : raw (-x) = raw x := raw_radial (norm_neg x)

lemma raw_contDiff : ContDiff ℝ ∞ raw := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have hs := (ContDiffBumpBase.ofInnerProductSpace ℂ).smooth.contDiffAt
    (x := ((2 : ℝ), (2 : ℝ) • x))
    (prod_mem_nhds (Ioi_mem_nhds (by norm_num : (1 : ℝ) < 2)) univ_mem)
  have hc : ContDiffAt ℝ ∞ (fun y : ℂ => ((2 : ℝ), (2 : ℝ) • y)) x := by fun_prop
  have hh := hs.comp x hc
  exact hh

lemma raw_support : support raw = ball (0 : ℂ) 1 := by
  have hs := (ContDiffBumpBase.ofInnerProductSpace ℂ).support 2 (by norm_num)
  ext x
  change ((2 : ℝ) • x) ∈ support ((ContDiffBumpBase.ofInnerProductSpace ℂ).toFun 2) ↔ _
  rw [hs]
  simp only [mem_ball_zero_iff, norm_smul, Real.norm_ofNat]
  constructor <;> intro h <;> linarith

lemma raw_hasCompactSupport : HasCompactSupport raw := by
  rw [HasCompactSupport, tsupport, raw_support, closure_ball _ (by norm_num : (1 : ℝ) ≠ 0)]
  exact isCompact_closedBall _ _

lemma raw_integrable : Integrable raw volume :=
  raw_contDiff.continuous.integrable_of_hasCompactSupport raw_hasCompactSupport

lemma raw_integral_pos : 0 < ∫ x : ℂ, raw x := by
  apply (integral_pos_iff_support_of_nonneg raw_nonneg raw_integrable).mpr
  rw [raw_support]
  exact measure_ball_pos volume 0 (by norm_num)

/-- The chosen radial mollifier of unit mass. -/
def rho (x : ℂ) : ℝ := raw x / ∫ y : ℂ, raw y

lemma rho_nonneg (x : ℂ) : 0 ≤ rho x := div_nonneg (raw_nonneg x) raw_integral_pos.le

lemma rho_radial {x y : ℂ} (h : ‖x‖ = ‖y‖) : rho x = rho y := by
  rw [rho, rho, raw_radial h]

lemma rho_neg (x : ℂ) : rho (-x) = rho x := rho_radial (norm_neg x)

lemma rho_contDiff : ContDiff ℝ ∞ rho := raw_contDiff.div_const _

lemma rho_support : support rho = ball (0 : ℂ) 1 := by
  change support (fun x => raw x / ∫ y : ℂ, raw y) = _
  rw [support_div, raw_support, support_const raw_integral_pos.ne', inter_univ]

lemma rho_hasCompactSupport : HasCompactSupport rho := by
  rw [HasCompactSupport, tsupport, rho_support, closure_ball _ (by norm_num : (1 : ℝ) ≠ 0)]
  exact isCompact_closedBall _ _

lemma rho_integrable : Integrable rho volume := raw_integrable.div_const _

lemma rho_integral : ∫ x : ℂ, rho x = 1 := by
  change (∫ x : ℂ, raw x / ∫ y : ℂ, raw y) = 1
  rw [integral_div]
  exact div_self raw_integral_pos.ne'

/-- Exact two-dimensional rescaling `ε⁻² ρ(x/ε)`. -/
def kernel (ε : ℝ) (x : ℂ) : ℝ := (ε ^ 2)⁻¹ * rho (ε⁻¹ • x)

lemma kernel_nonneg (ε : ℝ) (x : ℂ) : 0 ≤ kernel ε x :=
  mul_nonneg (inv_nonneg.mpr (sq_nonneg ε)) (rho_nonneg _)

lemma kernel_radial (ε : ℝ) {x y : ℂ} (h : ‖x‖ = ‖y‖) : kernel ε x = kernel ε y := by
  have hs : ‖ε⁻¹ • x‖ = ‖ε⁻¹ • y‖ := by rw [norm_smul, norm_smul, h]
  rw [kernel, kernel, rho_radial hs]

lemma kernel_neg (ε : ℝ) (x : ℂ) : kernel ε (-x) = kernel ε x :=
  kernel_radial ε (norm_neg x)

lemma kernel_contDiff (ε : ℝ) : ContDiff ℝ ∞ (kernel ε) :=
  contDiff_const.mul (rho_contDiff.comp (by fun_prop :
    ContDiff ℝ ∞ (fun x : ℂ => ε⁻¹ • x)))

lemma kernel_support {ε : ℝ} (hε : 0 < ε) : support (kernel ε) = ball (0 : ℂ) ε := by
  ext x
  rw [mem_support]
  change (ε ^ 2)⁻¹ * rho (ε⁻¹ • x) ≠ 0 ↔ _
  rw [mul_ne_zero_iff]
  have hne : (ε ^ 2)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hε.ne')
  rw [and_iff_right hne, ← mem_support, rho_support]
  simp only [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hε,
    ← div_eq_inv_mul]
  rw [div_lt_iff₀ hε, one_mul]

lemma kernel_hasCompactSupport {ε : ℝ} (hε : 0 < ε) : HasCompactSupport (kernel ε) := by
  rw [HasCompactSupport, tsupport, kernel_support hε, closure_ball _ hε.ne']
  exact isCompact_closedBall _ _

lemma kernel_integrable {ε : ℝ} (hε : 0 < ε) : Integrable (kernel ε) volume :=
  (kernel_contDiff ε).continuous.integrable_of_hasCompactSupport (kernel_hasCompactSupport hε)

lemma kernel_integral {ε : ℝ} (hε : 0 < ε) : ∫ x : ℂ, kernel ε x = 1 := by
  change (∫ x : ℂ, (ε ^ 2)⁻¹ * rho (ε⁻¹ • x)) = 1
  rw [integral_const_mul, Measure.integral_comp_smul volume rho ε⁻¹,
    Complex.finrank_real_complex, inv_pow, inv_inv, abs_of_nonneg (sq_nonneg ε),
    smul_eq_mul, rho_integral, mul_one]
  exact inv_mul_cancel₀ (pow_ne_zero _ hε.ne')

/-- The actual first-derivative kernel, with its exact dimensional scaling. -/
lemma kernel_fderiv (ε : ℝ) (x : ℂ) :
    fderiv ℝ (kernel ε) x = (ε ^ 3)⁻¹ • fderiv ℝ rho (ε⁻¹ • x) := by
  have hd := ((rho_contDiff.differentiable (by simp) (ε⁻¹ • x)).hasFDerivAt.comp x
    ((hasFDerivAt_id x).const_smul ε⁻¹)).const_mul ((ε ^ 2)⁻¹)
  have he : (ε ^ 2)⁻¹ •
      ((fderiv ℝ rho (ε⁻¹ • x)).comp (ε⁻¹ • ContinuousLinearMap.id ℝ ℂ)) =
      (ε ^ 3)⁻¹ • fderiv ℝ rho (ε⁻¹ • x) := by
    rw [ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_id, smul_smul]
    congr 1
    ring
  rw [← he]
  exact hd.fderiv

lemma rho_fderiv_integrable : Integrable (fderiv ℝ rho) volume :=
  (rho_contDiff.continuous_fderiv (by simp)).integrable_of_hasCompactSupport
    (rho_hasCompactSupport.fderiv ℝ)

lemma kernel_fderiv_integrable {ε : ℝ} (hε : 0 < ε) :
    Integrable (fderiv ℝ (kernel ε)) volume :=
  ((kernel_contDiff ε).continuous_fderiv (by simp)).integrable_of_hasCompactSupport
    ((kernel_hasCompactSupport hε).fderiv ℝ)

def derivativeMass : ℝ := ∫ x : ℂ, ‖fderiv ℝ rho x‖

lemma derivativeMass_nonneg : 0 ≤ derivativeMass := integral_nonneg (fun _ => norm_nonneg _)

lemma kernel_derivative_mass {ε : ℝ} (hε : 0 < ε) :
    (∫ x : ℂ, ‖fderiv ℝ (kernel ε) x‖) = derivativeMass / ε := by
  simp_rw [kernel_fderiv, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (pow_pos hε 3))]
  rw [integral_const_mul, Measure.integral_comp_smul volume (fun x : ℂ => ‖fderiv ℝ rho x‖) ε⁻¹,
    Complex.finrank_real_complex, inv_pow, inv_inv, abs_of_nonneg (sq_nonneg ε), smul_eq_mul]
  change (ε ^ 3)⁻¹ * (ε ^ 2 * derivativeMass) = derivativeMass / ε
  field_simp

lemma kernel_derivative_lintegral {ε : ℝ} (hε : 0 < ε) :
    ∫⁻ x : ℂ, ENNReal.ofReal ‖fderiv ℝ (kernel ε) x‖ =
      ENNReal.ofReal (derivativeMass / ε) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (kernel_fderiv_integrable hε).norm
    (Filter.Eventually.of_forall (fun _ => norm_nonneg _)), kernel_derivative_mass hε]

end TriangularBilliards.SpatialSmoothing

end
end

end OAI

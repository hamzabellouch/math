import Mathlib
import OAI.Geometry.TamingCompatibility.Functional.RadialNorm
import OAI.Geometry.TamingCompatibility.DifferentialForms.TwoDirection

namespace OAI


noncomputable section
namespace TamingCompatibility.RadialPotential
open ContinuousAlternatingMap
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma log_error_coefficient {a t L M : ℝ} (ha : 0 < a) (ht : t ≤ a)
    (hL : 0 ≤ L) (hM : 0 ≤ M) :
    6/a^2*(L*t)*(M+M)+2*(2/a)*L*M ≤ 16*L*M/a := by
  apply (le_div_iff₀ ha).mpr
  field_simp
  nlinarith [mul_nonneg (mul_nonneg hL hM) (sub_nonneg.mpr ht)]

lemma sqrt_error_coefficient {a t L M : ℝ} (ha : 0 < a) (ht : t ≤ a)
    (hL : 0 ≤ L) (hM : 0 ≤ M) :
    4/a*(L*t)*(M+M)+2*1*L*M ≤ 10*L*M := by
  field_simp
  nlinarith [mul_nonneg (mul_nonneg hL hM) (sub_nonneg.mpr ht)]

lemma log_ddc_perturbation {J : E → E →L[ℝ] E} (K : E →L[ℝ] E)
    {s : ℝ} (hs : 0 < s) (z v : E) (hJ : DifferentiableAt ℝ J z)
    (hJJ : ∀ v, J z (J z v) = -v) (hKK : ∀ v, K (K v) = -v)
    {L M : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hdiff : ‖J z-K‖ ≤ L*‖z‖) (hdJ : ‖fderiv ℝ J z‖ ≤ L)
    (hJn : ‖J z‖ ≤ M) (hKn : ‖K‖ ≤ M) :
    ‖extDeriv (ExteriorForms.dc J (logPotential s)) z ![v,J z v] -
      extDeriv (ExteriorForms.dc (fun _ => K) (logPotential s)) z ![v,K v]‖ ≤
      (16*L*M/(s+‖z‖))*‖v‖^2 := by
  have ha : 0 < s+‖z‖ := by positivity
  have hc : ContDiffAt ℝ 2 (logPotential s) z :=
    contDiffAt_infty.mp (logPotential_smooth hs).contDiffAt 2
  have hdf : DifferentiableAt ℝ (fderiv ℝ (logPotential s)) z :=
    (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  calc
    _ ≤ (‖fderiv ℝ (fderiv ℝ (logPotential s)) z‖*‖J z-K‖*(‖J z‖+‖K‖) +
        2*‖fderiv ℝ (logPotential s) z‖*‖fderiv ℝ J z‖*‖J z‖)*‖v‖^2 :=
      ddc_perturbation_bound K hdf hJ hJJ hKK v
    _ ≤ (6/(s+‖z‖)^2*(L*‖z‖)*(M+M)+2*(2/(s+‖z‖))*L*M)*‖v‖^2 := by
      gcongr
      · exact norm_logPotential_hessian hs z
      · exact norm_logPotential_fderiv hs z
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (log_error_coefficient ha (by linarith) hL hM) (sq_nonneg ‖v‖)

lemma sqrt_ddc_perturbation {J : E → E →L[ℝ] E} (K : E →L[ℝ] E)
    {s : ℝ} (hs : 0 < s) (z v : E) (hJ : DifferentiableAt ℝ J z)
    (hJJ : ∀ v, J z (J z v) = -v) (hKK : ∀ v, K (K v) = -v)
    {L M : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hdiff : ‖J z-K‖ ≤ L*‖z‖) (hdJ : ‖fderiv ℝ J z‖ ≤ L)
    (hJn : ‖J z‖ ≤ M) (hKn : ‖K‖ ≤ M) :
    ‖extDeriv (ExteriorForms.dc J (sqrtPotential s)) z ![v,J z v] -
      extDeriv (ExteriorForms.dc (fun _ => K) (sqrtPotential s)) z ![v,K v]‖ ≤
      (10*L*M)*‖v‖^2 := by
  have ha : 0 < s+‖z‖ := by positivity
  have hc : ContDiffAt ℝ 2 (sqrtPotential s) z :=
    contDiffAt_infty.mp (sqrtPotential_smooth hs).contDiffAt 2
  have hdf : DifferentiableAt ℝ (fderiv ℝ (sqrtPotential s)) z :=
    (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  calc
    _ ≤ (‖fderiv ℝ (fderiv ℝ (sqrtPotential s)) z‖*‖J z-K‖*(‖J z‖+‖K‖) +
        2*‖fderiv ℝ (sqrtPotential s) z‖*‖fderiv ℝ J z‖*‖J z‖)*‖v‖^2 :=
      ddc_perturbation_bound K hdf hJ hJJ hKK v
    _ ≤ (4/(s+‖z‖)*(L*‖z‖)*(M+M)+2*1*L*M)*‖v‖^2 := by
      gcongr
      · exact norm_sqrtPotential_hessian hs z
      · exact norm_sqrtPotential_fderiv hs z
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (sqrt_error_coefficient ha (by linarith) hL hM) (sq_nonneg ‖v‖)
end TamingCompatibility.RadialPotential

end

end OAI

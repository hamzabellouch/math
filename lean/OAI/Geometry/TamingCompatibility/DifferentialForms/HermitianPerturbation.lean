import Mathlib
import OAI.Geometry.TamingCompatibility.Functional.RadialPerturbation
import OAI.Geometry.TamingCompatibility.Elliptic.HermitianDerivativeNorms

namespace OAI

section
section

section
noncomputable section
namespace TamingCompatibility.RadialPotential
open ContinuousAlternatingMap
open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma hermitianLog_ddc_perturbation {J : E → E →L[ℝ] E} (K : E →L[ℝ] E)
    {s : ℝ} (hs : 0 < s) (z v : E) (hJ : DifferentiableAt ℝ J z)
    (hJJ : ∀ v, J z (J z v) = -v) (hKK : ∀ v, K (K v) = -v)
    {L M : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hdiff : ‖J z-K‖ ≤ L*‖z‖) (hdJ : ‖fderiv ℝ J z‖ ≤ L)
    (hJn : ‖J z‖ ≤ M) (hKn : ‖K‖ ≤ M) :
    ‖extDeriv (ExteriorForms.dc J (hermitianLogPotential K s)) z ![v,J z v] -
      extDeriv (ExteriorForms.dc (fun _ => K) (hermitianLogPotential K s)) z ![v,K v]‖ ≤
      ((1+M)^2*(16*L*M/(s+‖z‖)))*‖v‖^2 := by
  have ha : 0 < s+‖z‖ := by positivity
  have hc : ContDiffAt ℝ 2 (hermitianLogPotential K s) z :=
    contDiffAt_infty.mp (hermitianLogPotential_smooth K hs).contDiffAt 2
  have hdf : DifferentiableAt ℝ (fderiv ℝ (hermitianLogPotential K s)) z :=
    (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hNs : 1+M ≤ (1+M)^2 := by nlinarith
  have hgN : 1+‖K‖ ≤ (1+M)^2 := (show 1+‖K‖ ≤ 1+M by linarith).trans hNs
  have hhN : (1+‖K‖)^2 ≤ (1+M)^2 := by gcongr
  calc
    _ ≤ (‖fderiv ℝ (fderiv ℝ (hermitianLogPotential K s)) z‖*‖J z-K‖*(‖J z‖+‖K‖) +
        2*‖fderiv ℝ (hermitianLogPotential K s) z‖*‖fderiv ℝ J z‖*‖J z‖)*‖v‖^2 :=
      ddc_perturbation_bound K hdf hJ hJJ hKK v
    _ ≤ ((1+M)^2*(6/(s+‖z‖)^2*(L*‖z‖)*(M+M)+2*(2/(s+‖z‖))*L*M))*‖v‖^2 := by
      have hh := (norm_hermitianLog_hessian K hs z).trans
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hhN (by norm_num)) (sq_nonneg _))
      have hg := (norm_hermitianLog_gradient K hs z).trans
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hgN (by norm_num)) ha.le)
      calc
        _ ≤ ((6*(1+M)^2/(s+‖z‖)^2)*(L*‖z‖)*(M+M) +
            2*(2*(1+M)^2/(s+‖z‖))*L*M)*‖v‖^2 := by gcongr
        _ = _ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (log_error_coefficient ha (by linarith) hL hM) (sq_nonneg _)) (sq_nonneg ‖v‖)

lemma hermitianSqrt_ddc_perturbation {J : E → E →L[ℝ] E} (K : E →L[ℝ] E)
    {s : ℝ} (hs : 0 < s) (z v : E) (hJ : DifferentiableAt ℝ J z)
    (hJJ : ∀ v, J z (J z v) = -v) (hKK : ∀ v, K (K v) = -v)
    {L M : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hdiff : ‖J z-K‖ ≤ L*‖z‖) (hdJ : ‖fderiv ℝ J z‖ ≤ L)
    (hJn : ‖J z‖ ≤ M) (hKn : ‖K‖ ≤ M) :
    ‖extDeriv (ExteriorForms.dc J (hermitianSqrtPotential K s)) z ![v,J z v] -
      extDeriv (ExteriorForms.dc (fun _ => K) (hermitianSqrtPotential K s)) z ![v,K v]‖ ≤
      ((1+M)^2*(10*L*M))*‖v‖^2 := by
  have ha : 0 < s+‖z‖ := by positivity
  have hc : ContDiffAt ℝ 2 (hermitianSqrtPotential K s) z :=
    contDiffAt_infty.mp (hermitianSqrtPotential_smooth K hs).contDiffAt 2
  have hdf : DifferentiableAt ℝ (fderiv ℝ (hermitianSqrtPotential K s)) z :=
    (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hNs : 1+M ≤ (1+M)^2 := by nlinarith
  have hgN : 1+‖K‖ ≤ (1+M)^2 := (show 1+‖K‖ ≤ 1+M by linarith).trans hNs
  have hhN : (1+‖K‖)^2 ≤ (1+M)^2 := by gcongr
  calc
    _ ≤ (‖fderiv ℝ (fderiv ℝ (hermitianSqrtPotential K s)) z‖*‖J z-K‖*(‖J z‖+‖K‖) +
        2*‖fderiv ℝ (hermitianSqrtPotential K s) z‖*‖fderiv ℝ J z‖*‖J z‖)*‖v‖^2 :=
      ddc_perturbation_bound K hdf hJ hJJ hKK v
    _ ≤ ((1+M)^2*(4/(s+‖z‖)*(L*‖z‖)*(M+M)+2*1*L*M))*‖v‖^2 := by
      have hh := (norm_hermitianSqrt_hessian K hs z).trans
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hhN (by norm_num)) ha.le)
      have hg := (norm_hermitianSqrt_gradient K hs z).trans hgN
      calc
        _ ≤ ((4*(1+M)^2/(s+‖z‖))*(L*‖z‖)*(M+M) +
            2*((1+M)^2)*L*M)*‖v‖^2 := by gcongr
        _ = _ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (sqrt_error_coefficient ha (by linarith) hL hM) (sq_nonneg _)) (sq_nonneg ‖v‖)
end TamingCompatibility.RadialPotential

end
end

section
noncomputable section
namespace TamingCompatibility.RadialPotential
open ContinuousAlternatingMap
open scoped ContDiff RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma hermitianLog_variable_ddc_lower {J : E → E →L[ℝ] E} (K : E →L[ℝ] E)
    {s : ℝ} (hs : 0 < s) (z v : E) (hJ : DifferentiableAt ℝ J z)
    (hJJ : ∀ v, J z (J z v) = -v) (hKK : ∀ v, K (K v) = -v)
    {L M : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hdiff : ‖J z-K‖ ≤ L*‖z‖) (hdJ : ‖fderiv ℝ J z‖ ≤ L)
    (hJn : ‖J z‖ ≤ M) (hKn : ‖K‖ ≤ M) :
    2*s^2*(‖v‖^2+‖K v‖^2)/(s^2+‖z‖^2+‖K z‖^2)^2 -
      ((1+M)^2*(16*L*M/(s+‖z‖)))*‖v‖^2 ≤
      extDeriv (ExteriorForms.dc J (hermitianLogPotential K s)) z ![v,J z v] := by
  have hp := hermitianLog_ddc_perturbation K hs z v hJ hJJ hKK hL hM hdiff hdJ hJn hKn
  have hb := hermitianLog_ddc_lower K hKK hs z v
  rw [Real.norm_eq_abs,abs_le] at hp
  linarith [hp.1]

lemma hermitian_sqrt_radius_bound (K : E →L[ℝ] E) {s M : ℝ} (hs : 0 < s)
    (hM : 0 ≤ M) (hK : ‖K‖ ≤ M) (z : E) :
    Real.sqrt (s^2+‖z‖^2+‖K z‖^2) ≤ (1+M)*(s+‖z‖) := by
  have hG : ‖hermitianGraph K z‖ ≤ (1+M)*‖z‖ :=
    ((hermitianGraph K).le_opNorm z).trans
      (mul_le_mul_of_nonneg_right ((norm_hermitianGraph_le K).trans (by linarith)) (norm_nonneg _))
  have hp : 0 ≤ s^2+‖z‖^2+‖K z‖^2 := by positivity
  have hq := Real.sq_sqrt hp
  have he := hermitianGraph_norm_sq K z
  have hsum : Real.sqrt (s^2+‖z‖^2+‖K z‖^2) ≤ s+‖hermitianGraph K z‖ := by
    nlinarith [Real.sqrt_nonneg (s^2+‖z‖^2+‖K z‖^2),
      norm_nonneg (hermitianGraph K z),mul_nonneg hs.le (norm_nonneg (hermitianGraph K z))]
  nlinarith [mul_nonneg hM hs.le]

lemma hermitianSqrt_variable_ddc_lower {J : E → E →L[ℝ] E} (K : E →L[ℝ] E)
    {s : ℝ} (hs : 0 < s) (z v : E) (hJ : DifferentiableAt ℝ J z)
    (hJJ : ∀ v, J z (J z v) = -v) (hKK : ∀ v, K (K v) = -v)
    {L M : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hdiff : ‖J z-K‖ ≤ L*‖z‖) (hdJ : ‖fderiv ℝ J z‖ ≤ L)
    (hJn : ‖J z‖ ≤ M) (hKn : ‖K‖ ≤ M) :
    ‖v‖^2/((1+M)*(s+‖z‖)) - ((1+M)^2*(10*L*M))*‖v‖^2 ≤
      extDeriv (ExteriorForms.dc J (hermitianSqrtPotential K s)) z ![v,J z v] := by
  have hp := hermitianSqrt_ddc_perturbation K hs z v hJ hJJ hKK hL hM hdiff hdJ hJn hKn
  have hb := hermitianSqrt_ddc_lower K hKK hs z v
  have hq : 0 < Real.sqrt (s^2+‖z‖^2+‖K z‖^2) := Real.sqrt_pos.mpr (by positivity)
  have hden : ‖v‖^2/((1+M)*(s+‖z‖)) ≤
      (‖v‖^2+‖K v‖^2)/Real.sqrt (s^2+‖z‖^2+‖K z‖^2) := by
    calc
      _ ≤ ‖v‖^2/Real.sqrt (s^2+‖z‖^2+‖K z‖^2) :=
        div_le_div_of_nonneg_left (sq_nonneg _) hq (hermitian_sqrt_radius_bound K hs hM hKn z)
      _ ≤ _ := div_le_div_of_nonneg_right (by nlinarith [sq_nonneg ‖K v‖]) hq.le
  rw [Real.norm_eq_abs,abs_le] at hp
  linarith [hp.1]

lemma hermitian_log_trace_inner (K : E →L[ℝ] E) {s M : ℝ} (hs : 0 < s)
    (hM : 0 ≤ M) (hK : ‖K‖ ≤ M) (z v : E) (hz : ‖z‖ ≤ s) :
    (2/(1+(1+M)^2)^2)*(‖v‖^2/s^2) ≤
      2*s^2*(‖v‖^2+‖K v‖^2)/(s^2+‖z‖^2+‖K z‖^2)^2 := by
  have hG : ‖hermitianGraph K z‖ ≤ (1+M)*s :=
    ((hermitianGraph K).le_opNorm z).trans
      (mul_le_mul ((norm_hermitianGraph_le K).trans (by linarith)) hz (norm_nonneg _) (by positivity))
  have hG2 := pow_le_pow_left₀ (norm_nonneg (hermitianGraph K z)) hG 2
  rw [hermitianGraph_norm_sq,mul_pow] at hG2
  have hA : s^2+‖z‖^2+‖K z‖^2 ≤ (1+(1+M)^2)*s^2 := by nlinarith
  have hA0 : 0 < s^2+‖z‖^2+‖K z‖^2 := by positivity
  have hb : 0 < (1+(1+M)^2)*s^2 := by positivity
  calc
    _ = (2*s^2*‖v‖^2)/((1+(1+M)^2)*s^2)^2 := by field_simp
    _ ≤ (2*s^2*‖v‖^2)/(s^2+‖z‖^2+‖K z‖^2)^2 :=
      div_le_div_of_nonneg_left (by positivity) (pow_pos hA0 2)
        (pow_le_pow_left₀ hA0.le hA 2)
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (sq_nonneg ‖K v‖)) (by positivity))
      (sq_nonneg _)
end TamingCompatibility.RadialPotential

end
end

end
end

end OAI

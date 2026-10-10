import Mathlib
import OAI.Probability.SKRatio.Matrices.StandardGaussianProduct

namespace OAI

section
section
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set
open scoped NNReal ENNReal
open Filter
open scoped Topology
namespace SKRatioGaussian
lemma tendsto_gaussianPDFReal_atTop (d : ℝ) {s : ℝ≥0} (hs : 0 < s) :
    Filter.Tendsto (gaussianPDFReal d s) Filter.atTop (𝓝 0) := by
  have hsp : (0:ℝ) < s := hs
  have hshift : Tendsto (fun x : ℝ => x-d) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (b+d)] with x hx
    linarith
  have hpow : Filter.Tendsto (fun x : ℝ => (x-d)^2) Filter.atTop Filter.atTop :=
    (tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0)).comp hshift
  have hexp := Real.tendsto_exp_neg_atTop_nhds_zero.comp (hpow.atTop_div_const (by positivity : 0 < 2*(s:ℝ)))
  rw [gaussianPDFReal_def]
  simpa only [neg_div, mul_zero,one_div,Function.comp_apply] using hexp.const_mul (1/sqrt (2*Real.pi*(s:ℝ)))

lemma tendsto_gaussianPDFReal_neg_atTop (d : ℝ) {s : ℝ≥0} (hs : 0 < s) :
    Filter.Tendsto (fun x => gaussianPDFReal d s (-x)) Filter.atTop (𝓝 0) := by
  have he : (fun x => gaussianPDFReal d s (-x)) = gaussianPDFReal (-d) s := by
    funext x
    unfold gaussianPDFReal
    congr 2
    ring
  rw [he]
  exact tendsto_gaussianPDFReal_atTop (-d) hs

theorem gaussian_lipschitz_IBP {f : ℝ → ℝ} {L : ℝ≥0} {C d : ℝ} {s : ℝ≥0}
    (hs : 0 < s) (hL : LipschitzWith L f) (hC : ∀ x, ‖f x‖ ≤ C) :
    (∫ y, (y-d)*f y ∂gaussianReal d s) = (s:ℝ)*(∫ y, deriv f y ∂gaussianReal d s) := by
  have hC0 : 0 ≤ C := (norm_nonneg (f 0)).trans (hC 0)
  have hdf : Integrable (deriv f) (gaussianReal d s) :=
    Integrable.of_bound (measurable_deriv f).aestronglyMeasurable (L:ℝ)
      (ae_of_all _ (fun _ => norm_deriv_le_of_lipschitz hL))
  have hyf : Integrable (fun y => (y-d)*f y) (gaussianReal d s) := by
    have hh := ((IsGaussian.integrable_id (μ := gaussianReal d s)).sub (integrable_const d)).bdd_mul
      (f := f) hL.continuous.aestronglyMeasurable (ae_of_all _ hC)
    simpa only [mul_comm,Pi.sub_apply,id_eq] using hh
  let p := gaussianPDFReal d s
  have hpi : Integrable (fun y => p y*deriv f y) := (integrable_gaussian_iff hs.ne').mp hdf
  have hxi : Integrable (fun y => p y*((y-d)*f y)) := (integrable_gaussian_iff hs.ne').mp hyf
  let g : ℝ → ℝ := fun y => p y*deriv f y-(p y*((y-d)*f y))/(s:ℝ)
  have hgi : Integrable g := hpi.sub (hxi.div_const _)
  have hpd (y : ℝ) : deriv p y = -(y-d)/(s:ℝ)*p y := (hasDerivAt_gaussianPDFReal d hs.ne' y).deriv
  have hpac (a b : ℝ) : AbsolutelyContinuousOnInterval p a b := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    have hh : ContDiff ℝ 1 p := by
      change ContDiff ℝ 1 (fun x : ℝ => (sqrt (2 * π * (s : ℝ)))⁻¹ * exp (-(x-d)^2/(2*(s:ℝ))))
      fun_prop
    exact hh.contDiffOn
  have hfac (a b : ℝ) : AbsolutelyContinuousOnInterval f a b := hL.lipschitzOnWith.absolutelyContinuousOnInterval
  have hftc (a b : ℝ) : (∫ y in a..b, g y) = p b*f b-p a*f a := by
    rw [← (hpac a b).integral_deriv_mul_eq_sub (hfac a b)]
    apply intervalIntegral.integral_congr
    intro y _
    dsimp [g]
    rw [hpd]
    ring
  have hbd (u : ℝ → ℝ) (hp : Filter.Tendsto (fun x => p (u x)) Filter.atTop (𝓝 0)) :
      Filter.Tendsto (fun x => p (u x)*f (u x)) Filter.atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun x => ?_) (by simpa only [zero_mul] using hp.mul_const C)
    rw [norm_mul, Real.norm_eq_abs (p (u x)),abs_of_nonneg (gaussianPDFReal_nonneg _ _ _)]
    exact mul_le_mul_of_nonneg_left (hC _) (gaussianPDFReal_nonneg _ _ _)
  have htop := hbd id (tendsto_gaussianPDFReal_atTop d hs)
  have hbot := hbd Neg.neg (tendsto_gaussianPDFReal_neg_atTop d hs)
  have hlim := intervalIntegral_tendsto_integral hgi Filter.tendsto_neg_atTop_atBot Filter.tendsto_id
  simp only [hftc] at hlim
  have hz : (∫ y, g y) = 0 := by
    simpa only [id_eq,sub_zero] using tendsto_nhds_unique hlim (htop.sub hbot)
  dsimp [g] at hz
  rw [integral_sub hpi (hxi.div_const _),integral_div] at hz
  rw [integral_gaussianReal_eq_integral_smul hs.ne',integral_gaussianReal_eq_integral_smul hs.ne']
  simp only [smul_eq_mul]
  have hh : (∫ y, p y*((y-d)*f y))/(s:ℝ) = ∫ y, p y*deriv f y := by linarith
  have hm := (div_eq_iff (ne_of_gt (show (0:ℝ) < s from hs))).mp hh
  dsimp [p] at hm
  nlinarith only [hm]

end SKRatioGaussian

end
end
end

end OAI

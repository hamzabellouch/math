import Mathlib
import OAI.Probability.SKSupport.Foundations.AdaptedIndepIncrement
import OAI.Probability.SKSupport.Moments.NormalThirdMoment
import OAI.Probability.SKSupport.Foundations.IntegrableCompBoundedDeriv

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK.WeakIto
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

lemma expected_brownian_step (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (s h : ℝ≥0) {Y : Ω → ℝ}
    (hY : Measurable[Filtration.natural B (fun t => (hm t).stronglyMeasurable) s] Y)
    (hYi : Integrable Y P) {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    (C₁ C₂ C₃ : ℝ≥0) (hC₁ : ∀ x, |deriv f x| ≤ C₁)
    (hC₂ : ∀ x, |deriv (deriv f) x| ≤ C₂)
    (hC₃ : ∀ x, |iteratedDeriv 3 f x| ≤ C₃) :
    |(∫ ω, f (Y ω + (B (s+h) ω - B s ω)) ∂P) -
      (∫ ω, f (Y ω) ∂P) -
      (h:ℝ)/2 * (∫ ω, deriv (deriv f) (Y ω) ∂P)| ≤
      (C₃:ℝ)/6 * ((h:ℝ)*Real.sqrt (h:ℝ)*normalThirdMoment) := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  have hYm := hY.mono
    ((Filtration.natural B (fun t => (hm t).stronglyMeasurable)).le s) le_rfl
  have hd : Integrable (fun ω => B (s+h) ω - B s ω) P :=
    (hB.integrable_eval _).sub (hB.integrable_eval _)
  have m2 := hB.isGaussianProcess.hasGaussianLaw_sub (s := s+h) (t := s) |>.memLp_two
  have hd2 : Integrable (fun ω => (B (s+h) ω - B s ω)^2) P := by
    simpa only [Pi.sub_apply] using m2.integrable_sq
  have hd3 : Integrable (fun ω => |B (s+h) ω - B s ω|^3) P := by
    have hh := hB.isGaussianProcess.hasGaussianLaw_sub (s := s+h) (t := s) |>.memLp
      (p := (3 : ℝ≥0∞)) (by norm_num)
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using hh.integrable_norm_pow (by norm_num : 3 ≠ 0)
  have hf₁ : ContDiff ℝ 2 (deriv f) := hf.deriv'
  have hf₂ : ContDiff ℝ 1 (deriv (deriv f)) := hf₁.deriv'
  have hm₁ : AEStronglyMeasurable (fun ω => deriv f (Y ω)) P :=
    (hf₁.continuous.measurable.comp hYm).aestronglyMeasurable
  have hm₂ : AEStronglyMeasurable (fun ω => deriv (deriv f) (Y ω)) P :=
    (hf₂.continuous.measurable.comp hYm).aestronglyMeasurable
  have hi₀ := integrable_comp_of_bounded_deriv (hf.differentiable (by norm_num)) C₁ hC₁ hYi
  have hi₁ : Integrable (fun ω => f (Y ω + (B (s+h) ω - B s ω))) P := by
    simpa only [Pi.add_apply] using integrable_comp_of_bounded_deriv
      (hf.differentiable (by norm_num)) C₁ hC₁ (hYi.add hd)
  have hiL := hd.bdd_mul hm₁ (Filter.Eventually.of_forall (fun ω => by
    simpa only [Real.norm_eq_abs] using hC₁ (Y ω)))
  have hiQ := hd2.bdd_mul hm₂ (Filter.Eventually.of_forall (fun ω => by
    simpa only [Real.norm_eq_abs] using hC₂ (Y ω)))
  have hLin := integral_adapted_mul_increment hB hm s h (hf₁.continuous.measurable.comp hY)
  have hQuad := integral_adapted_mul_increment_sq hB hm s h (hf₂.continuous.measurable.comp hY)
  simp only [Function.comp_apply] at hLin hQuad
  have hiD : Integrable (fun ω => f (Y ω + (B (s+h) ω - B s ω)) - f (Y ω)) P := hi₁.sub hi₀
  have hiDL : Integrable (fun ω => f (Y ω + (B (s+h) ω - B s ω)) - f (Y ω) -
      deriv f (Y ω) * (B (s+h) ω - B s ω)) P := hiD.sub hiL
  let R (ω : Ω) := f (Y ω + (B (s+h) ω - B s ω)) - f (Y ω) -
    deriv f (Y ω) * (B (s+h) ω - B s ω) -
    (1/2:ℝ) * (deriv (deriv f) (Y ω) * (B (s+h) ω - B s ω)^2)
  have hiR : Integrable R P := ((hi₁.sub hi₀).sub hiL).sub (hiQ.const_mul (1/2:ℝ))
  have hR : (∫ ω, R ω ∂P) = (∫ ω, f (Y ω + (B (s+h) ω - B s ω)) ∂P) -
      (∫ ω, f (Y ω) ∂P) - (h:ℝ)/2 * ∫ ω, deriv (deriv f) (Y ω) ∂P := by
    dsimp only [R]
    rw [integral_sub hiDL (hiQ.const_mul (1/2:ℝ)),
      integral_sub hiD hiL, integral_sub hi₁ hi₀, integral_const_mul,
      hLin, hQuad]
    ring
  rw [← hR]
  calc
    _ ≤ ∫ ω, |R ω| ∂P := abs_integral_le_integral_abs
    _ ≤ ∫ ω, (C₃:ℝ)/6 * |B (s+h) ω - B s ω|^3 ∂P := by
      apply integral_mono hiR.abs (hd3.const_mul _)
      intro ω
      dsimp only [R]
      simpa only [mul_assoc] using taylor2_bound hf hC₃ (Y ω) (B (s+h) ω - B s ω)
    _ = _ := by rw [integral_const_mul, increment_abs_cube hB s h]

end ZeroTemperatureSK.WeakIto

namespace ZeroTemperatureSK.WeakIto

lemma drift_perturbation_bound {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (C : ℝ≥0) (hC : ∀ x, |deriv (deriv f) x| ≤ C) (x d a : ℝ) :
    |f (x+d+a) - f (x+d) - deriv f x*a| ≤ (C:ℝ)*(|d|+|a|)*|a| := by
  have hfd : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have hl : LipschitzWith C (deriv f) := lipschitzWith_of_nnnorm_deriv_le
    (hfd.differentiable (by norm_num))
    (fun z => show ‖deriv (deriv f) z‖₊ ≤ C from by exact_mod_cast hC z)
  let g : ℝ → ℝ := fun z => f z - deriv f x*z
  have hgd (z : ℝ) : HasDerivAt g (deriv f z-deriv f x) z := by
    have h1 : HasDerivAt f (deriv f z) z := (hf.differentiable (by norm_num) z).hasDerivAt
    have h2 : HasDerivAt (fun t : ℝ => deriv f x*t) (deriv f x) z := by
      simpa using (hasDerivAt_id z).const_mul (deriv f x)
    exact h1.sub h2
  have hb (z : ℝ) (hz : z ∈ Set.uIcc (x+d) (x+d+a)) :
      ‖deriv f z - deriv f x‖ ≤ (C:ℝ)*(|d|+|a|) := by
    have hh := abs_sub_left_of_mem_uIcc hz
    rw [add_sub_cancel_left] at hh
    have hh' : |z-x| ≤ |d|+|a| := by
      have := abs_add_le (z-(x+d)) d
      have he : z-(x+d)+d = z-x := by ring
      rw [he] at this
      linarith
    have hg := hl.norm_sub_le z x
    simp only [Real.norm_eq_abs] at hg ⊢
    exact hg.trans (mul_le_mul_of_nonneg_left hh' C.coe_nonneg)
  have hmv := (convex_uIcc (x+d) (x+d+a)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z _ => (hgd z).hasDerivWithinAt) hb left_mem_uIcc right_mem_uIcc
  simp only [g, Real.norm_eq_abs, add_sub_cancel_left] at hmv
  convert hmv using 1
  congr 1
  ring

end ZeroTemperatureSK.WeakIto

end
end
end

end OAI

import Mathlib
import OAI.Probability.SKSupport.Diffusion.ExpectedBrownianStep

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace ZeroTemperatureSK.WeakIto

def normalFirstMoment : ℝ := ∫ x : ℝ, |x| ∂gaussianReal 0 1

lemma normalFirstMoment_nonneg : 0 ≤ normalFirstMoment := integral_nonneg abs_nonneg

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

lemma increment_abs_first (hB : IsPreBrownianReal B P) (s h : ℝ≥0) :
    (∫ ω, |B (s+h) ω - B s ω| ∂P) = Real.sqrt (h:ℝ)*normalFirstMoment := by
  have he := (hB.hasLaw_sub (s+h) s).integral_comp
    (f := abs) continuous_abs.measurable.aestronglyMeasurable
  change (∫ ω, |B (s+h) ω - B s ω| ∂P) = _ at he
  rw [he]
  have hh := gaussian_abs_pow 1 (nndist ((s+h:ℝ≥0):ℝ) (s:ℝ))
  simp only [pow_one] at hh
  change (∫ x : ℝ, |x| ∂gaussianReal 0 (nndist ((s+h:ℝ≥0):ℝ) (s:ℝ))) = _
  rw [hh]
  change Real.sqrt ((nndist ((s+h:ℝ≥0):ℝ) (s:ℝ):ℝ≥0):ℝ) * normalFirstMoment = _
  rw [coe_nndist, Real.dist_eq]
  rw [NNReal.coe_add, add_sub_cancel_left, abs_of_nonneg h.coe_nonneg]

lemma expected_control_step (hB : IsPreBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (s h : ℝ≥0) {Y A : Ω → ℝ}
    (hY : Measurable[Filtration.natural B (fun t => (hm t).stronglyMeasurable) s] Y)
    (hYi : Integrable Y P) (hA : Measurable A) (M : ℝ≥0)
    (hAb : ∀ ω, |A ω| ≤ (M:ℝ)*(h:ℝ)) {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    (C₁ C₂ C₃ : ℝ≥0) (hC₁ : ∀ x, |deriv f x| ≤ C₁)
    (hC₂ : ∀ x, |deriv (deriv f) x| ≤ C₂)
    (hC₃ : ∀ x, |iteratedDeriv 3 f x| ≤ C₃) :
    |(∫ ω, f (Y ω + (B (s+h) ω - B s ω) + A ω) ∂P) -
      (∫ ω, f (Y ω) ∂P) - (∫ ω, deriv f (Y ω) * A ω ∂P) -
      (h:ℝ)/2 * (∫ ω, deriv (deriv f) (Y ω) ∂P)| ≤
      (C₃:ℝ)/6 * ((h:ℝ)*Real.sqrt (h:ℝ)*normalThirdMoment) +
      (C₂:ℝ)*(M:ℝ)*(h:ℝ) * (Real.sqrt (h:ℝ)*normalFirstMoment + (M:ℝ)*(h:ℝ)) := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  have hYm := hY.mono
    ((Filtration.natural B (fun t => (hm t).stronglyMeasurable)).le s) le_rfl
  have hd : Integrable (fun ω => B (s+h) ω - B s ω) P :=
    (hB.integrable_eval _).sub (hB.integrable_eval _)
  have hAi : Integrable A P := Integrable.of_bound hA.aestronglyMeasurable ((M:ℝ)*(h:ℝ))
    (Filter.Eventually.of_forall (fun ω => by simpa only [Real.norm_eq_abs] using hAb ω))
  have hf₁ : ContDiff ℝ 2 (deriv f) := hf.deriv'
  have hiF : Integrable (fun ω => f (Y ω + (B (s+h) ω - B s ω))) P := by
    simpa only [Pi.add_apply] using integrable_comp_of_bounded_deriv
      (hf.differentiable (by norm_num)) C₁ hC₁ (hYi.add hd)
  have hiFA : Integrable (fun ω => f (Y ω + (B (s+h) ω - B s ω) + A ω)) P := by
    simpa only [Pi.add_apply] using integrable_comp_of_bounded_deriv
      (hf.differentiable (by norm_num)) C₁ hC₁ ((hYi.add hd).add hAi)
  have hiL : Integrable (fun ω => deriv f (Y ω)*A ω) P := hAi.bdd_mul
    (hf₁.continuous.measurable.comp hYm).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ω => by simpa only [Real.norm_eq_abs] using hC₁ (Y ω)))
  let R (ω : Ω) := f (Y ω + (B (s+h) ω - B s ω) + A ω) -
    f (Y ω + (B (s+h) ω - B s ω)) - deriv f (Y ω)*A ω
  have hiD : Integrable (fun ω => f (Y ω + (B (s+h) ω - B s ω) + A ω) -
    f (Y ω + (B (s+h) ω - B s ω))) P := hiFA.sub hiF
  have hiR : Integrable R P := hiD.sub hiL
  have hR : (∫ ω, R ω ∂P) =
      (∫ ω, f (Y ω + (B (s+h) ω - B s ω) + A ω) ∂P) -
      (∫ ω, f (Y ω + (B (s+h) ω - B s ω)) ∂P) -
      (∫ ω, deriv f (Y ω)*A ω ∂P) := by
    dsimp only [R]
    rw [integral_sub hiD hiL, integral_sub hiFA hiF]
  have hRb : |∫ ω, R ω ∂P| ≤ (C₂:ℝ)*(M:ℝ)*(h:ℝ) *
      (Real.sqrt (h:ℝ)*normalFirstMoment + (M:ℝ)*(h:ℝ)) := by
    calc
      _ ≤ ∫ ω, |R ω| ∂P := abs_integral_le_integral_abs
      _ ≤ ∫ ω, (C₂:ℝ)*(M:ℝ)*(h:ℝ) * (|B (s+h) ω - B s ω| + (M:ℝ)*(h:ℝ)) ∂P := by
        apply integral_mono hiR.abs ((hd.abs.add (integrable_const _)).const_mul _)
        intro ω
        have hb := drift_perturbation_bound (hf.of_le (by norm_num)) C₂ hC₂
          (Y ω) (B (s+h) ω - B s ω) (A ω)
        change |R ω| ≤ _
        apply hb.trans
        have h₁ := mul_le_mul_of_nonneg_left (add_le_add_left (hAb ω)
          |B (s+h) ω - B s ω|) C₂.coe_nonneg
        have h₂ := mul_le_mul h₁ (hAb ω) (abs_nonneg (A ω))
          (mul_nonneg C₂.coe_nonneg (by positivity))
        convert h₂ using 1 <;> (try dsimp only [Pi.add_apply]) <;> ring
      _ = _ := by
        rw [integral_const_mul, integral_add hd.abs (integrable_const _),
          increment_abs_first hB s h]
        simp
  rw [hR] at hRb
  have hG := expected_brownian_step hB hm s h hY hYi hf C₁ C₂ C₃ hC₁ hC₂ hC₃
  have htri := abs_add_le
    ((∫ ω, f (Y ω + (B (s+h) ω - B s ω)) ∂P) - (∫ ω, f (Y ω) ∂P) -
      (h:ℝ)/2 * (∫ ω, deriv (deriv f) (Y ω) ∂P))
    ((∫ ω, f (Y ω + (B (s+h) ω - B s ω) + A ω) ∂P) -
      (∫ ω, f (Y ω + (B (s+h) ω - B s ω)) ∂P) -
      (∫ ω, deriv f (Y ω)*A ω ∂P))
  calc
    _ = |((∫ ω, f (Y ω + (B (s+h) ω - B s ω)) ∂P) - (∫ ω, f (Y ω) ∂P) -
      (h:ℝ)/2 * (∫ ω, deriv (deriv f) (Y ω) ∂P)) +
    ((∫ ω, f (Y ω + (B (s+h) ω - B s ω) + A ω) ∂P) -
      (∫ ω, f (Y ω + (B (s+h) ω - B s ω)) ∂P) -
      (∫ ω, deriv f (Y ω)*A ω ∂P))| := by congr 1; ring
    _ ≤ _ := htri.trans (add_le_add hG hRb)

end ZeroTemperatureSK.WeakIto

end
end
end

end OAI

import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.CappedBilinearError
import OAI.Analysis.RieszRectifiability.Limits.CappedWeakConvergence

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology
open scoped NNReal

theorem fractionalBilinear_test_sub {d : ℕ} (m : ℕ) (w φ η : Ambient d → ℝ)
    (c : ℝ) (x y : Ambient d) :
    fractionalBilinear m w (fun z => φ z - c * η z) x y =
      fractionalBilinear m w φ x y - c * fractionalBilinear m w η x y := by
  unfold fractionalBilinear
  ring

theorem fractionalBilinear_integral_test_sub {d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) (w φ η : Ambient d → ℝ) (c : ℝ)
    (hφ : Integrable (fun q : Ambient d × Ambient d => fractionalBilinear m w φ q.1 q.2)
      (μ.prod μ))
    (hη : Integrable (fun q : Ambient d × Ambient d => fractionalBilinear m w η q.1 q.2)
      (μ.prod μ)) :
    (∫ q : Ambient d × Ambient d, fractionalBilinear m w (fun z => φ z - c * η z) q.1 q.2
      ∂μ.prod μ) =
      (∫ q : Ambient d × Ambient d, fractionalBilinear m w φ q.1 q.2 ∂μ.prod μ) -
      c * (∫ q : Ambient d × Ambient d, fractionalBilinear m w η q.1 q.2 ∂μ.prod μ) := by
  simp only [fractionalBilinear_test_sub]
  rw [integral_sub hφ (hη.const_mul c), integral_const_mul]

theorem meanCorrection_singular_tendsto {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : ℕ → FiniteMeasure (Ambient d)) (ν : FiniteMeasure (Ambient d))
    (hweak : Tendsto μ atTop (𝓝 ν))
    (hg : ∀ j, GlobalUpperGrowth (p + 1) C (μ j : Measure (Ambient d)))
    (w : ℕ → Ambient d → ℝ) (hw : ∀ j, Measurable (w j))
    (hwI : ∀ j, Integrable (w j) (μ j : Measure (Ambient d)))
    (henergy : ∀ j, Integrable
      (fun q : Ambient d × Ambient d => fractionalPairEnergy (p + 1) (w j) q.1 q.2)
      ((μ j : Measure (Ambient d)).prod (μ j : Measure (Ambient d))))
    (φ η : Ambient d → ℝ) (Lφ Bφ Lη Bη : ℝ≥0)
    (hφ : LipschitzWith Lφ φ) (hφB : ∀ x, |φ x| ≤ (Bφ : ℝ))
    (hη : LipschitzWith Lη η) (hηB : ∀ x, |η x| ≤ (Bη : ℝ))
    (hmean : (∫ x, φ x ∂(ν : Measure (Ambient d))) = 0)
    (hbump : (∫ x, η x ∂(ν : Measure (Ambient d))) ≠ 0)
    (P Q : ℝ)
    (hP : Tendsto (fun j => ∫ q : Ambient d × Ambient d, fractionalBilinear (p + 1) (w j) φ q.1 q.2
      ∂(μ j : Measure (Ambient d)).prod (μ j : Measure (Ambient d))) atTop (𝓝 P))
    (hQ : Tendsto (fun j => ∫ q : Ambient d × Ambient d, fractionalBilinear (p + 1) (w j) η q.1 q.2
      ∂(μ j : Measure (Ambient d)).prod (μ j : Measure (Ambient d))) atTop (𝓝 Q)) :
    Tendsto (fun j => ∫ q : Ambient d × Ambient d,
      fractionalBilinear (p + 1) (w j) (meanCorrection (μ j : Measure (Ambient d)) φ η) q.1 q.2
      ∂(μ j : Measure (Ambient d)).prod (μ j : Measure (Ambient d))) atTop (𝓝 P) := by
  have hφweak := bounded_continuous_integral_tendsto μ ν hweak φ hφ.continuous Bφ hφB
  rw [hmean] at hφweak
  have hηweak := bounded_continuous_integral_tendsto μ ν hweak η hη.continuous Bη hηB
  have hc := meanCorrection_coefficient_tendsto_zero
    (fun j => (μ j : Measure (Ambient d))) φ η _ hbump hφweak hηweak
  have hlim := hP.sub (hc.mul hQ)
  simp only [zero_mul, sub_zero] at hlim
  have heq : ∀ j, (∫ q : Ambient d × Ambient d,
      fractionalBilinear (p + 1) (w j) (meanCorrection (μ j : Measure (Ambient d)) φ η) q.1 q.2
      ∂(μ j : Measure (Ambient d)).prod (μ j : Measure (Ambient d))) =
      (∫ q : Ambient d × Ambient d, fractionalBilinear (p + 1) (w j) φ q.1 q.2
        ∂(μ j : Measure (Ambient d)).prod (μ j : Measure (Ambient d))) -
      ((∫ x, φ x ∂(μ j : Measure (Ambient d))) / (∫ x, η x ∂(μ j : Measure (Ambient d)))) *
      (∫ q : Ambient d × Ambient d, fractionalBilinear (p + 1) (w j) η q.1 q.2
        ∂(μ j : Measure (Ambient d)).prod (μ j : Measure (Ambient d))) := by
    intro j
    exact fractionalBilinear_integral_test_sub (p + 1) (μ j : Measure (Ambient d))
      (w j) φ η _
      (fractional_bilinear_integrable_and_cap_error p C _ (hg j) (w j) φ (hw j) (hwI j)
        Lφ Bφ hφ hφB (henergy j) 1 (by norm_num)).1
      (fractional_bilinear_integrable_and_cap_error p C _ (hg j) (w j) η (hw j) (hwI j)
        Lη Bη hη hηB (henergy j) 1 (by norm_num)).1
  simpa only [heq] using! hlim

end

end RieszRectifiability

end OAI

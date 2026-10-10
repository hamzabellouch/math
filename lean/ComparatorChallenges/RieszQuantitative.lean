import Mathlib

namespace OAI

namespace RieszRectifiability
noncomputable section
open MeasureTheory Set Metric
open scoped NNReal ENNReal

abbrev Ambient (d : ℕ) := EuclideanSpace ℝ (Fin d)

def AdmissibleRadius {d : ℕ} (μ : Measure (Ambient d)) (r : ℝ) : Prop :=
  0 < r ∧ ENNReal.ofReal r ≤ Metric.ediam μ.support

def kernel {d : ℕ} (n : ℕ) (x y : Ambient d) : Ambient d :=
  (‖x - y‖ ^ (n + 1))⁻¹ • (x - y)

def truncated {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (ε : ℝ) (f : Ambient d → ℝ) (x : Ambient d) : Ambient d :=
  ∫ y in {y | ε < dist x y}, f y • kernel n x y ∂μ

def ADRegularWithConstant {d : ℕ} (n : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) : Prop :=
  1 ≤ C ∧ ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
    ENNReal.ofReal (r ^ n / C) ≤ μ (ball x r) ∧
    μ (ball x r) ≤ ENNReal.ofReal (C * r ^ n)

def RieszL2BoundedWithConstant {d : ℕ} (n : ℕ) (C : ℝ≥0)
    (μ : Measure (Ambient d)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ f : Ambient d → ℝ,
    MemLp f 2 μ → MemLp (truncated n μ ε f) 2 μ ∧
      eLpNorm (truncated n μ ε f) 2 μ ≤ (C : ℝ≥0∞) * eLpNorm f 2 μ

def BallImageConclusion {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (θ : ℝ) (M : ℝ≥0) : Prop :=
  ∀ x ∈ μ.support, ∀ r : ℝ, AdmissibleRadius μ r →
    ∃ g : (ball (0 : Ambient n) r) → Ambient d,
      LipschitzWith M g ∧
      ENNReal.ofReal (θ * r ^ n) ≤ μ (ball x r ∩ range g)

/-- A single mass fraction and Lipschitz bound work for all measures with fixed AD and Riesz bounds. -/
def QuantitativeFullStatement : Prop :=
  ∀ d n : ℕ, 4 ≤ d → 2 ≤ n → n + 2 ≤ d →
    ∀ C_AD : ℝ, 1 ≤ C_AD → ∀ C_R : ℝ≥0,
      ∃ θ : ℝ, 0 < θ ∧ ∃ M : ℝ≥0,
        ∀ μ : Measure (Ambient d), μ.Regular →
          ADRegularWithConstant n C_AD μ →
          RieszL2BoundedWithConstant n C_R μ →
          BallImageConclusion n μ θ M

end
end RieszRectifiability

namespace RieszRectifiability

/-- Class-uniform Lipschitz ball images from fixed AD and hard-truncation L² bounds. -/
theorem quantitative_higher_codimension_riesz_rectifiability : QuantitativeFullStatement := by
  sorry

end RieszRectifiability

end OAI

import OAI.NumberTheory.TwoPoint.Basic
import OAI.NumberTheory.TwoPoint.PretentiousDistance
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace OAI

open Filter

namespace TwoPointCorrelations

/-- Theorem 1.1 (`thm:q-affine`) of the manuscript, through all real
cutoffs, with a single exponent independent of the four affine coefficients. -/
def LiouvilleLogSaving : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ a₁ a₂ b₁ b₂ : ℕ,
    0 < a₁ → 0 < a₂ → a₁ * b₂ ≠ a₂ * b₁ →
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 3 ≤ X →
      ‖affineSum liouville liouville a₁ a₂ b₁ b₂ ⌊X⌋₊‖ ≤
        C * X / Real.rpow (Real.log X) c

/-- Theorem 1.2 (`thm:elliott`): the factors are ordinary multiplicative
functions; either original factor satisfies the growing-height condition. -/
def BinaryCorrectedElliott : Prop :=
  ∀ f₁ f₂ : ℕ → ℂ, Multiplicative f₁ → Multiplicative f₂ →
    OneBounded f₁ → OneBounded f₂ →
    (UniformlyNonpretentious f₁ ∨ UniformlyNonpretentious f₂) →
    ∀ h₁ h₂ : ℕ, h₁ ≠ h₂ →
      Tendsto (fun N : ℕ => correlationSum f₁ f₂ h₁ h₂ N / (N : ℂ)) atTop (nhds 0)

/-- Corollary 1.3 (`cor:affine`), including coefficients sharing prime factors. -/
def AffineCorrectedElliott : Prop :=
  ∀ f₁ f₂ : ℕ → ℂ, Multiplicative f₁ → Multiplicative f₂ →
    OneBounded f₁ → OneBounded f₂ →
    (UniformlyNonpretentious f₁ ∨ UniformlyNonpretentious f₂) →
    ∀ a₁ a₂ b₁ b₂ : ℕ, 0 < a₁ → 0 < a₂ → a₁ * b₂ ≠ a₂ * b₁ →
      Tendsto (fun N : ℕ => affineSum f₁ f₂ a₁ a₂ b₁ b₂ N / (N : ℂ)) atTop (nhds 0)

end TwoPointCorrelations

end OAI

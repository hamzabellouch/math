import Mathlib

namespace OAI

open Set Filter MeasureTheory
open scoped Topology

namespace StrictInverseFirstPower

def disk : Set ℂ := Metric.ball 0 1

def NormalizedUnivalent (f : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ f disk ∧ Set.InjOn f disk ∧ f 0 = 0 ∧ deriv f 0 = 1

def BoundedNormalizedUnivalent (f : ℂ → ℂ) : Prop :=
  NormalizedUnivalent f ∧ ∃ R : ℝ, ∀ z ∈ disk, ‖f z‖ ≤ R

noncomputable def integralMean (p : ℝ) (f : ℂ → ℂ) (r : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ θ in -Real.pi..Real.pi,
    ‖deriv f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ p

noncomputable def growthExponent (p : ℝ) (f : ℂ → ℂ) : EReal :=
  Filter.limsup (fun r : ℝ =>
    ((Real.log (integralMean p f r) / Real.log (1 / (1 - r)) : ℝ) : EReal))
    (𝓝[<] (1 : ℝ))

noncomputable def boundedSpectrum (p : ℝ) : EReal :=
  ⨆ (f : ℂ → ℂ) (_ : BoundedNormalizedUnivalent f), growthExponent p f

noncomputable def kraetzerPrediction (p : ℝ) : EReal :=
  if |p| ≤ 2 then ((p ^ (2 : ℕ) / 4 : ℝ) : EReal)
  else ((|p| - 1 : ℝ) : EReal)

theorem main :
    (∃ ε C : ℝ, 0 < ε ∧ ε < 1 / 4 ∧
      ∀ (f : ℂ → ℂ), NormalizedUnivalent f →
        ∀ r : ℝ, 1 / 2 ≤ r → r < 1 →
          integralMean (-1) f r ≤ C * (1 - r) ^ (-(1 / 4 : ℝ) + ε)) ∧
    boundedSpectrum (-1) < (1 / 4 : EReal) ∧
    (¬ ∀ p : ℝ, boundedSpectrum p = kraetzerPrediction p) := by
  sorry

end StrictInverseFirstPower

end OAI

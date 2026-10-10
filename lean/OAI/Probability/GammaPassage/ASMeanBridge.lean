import OAI.Probability.GammaPassage.MeanLimit
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Algebra.Order.Archimedean.Basic

namespace OAI

namespace GammaFPP
open MeasureTheory Filter Topology PlanarFPP

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Summable deviations at the countable tolerances `1 / (k + 1)` imply
almost-sure convergence to zero. The events need not be measurable. -/
theorem ae_tendsto_zero_of_summable_deviations (X : ℕ → Ω → ℝ)
    (hsum : ∀ k : ℕ,
      (∑' n, P {ω | 1 / ((k : ℝ) + 1) ≤ |X n ω|}) ≠ ⊤) :
    ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 0) := by
  have hall : ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ᶠ n in atTop,
      ω ∉ {ω | 1 / ((k : ℝ) + 1) ≤ |X n ω|} :=
    ae_all_iff.mpr (fun k => ae_eventually_notMem (hsum k))
  filter_upwards [hall] with ω hω
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  filter_upwards [hω k] with n hn
  have hn' : |X n ω| < 1 / ((k : ℝ) + 1) := lt_of_not_ge hn
  simpa only [Real.dist_eq, sub_zero] using hn'.trans hk

/-- Add a convergent deterministic center after Borel--Cantelli. -/
theorem ae_tendsto_of_summable_centered_deviations
    (X : ℕ → Ω → ℝ) (a : ℕ → ℝ) (L : ℝ)
    (ha : Tendsto a atTop (𝓝 L))
    (hsum : ∀ k : ℕ,
      (∑' n, P {ω | 1 / ((k : ℝ) + 1) ≤ |X n ω - a n|}) ≠ ⊤) :
    ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 L) := by
  filter_upwards [ae_tendsto_zero_of_summable_deviations
    (fun n ω => X n ω - a n) hsum] with ω hω
  simpa only [sub_add_cancel, zero_add] using hω.add ha

/-- Summable centered lattice-passage deviations identify the almost-sure
limit with the Fekete limit of the means. -/
theorem GammaEnvironment.ae_lattice_limit_of_summable_deviations
    {τ : Edge → Ω → ℝ} {shape rate : ℝ}
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (z : Vertex)
    (hsum : ∀ k : ℕ, (∑' n : ℕ, P {ω |
      1 / ((k : ℝ) + 1) ≤
        |passageTime (fun e => τ e ω) 0 (n • z) / (n : ℝ) -
          meanPassageSequence P τ z n / (n : ℝ)|}) ≠ ⊤) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ => passageTime (fun e => τ e ω) 0 (n • z) / (n : ℝ))
      atTop (𝓝 (directionalMeanConstant h hs hr z)) :=
  ae_tendsto_of_summable_centered_deviations _ _ _
    (h.meanPassageSequence_tendsto hs hr z) hsum

end GammaFPP

end OAI

import OAI.NumberTheory.EgyptianFractions.ThreePrimeMangoldtBridge
import OAI.NumberTheory.EgyptianFractions.ThreePrimeSingularSeries

namespace OAI
noncomputable section
open Filter

namespace Problem337

/-- The uniform lower bound on the singular series supplies a quadratic main
term. This bridge has an explicit analytic error hypothesis and asserts no
estimate for prime exponential sums. -/
theorem quantitativeThreePrimeLowerBound_of_mangoldt_singular_error
    (A : ℝ) (hA : 0 < A)
    (herror : ∀ᶠ u : ℕ in atTop, Odd u →
      |mangoldtTripleSum u - A * threePrimeSingularSeries u * (u : ℝ) ^ 2| ≤
        (A / 2) * (u : ℝ) ^ 2) :
    QuantitativeThreePrimeLowerBound := by
  apply quantitativeThreePrimeLowerBound_of_mangoldt
  refine ⟨A / 2, by positivity, ?_⟩
  filter_upwards [herror] with u hu
  intro hodd
  have hs := threePrimeSingularSeries_one_le hodd
  have hscale : 0 ≤ A * (u : ℝ) ^ 2 := mul_nonneg hA.le (sq_nonneg _)
  have hmain := mul_le_mul_of_nonneg_right hs hscale
  have hlow := (abs_le.mp (hu hodd)).1
  nlinarith

/-- The classical ternary Mangoldt asymptotic, stated as a proposition to keep
the genuinely unproved analytic input explicit. Its main term is the singular
series times the area of the positive fixed-sum simplex, namely `u²/2`. -/
def TernaryMangoldtAsymptotic : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ u : ℕ in atTop, Odd u →
    |mangoldtTripleSum u - (1 / 2 : ℝ) * threePrimeSingularSeries u * (u : ℝ) ^ 2| ≤
      ε * (u : ℝ) ^ 2

/-- Uniform singular-series positivity, prime-power removal, and unweighting
are all discharged. Only the stated ternary asymptotic remains as an input. -/
theorem quantitativeThreePrimeLowerBound_of_ternary_mangoldt_asymptotic
    (h : TernaryMangoldtAsymptotic) : QuantitativeThreePrimeLowerBound := by
  apply quantitativeThreePrimeLowerBound_of_mangoldt_singular_error (1 / 2) (by norm_num)
  simpa only [show (1 / 2 : ℝ) / 2 = 1 / 4 by norm_num] using h (1 / 4) (by norm_num)

end Problem337

end

end OAI

import OAI.Analysis.StrictMeans.Endpoints

namespace OAI

namespace StrictInverseFirstPower

theorem main :
    (∃ ε C : ℝ, 0 < ε ∧ ε < 1 / 4 ∧
      ∀ (f : ℂ → ℂ), NormalizedUnivalent f →
        ∀ r : ℝ, 1 / 2 ≤ r → r < 1 →
          integralMean (-1) f r ≤ C * (1 - r) ^ (-(1 / 4 : ℝ) + ε)) ∧
    boundedSpectrum (-1) < (1 / 4 : EReal) ∧
    (¬ ∀ p : ℝ, boundedSpectrum p = kraetzerPrediction p) :=
  ⟨uniform_inverse_first_power, bounded_spectrum_strict, kraetzer_identity_false⟩

end StrictInverseFirstPower

end OAI

import OAI.Combinatorics.BalancedRyser.Probability.FiniteCenteredPatternLemmas
import OAI.Combinatorics.BalancedRyser.Probability.PatternMomentTails

namespace OAI

namespace Balanced.PatternSourceTails

universe u

theorem uniform_raw_pattern_tail_of_totalBound
    (P : ℕ → PatternModel.{u}) (K₀ : ∀ q, Finset (P q).Color)
    (hsupport : UniformPatternSupports P)
    (htotal : UniformPatternTotalBound P K₀ (fun _ => 1)) (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ q, N ≤ q → ∀ x : (P q).Sample,
      (P q).measure.real {ω | (q : ℝ) ^ (1 / 100 : ℝ) ≤
        (P q).count ((P q).fixCoordinates (K₀ q) x ω)} ≤ C / (q : ℝ) ^ (r + 1) := by
  exact PatternTails.uniform_count_oneHundredth_tail_of_moments P K₀
    (uniformPatternMoments_of_totalBound P K₀ hsupport htotal) (r + 1) (by omega)

theorem uniform_centered_pattern_tail_of_exposureBounds
    (P : ℕ → PatternModel.{u}) (K₀ : ∀ q, Finset (P q).Color)
    (hsupport : UniformPatternSupports P)
    (htotal : UniformPatternTotalBound P K₀ (fun q => (q : ℝ)))
    (hoverlap : UniformPatternOverlapBound P K₀)
    (s : ℕ) (hs : 0 < s) (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ q, N ≤ q → ∀ x : (P q).Sample,
      (P q).measure.real {ω | η * (q : ℝ) ≤
        |(P q).count ((P q).fixCoordinates (K₀ q) x ω) -
          (P q).fixedExpectation (K₀ q) x (P q).count|} ≤ C / (q : ℝ) ^ s := by
  exact PatternTails.uniform_centered_linear_tail_of_moments P K₀
    (uniformCenteredPatternMoments_of_exposureBounds P K₀ hsupport htotal hoverlap)
    s hs η hη

end Balanced.PatternSourceTails

end OAI

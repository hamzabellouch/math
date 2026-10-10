import OAI.Combinatorics.BalancedRyser.Candidates.CandidateGeneratorPairMoments
import OAI.Combinatorics.BalancedRyser.Incidence.CandidateIncidenceTests

namespace OAI

noncomputable section
open MeasureTheory

namespace Balanced.CandidateIncidenceTests

universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
local instance generatorFamilyMeasurableSpace : MeasurableSpace F := ⊤

theorem generatorPair_raw_moment_le (d e : Direction F) (s : ℕ) :
    (∫ M, (count M (Sum.inr (Sum.inr (Sum.inr (Sum.inl (d,e))))) : ℝ)^s
      ∂(offsetLaw F).toMeasure) ≤
      (32768 * (((s-1)*4 : ℕ) + 3)^4 : ℝ)^s := by
  classical
  by_cases h : d ≠ e
  · simpa only [count, ite_eq_left h, CandidateGeneratorPair.count] using
      CandidateGeneratorPair.count_moment_le ({d,e} : Finset (Direction F))
        (by simp [h]) s
  · by_cases hs : s = 0
    · subst s
      simp
    · simp only [count, ite_eq_right h, Nat.cast_zero, zero_pow hs, integral_zero]
      positivity

end Balanced.CandidateIncidenceTests

end

end OAI

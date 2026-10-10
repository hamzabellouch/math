import OAI.Combinatorics.BalancedRyser.Incidence.CandidateIncidenceCountTransport
import OAI.Combinatorics.BalancedRyser.Incidence.CandidateIncidenceTests

namespace OAI

namespace Balanced.CandidateIncidenceTests

noncomputable section
open MeasureTheory
universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
local instance lineHitFamilyMeasurableSpace : MeasurableSpace F := ⊤

theorem lineHit_raw_moment_le (g : Direction F) (L : Line F) (s : ℕ) :
    (∫ M, (count M (Sum.inr (Sum.inr (Sum.inr (Sum.inr (g,L))))) : ℝ)^s
      ∂(offsetLaw F).toMeasure) ≤
      (32768 * (((s-1)*4 : ℕ) + 1)^4 : ℝ)^s := by
  simpa only [count] using CandidateIncidence.lineHit_successfulTest_moment_le g L s

theorem exists_lineHit_raw_moment_bound (s : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
      ∀ (g : Direction F) (L : Line F),
      (∫ M, (count M (Sum.inr (Sum.inr (Sum.inr (Sum.inr (g,L))))) : ℝ)^s
        ∂(offsetLaw F).toMeasure) ≤ C := by
  refine ⟨(32768 * (((s-1)*4 : ℕ) + 1)^4 : ℝ)^s, by positivity, ?_⟩
  intro F _ _ _ g L
  exact lineHit_raw_moment_le g L s

end
end Balanced.CandidateIncidenceTests

end OAI

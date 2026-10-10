import OAI.Combinatorics.BalancedRyser.Candidates.CandidateGeneratorPairFamily
import OAI.Combinatorics.BalancedRyser.Candidates.CandidatePointFamily
import OAI.Combinatorics.BalancedRyser.Candidates.CandidateTwoLineFamily
import OAI.Combinatorics.BalancedRyser.Incidence.CandidateIncidenceProbability

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace Balanced.CandidateIncidenceTests

universe u
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
local instance smallFamilyMeasurableSpace : MeasurableSpace F := ⊤

def smallMomentConstant (s : ℕ) : ℝ :=
  max ((60000 * (((s-1)*4 : ℕ)+1)^4 : ℝ)^s)
    (max ((40960 * ((((s-1)*6 : ℕ) : ℝ)+3)^4)^s)
      (max ((32768 * (((s-1)*4 : ℕ)+3)^4 : ℝ)^s)
        ((32768 * (((s-1)*4 : ℕ)+1)^4 : ℝ)^s)))

theorem smallMomentConstant_pos (s : ℕ) : 0 < smallMomentConstant s := by
  unfold smallMomentConstant
  exact lt_of_lt_of_le (by positivity) (le_max_left _ _)

theorem small_raw_moment_le (t : Test F) (s : ℕ) :
    (∫ M : MergedPairs F, (count M t : ℝ)^s ∂(offsetLaw F).toMeasure) ≤
      smallMomentConstant s := by
  unfold smallMomentConstant
  rcases t with p | (⟨p,l⟩ | (⟨l,k⟩ | (⟨d,e⟩ | ⟨g,l⟩)))
  · exact (point_raw_moment_le p s).trans (le_max_left _ _)
  · exact (pointLine_raw_moment_le p l s).trans (le_max_left _ _)
  · exact (twoLine_raw_moment_le l k s).trans
      (le_max_of_le_right (le_max_left _ _))
  · exact (generatorPair_raw_moment_le d e s).trans
      (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
  · exact (lineHit_raw_moment_le g l s).trans
      (le_max_of_le_right (le_max_of_le_right (le_max_right _ _)))

theorem small_bad_probability_bound :
    offsetEventProbability (F := F)
      {M | ¬ SmallGood M (Nat.ceil ((Fintype.card F : ℝ) ^ (1 / 100 : ℝ)))} ≤
        15 * smallMomentConstant 500 / Fintype.card F :=
  small_bad_probability_le _ (smallMomentConstant_pos 500).le
    (fun t => small_raw_moment_le t 500)

theorem tendsto_smallGood
    (F : ℕ → Type u) [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop) :
    Tendsto (fun n => offsetEventProbability (F := F n)
      {M | SmallGood M (Nat.ceil ((Fintype.card (F n) : ℝ) ^ (1 / 100 : ℝ)))})
      atTop (𝓝 1) := by
  apply tendsto_smallGood_of_moments F hq
  exact ⟨smallMomentConstant 500, (smallMomentConstant_pos 500).le,
    Eventually.of_forall (fun _ t => small_raw_moment_le t 500)⟩

end Balanced.CandidateIncidenceTests

end

end OAI

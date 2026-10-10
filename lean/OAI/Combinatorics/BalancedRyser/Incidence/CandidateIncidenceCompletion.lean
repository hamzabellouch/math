import OAI.Combinatorics.BalancedRyser.Candidates.CandidateGlobalLineTail
import OAI.Combinatorics.BalancedRyser.Candidates.CandidateGraphProbabilityReduction
import OAI.Combinatorics.BalancedRyser.Incidence.CandidateSmallIncidence

namespace OAI

noncomputable section
open Filter
open scoped Topology

namespace Balanced.CandidateIncidenceTests

universe u

theorem tendsto_globalGood
    (F : ℕ → Type u) [∀ n, Field (F n)] [∀ n, Fintype (F n)]
    [∀ n, DecidableEq (F n)]
    (hq : Tendsto (fun n => Fintype.card (F n)) atTop atTop) :
    Tendsto (fun n => offsetEventProbability (F := F n)
      {M | GlobalGood M 2621441}) atTop (𝓝 1) := by
  simpa only [GlobalGood] using
    CandidateGlobalLine.successfulTest_globalLine_all_probability_tendsto_one F hq

theorem candidateGraphResult_of_size_estimate (c : ℝ) (hc : 0 < c)
    (hsize : ∀ (F : ℕ → Type u) [∀ n, Field (F n)] [∀ n, Fintype (F n)]
      [∀ n, DecidableEq (F n)],
      Tendsto (fun n => Fintype.card (F n)) atTop atTop →
      Tendsto (fun n => offsetEventProbability (F := F n) {M | SizeGood M c})
        atTop (𝓝 1)) : CandidateGraphResult.{u} := by
  refine candidateGraphResult_of_incidence_estimates c 2621441 hc (by norm_num)
    hsize ?_ ?_
  · intro F _ _ _ hq
    exact tendsto_smallGood F hq
  · intro F _ _ _ hq
    exact tendsto_globalGood F hq

end Balanced.CandidateIncidenceTests

end

end OAI

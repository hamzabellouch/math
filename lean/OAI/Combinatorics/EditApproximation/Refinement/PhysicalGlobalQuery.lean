import OAI.Combinatorics.EditApproximation.Probability.FiniteQueryRestriction
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalRefinementDataRequest
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalMedianQuery
import OAI.Combinatorics.EditApproximation.Geometry.LocalSeedSequence
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! The global query body. A seed read at pass zero evaluates the coarse
seed entry; every later pass reads the preceding pass's copy medians.
All warmup and refinement dependencies carry strict physical ranks. -/

namespace EditApproximation



section Program

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero R]
  (source target : List α) (N P F exponent H Q T S copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R → CellGroupDraws M F Q)
  (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
  (initial : PhysicalEntry M J target.length → ℕ)

def physicalGlobalQuery (request : PhysicalTableRequest M J target.length) :
    FiniteQuery {child : PhysicalTableRequest M J target.length //
      child.combinedRank T S < request.combinedRank T S} := by
  let seedRead := globalSeedRead N T S copies multiplier initial request
  by_cases hwarmup : request.index ≤ T
  · exact physicalWarmupRequestQuery source target N P F (factor request.pass)
      request.pass request.copy T S request.index request.node request.state seedRead
  · by_cases hbelow : request.node.1.val < J
    · by_cases hshort : (physicalSourceInterval source.length request.node).hi -
          (physicalSourceInterval source.length request.node).lo ≤ 1
      · exact physicalInitialQuery source target N P F (factor request.pass) seedRead
          (request.node, request.state)
      · have ht : 0 < request.index - T := by omega
        have hrequest : PhysicalTableRequest.refinement request.pass request.copy request.node
            T (request.index - T) request.state = request := by
          have hi : T + (request.index - T) = request.index := by omega
          unfold PhysicalTableRequest.refinement
          rw [hi]
        have program := physicalRefinementDataRequestQuery source target N P F exponent H Q
          tau (refinementFactor (factor request.pass) F) eta kappa delta
          request.pass request.copy T S (request.index - T) ht request.node hbelow
          (group request.pass request.copy ⟨request.node, hbelow⟩ (Fin.ofNat R (request.index - T - 1)))
          (integer request.pass request.copy ⟨request.node, hbelow⟩ (Fin.ofNat R (request.index - T - 1)))
          request.state
        exact FiniteQuery.mapKeys
          (fun child => ⟨child.val, by simpa only [hrequest] using child.property⟩) program
    · exact physicalInitialQuery source target N P F (factor request.pass) seedRead
        (request.node, request.state)

end Program

end EditApproximation

end OAI

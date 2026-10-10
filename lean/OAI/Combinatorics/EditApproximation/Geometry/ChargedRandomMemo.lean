import OAI.Combinatorics.EditApproximation.Geometry.ChargedRandomGlobalQuery
import OAI.Combinatorics.EditApproximation.Refinement.PhysicalRandomValue
import OAI.Combinatorics.EditApproximation.Geometry.SourceRankedProgram
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! The charged evaluator actually caches random source coordinates and
physical entries in one rank-decreasing memo computation. -/

namespace EditApproximation

section Memo

variable {σ α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P F exponent H Q T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (readGroup : ℕ → ℕ → PhysicalInternalNode M J → Fin R → GroupScalarKey M F Q → FiniteQuery σ)
  (readInteger : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
  (initial : PhysicalEntry M J target.length → ℕ)
  (sourceAnswer : σ → ℚ)



 theorem chargedRandomMemoEvaluate_value
    (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R → CellGroupDraws M F Q)
    (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
    (hgroup : ∀ pass copy node time key, (readGroup pass copy node time key).value sourceAnswer =
      groupScalarValue (group pass copy node time) key)
    (honline : ∀ pass copy (node : PhysicalInternalNode M J) time key,
      (readInteger pass copy node time key
        (keyedOnlineSourceRange source target (physicalSourceInterval source.length node.val)
          P exponent H tau (fun i r => (∑ j : Fin T, localRequestValue source target N P F exponent H Q T S
            copies factor multiplier tau eta kappa delta group integer initial (PhysicalTableRequest.warmup
              pass copy (physicalChild node.val node.property i) j.val r)) / T) key)).value sourceAnswer =
        (integer pass copy node time key.1 key.2 : ℚ))
    (bits : ℕ) (encode : Sum σ (ChargedPhysicalRequest M J target.length passes copies T S) → ℕ)
    (hinjective : Function.Injective encode) (hbounded : ∀ key, encode key < 2 ^ bits)
    (request : ChargedPhysicalRequest M J target.length passes copies T S) :
    (chargedRandomMemoEvaluate source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta readGroup readInteger initial sourceAnswer bits encode request).value =
    chargedRequestValue source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta group integer initial request := by
  unfold chargedRandomMemoEvaluate
  exact SourceRanked.memo_value ChargedPhysicalRequest.rank _ sourceAnswer
    (chargedRequestValue source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta group integer initial)
    (chargedRandomGlobalQuery_value source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta readGroup readInteger initial group integer sourceAnswer
      (physicalRandomBoundedQuery_localValue source target N P F exponent H Q T S passes copies factor
        multiplier tau eta kappa delta group integer initial readGroup readInteger sourceAnswer hgroup honline))
    bits encode hinjective hbounded (.inr request)

end Memo

end EditApproximation

end OAI

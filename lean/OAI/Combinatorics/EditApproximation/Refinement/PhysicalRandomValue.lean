import OAI.Combinatorics.EditApproximation.Refinement.PhysicalRandomBoundedQuery
import OAI.Combinatorics.EditApproximation.Geometry.LocalOnlineSourceQuery

namespace OAI

namespace EditApproximation

section Values

variable {σ α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P F exponent H Q T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R → CellGroupDraws M F Q)
  (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
  (initial : PhysicalEntry M J target.length → ℕ)

omit [NeZero M] in
 theorem localRequestValue_onlineRange (pass copy : ℕ) (node : PhysicalInternalNode M J)
    (key : ℕ × TargetInterval target.length) (hb : key.1 ∈ dyadicScales N) :
    keyedOnlineSourceRange source target (physicalSourceInterval source.length node.val) P exponent H tau
      (fun i r => (∑ j : Fin T, localRequestValue source target N P F exponent H Q T S copies
        factor multiplier tau eta kappa delta group integer initial
        (PhysicalTableRequest.warmup pass copy (physicalChild node.val node.property i) j.val r)) / T) key =
    physicalLocalOnlineMass source target
      (localSeedSequence source target N P F exponent H Q T S copies factor multiplier
        tau eta kappa delta group integer initial pass) N P F (factor pass) T exponent H tau
      (node, physicalScaleIndex N key.1 hb, key.2) := by
  have hmass :
      (fun i r => (∑ j : Fin T, localRequestValue source target N P F exponent H Q T S copies
        factor multiplier tau eta kappa delta group integer initial
        (PhysicalTableRequest.warmup pass copy (physicalChild node.val node.property i) j.val r)) / T) =
      physicalLocalChildMass source target
        (localSeedSequence source target N P F exponent H Q T S copies factor multiplier
          tau eta kappa delta group integer initial pass) N P F (factor pass) T node.val node.property := by
    funext i r
    exact localRequestValue_mass source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial pass copy (physicalChild node.val node.property i) r
  unfold keyedOnlineSourceRange physicalLocalOnlineMass physicalLocalOnlineBandG
  rw [physicalScaleIndex_get, hmass]

variable
  (readGroup : ℕ → ℕ → PhysicalInternalNode M J → Fin R → GroupScalarKey M F Q → FiniteQuery σ)
  (readInteger : ℕ → ℕ → PhysicalInternalNode M J → Fin R →
    (ℕ × TargetInterval target.length) → ℕ → FiniteQuery σ)
  (sourceAnswer : σ → ℚ)
  (hgroup : ∀ pass copy node time key, (readGroup pass copy node time key).value sourceAnswer =
    groupScalarValue (group pass copy node time) key)
  (honline : ∀ pass copy (node : PhysicalInternalNode M J) time key,
    (readInteger pass copy node time key
      (keyedOnlineSourceRange source target (physicalSourceInterval source.length node.val)
        P exponent H tau (fun i r => (∑ j : Fin T, localRequestValue source target N P F exponent H Q T S
          copies factor multiplier tau eta kappa delta group integer initial (PhysicalTableRequest.warmup
            pass copy (physicalChild node.val node.property i) j.val r)) / T) key)).value sourceAnswer =
      (integer pass copy node time key.1 key.2 : ℚ))

include hgroup honline in
 theorem physicalRandomBoundedQuery_localValue
    (request : {request : PhysicalTableRequest M J target.length // request.Bounded passes copies T S}) :
    (physicalRandomBoundedQuery source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta readGroup readInteger initial request).value
      (Sum.elim sourceAnswer (fun key => localRequestValue source target N P F exponent H Q T S copies
        factor multiplier tau eta kappa delta group integer initial key.val.val)) =
    localRequestValue source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial request.val := by
  rw [physicalRandomBoundedQuery_value]
  exact (physicalRandomGlobalQuery_compare source target N P F exponent H Q T S copies factor multiplier
    tau eta kappa delta readGroup readInteger initial group integer sourceAnswer
    (localRequestValue source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial) hgroup honline request.val).trans
    (physicalGlobalQuery_value source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial request.val)

end Values

end EditApproximation

end OAI

import OAI.Combinatorics.EditApproximation.Refinement.PhysicalBoundedQuery
import OAI.Combinatorics.EditApproximation.Geometry.ChargedSeedQuery
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! The global lazy program exposes coarse entries as ordinary memo requests.
Warmup uses these explicit seed reads; positive internal refinement uses the
proved finite table query, whose data reads are all earlier table entries. -/

namespace EditApproximation





section Global

variable {α : Type*} [DecidableEq α] {M J R : ℕ} [NeZero R]
  (source target : List α) (N P F exponent H Q T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (group : ℕ → ℕ → PhysicalInternalNode M J → Fin R → CellGroupDraws M F Q)
  (integer : ℕ → ℕ → PhysicalInternalNode M J → Fin R → ℕ → TargetInterval target.length → ℕ)
  (initial : PhysicalEntry M J target.length → ℕ)

def chargedRequestValue : ChargedPhysicalRequest M J target.length passes copies T S → ℚ
  | .inl entry => initial entry
  | .inr request => localRequestValue source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial request.val

theorem chargedSeedQuery_localValue
    (parent : {r : PhysicalTableRequest M J target.length // r.Bounded passes copies T S})
    (q : TargetInterval target.length) :
    (chargedSeedQuery N multiplier parent (parent.val.node, q)).value
      (fun child => chargedRequestValue source target N P F exponent H Q T S passes copies
        factor multiplier tau eta kappa delta group integer initial child.val) =
    (localSeedSequence source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial parent.val.pass (parent.val.node, q) : ℚ) := by
  rw [chargedSeedQuery_value]
  by_cases hp : parent.val.pass = 0
  · rw [ite_eq_left hp, hp]
    rfl
  · rw [ite_eq_right hp]
    simp only [chargedRequestValue, chargedPreviousPass]
    have hprev (copy : Fin copies) : previousPassRequest T S copy.val parent.val q =
        PhysicalTableRequest.refinement (parent.val.pass - 1) copy.val parent.val.node T S q := rfl
    simp only [hprev, localRequestValue_refinement]
    obtain ⟨pass, heq⟩ := Nat.exists_eq_succ_of_ne_zero hp
    simp only [heq, Nat.succ_eq_add_one, Nat.add_sub_cancel, localSeedSequence]

theorem chargedWarmupQuery_value
    (parent : {r : PhysicalTableRequest M J target.length // r.Bounded passes copies T S})
    (hindex : parent.val.index ≤ T) :
    (chargedWarmupQuery source target N P F factor multiplier parent).value
      (fun child => chargedRequestValue source target N P F exponent H Q T S passes copies
        factor multiplier tau eta kappa delta group integer initial child.val) =
    localRequestValue source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial parent.val := by
  have hreq : PhysicalTableRequest.warmup parent.val.pass parent.val.copy parent.val.node
      parent.val.index parent.val.state = parent.val := rfl
  rw [← hreq, localRequestValue_warmup source target N P F exponent H Q T S copies factor multiplier
    tau eta kappa delta group integer initial _ _ _ _ hindex]
  change (chargedWarmupQuery source target N P F factor multiplier parent).value _ = _
  have hseed := chargedSeedQuery_localValue source target N P F exponent H Q T S passes copies
    factor multiplier tau eta kappa delta group integer initial parent
  unfold chargedWarmupQuery
  split_ifs with hz hbelow hshort
  · rw [hz]
    exact physicalInitialQuery_value_local source target N P F _ _ _ _ _ _ hseed
  · rw [physicalLocalWarmup_terminal _ _ _ _ _ _ _ _ _ _ (Or.inr hshort)]
    exact physicalInitialQuery_value_local source target N P F _ _ _ _ _ _ hseed
  · have hi : parent.val.index = (parent.val.index - 1) + 1 := by omega
    conv_rhs => rw [hi]
    apply physicalWarmupStepQuery_value_local source target N P F _ _ _ _ _
      parent.val.node hbelow hshort (parent.val.index - 1) parent.val.state hseed
    intro input
    change localRequestValue source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial
      (PhysicalTableRequest.warmup parent.val.pass parent.val.copy
        (physicalChild parent.val.node hbelow input.1) (parent.val.index - 1) input.2) = _
    exact localRequestValue_warmup source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial _ _ _ _ (by omega) _
  · rw [physicalLocalWarmup_terminal _ _ _ _ _ _ _ _ _ _ (Or.inl hbelow)]
    exact physicalInitialQuery_value_local source target N P F _ _ _ _ _ _ hseed

def chargedGlobalQuery (request : ChargedPhysicalRequest M J target.length passes copies T S) :
    FiniteQuery {child : ChargedPhysicalRequest M J target.length passes copies T S //
      child.rank < request.rank} :=
  match request with
  | .inl entry => .done (initial entry)
  | .inr parent =>
    if parent.val.index ≤ T then chargedWarmupQuery source target N P F factor multiplier parent
    else if parent.val.node.1.val < J then
      if (physicalSourceInterval source.length parent.val.node).hi -
          (physicalSourceInterval source.length parent.val.node).lo ≤ 1 then
        physicalInitialQuery source target N P F (factor parent.val.pass)
          (chargedSeedQuery N multiplier parent) (parent.val.node, parent.val.state)
      else FiniteQuery.mapKeys (fun child =>
        ⟨Sum.inr child.val, ChargedPhysicalRequest.table_rank_lt parent child.val child.property⟩)
        (physicalBoundedQuery source target N P F exponent H Q T S passes copies factor multiplier
          tau eta kappa delta group integer initial parent)
    else physicalInitialQuery source target N P F (factor parent.val.pass)
      (chargedSeedQuery N multiplier parent) (parent.val.node, parent.val.state)


theorem localRequestValue_terminal (request : PhysicalTableRequest M J target.length)
    (hterminal : ¬ request.node.1.val < J ∨
      (physicalSourceInterval source.length request.node).hi -
        (physicalSourceInterval source.length request.node).lo ≤ 1) :
    localRequestValue source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial request =
    stageInitial source target
      (localSeedSequence source target N P F exponent H Q T S copies factor multiplier
        tau eta kappa delta group integer initial request.pass)
      N P F (factor request.pass) (request.node, request.state) := by
  unfold localRequestValue unifiedPhysicalValue
  dsimp only
  split_ifs
  · exact physicalLocalWarmup_terminal _ _ _ _ _ _ _ _ _ _ hterminal
  · rw [physicalLocalRefinement]
    rcases hterminal with hd | hw
    · rw [dite_eq_right hd]
    · split_ifs <;> rfl

theorem chargedGlobalQuery_value (request : ChargedPhysicalRequest M J target.length passes copies T S) :
    (chargedGlobalQuery source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta group integer initial request).value
      (fun child => chargedRequestValue source target N P F exponent H Q T S passes copies
        factor multiplier tau eta kappa delta group integer initial child.val) =
    chargedRequestValue source target N P F exponent H Q T S passes copies
      factor multiplier tau eta kappa delta group integer initial request := by
  cases request with
  | inl entry => rfl
  | inr parent =>
    change _ = localRequestValue source target N P F exponent H Q T S copies factor multiplier
      tau eta kappa delta group integer initial parent.val
    unfold chargedGlobalQuery
    dsimp only
    split_ifs with hi hd hw
    · exact chargedWarmupQuery_value source target N P F exponent H Q T S passes copies
        factor multiplier tau eta kappa delta group integer initial parent hi
    · rw [localRequestValue_terminal source target N P F exponent H Q T S copies factor multiplier
        tau eta kappa delta group integer initial parent.val (Or.inr hw)]
      exact physicalInitialQuery_value_local source target N P F _ _ _ _ _ _
        (chargedSeedQuery_localValue source target N P F exponent H Q T S passes copies
          factor multiplier tau eta kappa delta group integer initial parent)
    · rw [FiniteQuery.mapKeys_value]
      exact physicalBoundedQuery_value source target N P F exponent H Q T S passes copies
        factor multiplier tau eta kappa delta group integer initial parent
    · rw [localRequestValue_terminal source target N P F exponent H Q T S copies factor multiplier
        tau eta kappa delta group integer initial parent.val (Or.inl hd)]
      exact physicalInitialQuery_value_local source target N P F _ _ _ _ _ _
        (chargedSeedQuery_localValue source target N P F exponent H Q T S passes copies
          factor multiplier tau eta kappa delta group integer initial parent)

def chargedMemoEvaluate (request : ChargedPhysicalRequest M J target.length passes copies T S) :=
  rankedMemoEvaluate ChargedPhysicalRequest.rank
    (chargedGlobalQuery source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta group integer initial)
    (ChargedPhysicalRequest.bits M J target.length passes copies T S)
    ChargedPhysicalRequest.code request .empty

theorem chargedMemoEvaluate_value (hM : 1 ≤ M)
    (request : ChargedPhysicalRequest M J target.length passes copies T S) :
    (chargedMemoEvaluate source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta group integer initial request).value =
    chargedRequestValue source target N P F exponent H Q T S passes copies
      factor multiplier tau eta kappa delta group integer initial request := by
  unfold chargedMemoEvaluate
  exact rankedMemoEvaluate_specification ChargedPhysicalRequest.rank
    (chargedGlobalQuery source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta group integer initial)
    (chargedRequestValue source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta group integer initial)
    (chargedGlobalQuery_value source target N P F exponent H Q T S passes copies factor multiplier
      tau eta kappa delta group integer initial)
    _ _ (ChargedPhysicalRequest.code_injective hM) (ChargedPhysicalRequest.code_fits hM) request

end Global

end EditApproximation

end OAI

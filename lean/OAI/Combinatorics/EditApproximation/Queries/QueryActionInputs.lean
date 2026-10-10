import OAI.Combinatorics.EditApproximation.Queries.QueryInputCodes
import OAI.Combinatorics.EditApproximation.Binary.BinaryBellmanKernel
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Once the selected group and online actions have been computed, the
last adaptive gather lists exactly their child coordinates, sorted by
the same injective encoding as the reference query. -/

namespace EditApproximation

theorem query_mem_action_cover {Parent Child : Type*} [DecidableEq Child] {M : ℕ}
    (actions : List (RationalBellmanAction Parent Child M)) (input : Child) :
    input ∈ actionCurrentInputCover actions ↔
      ∃ action ∈ actions, ∃ i, action.childState i = input := by
  constructor
  · intro h
    obtain ⟨index, _, hi⟩ := Finset.mem_biUnion.mp h
    obtain ⟨i, _, heq⟩ := Finset.mem_image.mp hi
    exact ⟨actions.get index, List.get_mem actions index, i, heq⟩
  · rintro ⟨action, ha, i, rfl⟩
    exact actionCurrentInputCover_mem actions action ha i



theorem queryActionInputsWithWork_value {Parent Child : Type*} [DecidableEq Child] {M : ℕ}
    (actions : List (BinaryBellmanAction Parent Child M)) :
    (queryActionInputsWithWork actions).1.toFinset =
      actionCurrentInputCover (actions.map BinaryBellmanAction.decode) := by
  ext input
  simp only [queryActionInputsWithWork, arithmeticFlatMapWithWork_value, arithmeticMapWithWork_value,
    List.mem_toFinset, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and, query_mem_action_cover]
  constructor
  · rintro ⟨action, ha, i, hi⟩
    exact ⟨action.decode, ⟨action, ha, rfl⟩, i, hi⟩
  · rintro ⟨action, ⟨word, hw, rfl⟩, i, hi⟩
    exact ⟨word, hw, i, hi⟩



theorem queryNeededInputsWithWork_value {n M : ℕ}
    (selected online : List (BinaryBellmanAction (TargetInterval n) (Fin M × TargetInterval n) M)) :
    (queryNeededInputsWithWork selected online).1 =
      orderedInputs childInputCode (childInputCode_injective M n)
        (actionCurrentInputCover (selected.map BinaryBellmanAction.decode) ∪
         actionCurrentInputCover (online.map BinaryBellmanAction.decode)) := by
  simp only [queryNeededInputsWithWork, queryOrderedChildInputsWithWork_value,
    List.toFinset_append, queryActionInputsWithWork_value]

end EditApproximation

end OAI

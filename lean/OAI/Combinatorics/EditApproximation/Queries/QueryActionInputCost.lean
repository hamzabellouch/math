import OAI.Combinatorics.EditApproximation.Queries.QueryActionInputs
import OAI.Combinatorics.EditApproximation.Queries.QueryCodeBounds
import OAI.Combinatorics.EditApproximation.Queries.QueryHistoryBounds

namespace OAI

/-! Bounds for the final adaptive child gather.  The temporary list and
its sorting work depend on emitted actions, rather than the full table. -/

namespace EditApproximation

theorem queryActionInputsWithWork_bounds {Parent Child : Type*} {M : ℕ}
    (actions : List (BinaryBellmanAction Parent Child M)) :
    (queryActionInputsWithWork actions).1.length = actions.length * M ∧
    (queryActionInputsWithWork actions).2 ≤ actions.length * (5 * M + 3) + M + 1 := by
  let run := fun action : BinaryBellmanAction Parent Child M =>
    arithmeticMapWithWork (fun i : Fin M => (action.childState i, 1)) (List.finRange M)
  have hlen (action : BinaryBellmanAction Parent Child M) : (run action).1.length = M := by
    simp only [run, arithmeticMapWithWork_value, List.length_map, List.length_finRange]
  have hc (action : BinaryBellmanAction Parent Child M) : (run action).2 ≤ 4 * M := by
    have h := arithmeticMapWithWork_cost (fun i : Fin M => (action.childState i, 1))
      (List.finRange M) 1 (fun _ _ => le_rfl)
    simpa only [List.length_finRange, Nat.reduceAdd, Nat.mul_comm] using h
  constructor
  · simp only [queryActionInputsWithWork, arithmeticFlatMapWithWork_value, List.length_flatMap,
      arithmeticMapWithWork_value, List.length_map, List.length_finRange, List.map_const',
      List.sum_replicate, smul_eq_mul]
  · have h := arithmeticFlatMapWithWork_cost run actions (4 * M) M
      (fun action _ => hc action) (fun action _ => (hlen action).le)
    change (arithmeticFlatMapWithWork run actions).2 + M + 1 ≤ _
    have heq : 4 * M + M + 3 = 5 * M + 3 := by omega
    rw [heq] at h
    omega

theorem queryOrderedChildInputsWithWork_length {M n : ℕ} (inputs : List (Fin M × TargetInterval n)) :
    (queryOrderedChildInputsWithWork inputs).1.length ≤ inputs.length := by
  rw [queryOrderedChildInputsWithWork_value, orderedInputs_length]
  exact List.toFinset_card_le inputs

def queryNeededInputsBitBudget (actions M B : ℕ) : ℕ :=
  actions * (5 * M + 3) + 2 * M + actions * M +
    (actions * M + 1) ^ 2 * (202000 * (B + 1) ^ 2) + 4

theorem queryNeededInputsWithWork_bounds {n M : ℕ}
    (selected online : List (BinaryBellmanAction (TargetInterval n) (Fin M × TargetInterval n) M))
    (B : ℕ) (hM : Nat.size M ≤ B) (hn : Nat.size n ≤ B) :
    (queryNeededInputsWithWork selected online).1.length ≤ (selected.length + online.length) * M ∧
    (queryNeededInputsWithWork selected online).2 ≤
      queryNeededInputsBitBudget (selected.length + online.length) M B := by
  let first := queryActionInputsWithWork selected
  let second := queryActionInputsWithWork online
  have hf := queryActionInputsWithWork_bounds selected
  have hs := queryActionInputsWithWork_bounds online
  have hl : (first.1 ++ second.1).length = (selected.length + online.length) * M := by
    rw [List.length_append, hf.1, hs.1, Nat.add_mul]
  have hsort := queryOrderedChildInputsWithWork_cost (first.1 ++ second.1) B hM hn
  rw [hl] at hsort
  constructor
  · exact (queryOrderedChildInputsWithWork_length (first.1 ++ second.1)).trans_eq hl
  · change first.2 + second.2 + first.1.length +
      (queryOrderedChildInputsWithWork (first.1 ++ second.1)).2 + 2 ≤ _
    have hfc : first.2 ≤ selected.length * (5 * M + 3) + M + 1 := hf.2
    have hsc : second.2 ≤ online.length * (5 * M + 3) + M + 1 := hs.2
    unfold queryNeededInputsBitBudget
    rw [Nat.add_mul]
    have hfl : first.1.length ≤ (selected.length + online.length) * M := by
      rw [hf.1, Nat.add_mul]
      omega
    omega

end EditApproximation

end OAI

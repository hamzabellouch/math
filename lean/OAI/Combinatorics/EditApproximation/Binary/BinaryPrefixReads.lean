import OAI.Combinatorics.EditApproximation.Binary.BinaryPrefixWork
import OAI.Combinatorics.EditApproximation.Binary.BinaryReadComposition
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Prefix predictors retain the costs of the child words they inspect. -/

namespace EditApproximation
namespace BinaryFraction



theorem prefixReadWithWork_eq {nx ny M : ℕ} (parent : TargetInterval nx) (r : TargetInterval ny)
    (states : Fin M → TargetInterval ny) (read : Fin M → TargetInterval ny → BinaryFraction × ℕ)
    (j : ℕ) (p : BinaryFraction) :
    (prefixReadWithWork parent r states read j p).1 =
      (prefixWithWork parent r states (fun i q => (read i q).1) j p).1 := by
  have hw : (arithmeticMapWithWork (fun i : Fin M =>
      if i.val < j then read i (states i) else (zero, 1)) (List.finRange M)).1 =
      List.ofFn (fun i : Fin M => if i.val < j then (read i (states i)).1 else zero) := by
    simp only [arithmeticMapWithWork_value, List.ofFn_eq_map]
    apply List.map_congr_left
    intro i _
    split_ifs <;> rfl
  simp only [prefixReadWithWork, hw, prefixWithWork]

theorem prefixReadWithWork_cost {nx ny M : ℕ} (parent : TargetInterval nx) (r : TargetInterval ny)
    (states : Fin M → TargetInterval ny) (read : Fin M → TargetInterval ny → BinaryFraction × ℕ)
    (j : ℕ) (p : BinaryFraction) (R : ℕ) (hr : ∀ i, (read i (states i)).2 ≤ R) :
    (prefixReadWithWork parent r states read j p).2 ≤
      (prefixWithWork parent r states (fun i q => (read i q).1) j p).2 + M * (R + 4) := by
  let get := fun i : Fin M => if i.val < j then read i (states i) else (zero, 1)
  have h := arithmeticMapWithWork_cost get (List.finRange M) (R + 1) (by
    intro i _
    dsimp only [get]
    split_ifs
    · exact (hr i).trans (Nat.le_succ R)
    · omega)
  have hw : (arithmeticMapWithWork get (List.finRange M)).1 =
      List.ofFn (fun i : Fin M => if i.val < j then (read i (states i)).1 else zero) := by
    simp only [arithmeticMapWithWork_value, List.ofFn_eq_map]
    apply List.map_congr_left
    intro i _
    dsimp only [get]
    split_ifs <;> rfl
  simp only [List.length_finRange, Nat.add_assoc, Nat.reduceAdd] at h
  change (arithmeticMapWithWork get (List.finRange M)).2 + _ + _ + _ + _ + _ + _ + 6 * M + 5 ≤ _
  rw [hw]
  unfold prefixWithWork
  dsimp only
  omega



theorem prefixMinimumReadWithWork_eq {nx ny M : ℕ} (parent : TargetInterval nx) (r : TargetInterval ny)
    (actions : List (Fin M → TargetInterval ny)) (hne : actions ≠ [])
    (read : Fin M → TargetInterval ny → BinaryFraction × ℕ) (j : ℕ) (p : BinaryFraction) :
    (prefixMinimumReadWithWork parent r actions hne read j p).1 =
      (prefixMinimumWithWork parent r actions hne (fun i q => (read i q).1) j p).1 := by
  simp only [prefixMinimumReadWithWork, prefixMinimumWithWork, arithmeticMapWithWork_value,
    prefixReadWithWork_eq]

theorem prefixMinimumReadWithWork_cost {nx ny M : ℕ} (parent : TargetInterval nx) (r : TargetInterval ny)
    (actions : List (Fin M → TargetInterval ny)) (hne : actions ≠ [])
    (read : Fin M → TargetInterval ny → BinaryFraction × ℕ) (j : ℕ) (p : BinaryFraction)
    (R : ℕ) (hr : ∀ action ∈ actions, ∀ i, (read i (action i)).2 ≤ R) :
    (prefixMinimumReadWithWork parent r actions hne read j p).2 ≤
      (prefixMinimumWithWork parent r actions hne (fun i q => (read i q).1) j p).2 +
        (actions.length + 1) * (M * (R + 4)) := by
  have h := arithmeticMapWithWork_extra (fun action => prefixReadWithWork parent r action read j p)
    (fun action => prefixWithWork parent r action (fun i q => (read i q).1) j p)
    (fun _ => M * (R + 4)) actions
    (fun action _ => prefixReadWithWork_eq parent r action read j p)
    (fun action ha => prefixReadWithWork_cost parent r action read j p R (hr action ha))
  have hf := prefixReadWithWork_cost parent r (actions.head hne) read j p R (hr _ (List.head_mem hne))
  have hs : (actions.map (fun _ => M * (R + 4))).sum = actions.length * (M * (R + 4)) := by
    simp only [List.map_const', List.sum_replicate, smul_eq_mul]
  rw [hs] at h
  unfold prefixMinimumReadWithWork prefixMinimumWithWork
  dsimp only
  rw [prefixReadWithWork_eq, h.1]
  simp only [Nat.add_mul, Nat.one_mul]
  omega

end BinaryFraction
end EditApproximation

end OAI

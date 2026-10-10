import OAI.Combinatorics.EditApproximation.Binary.BinaryCutReads
import OAI.Combinatorics.EditApproximation.Binary.BinaryScoreReads
import OAI.Combinatorics.EditApproximation.Binary.BinaryPreparedRepresentative
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Representative bands with charged child-table reads in every score
and prefix predicate over the materialized wide grid. -/

namespace EditApproximation
namespace BinaryFraction



theorem bandFromActionsReadWithWork_eq_cost {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (b : ℕ) (tau theta velocity : BinaryFraction)
    (read : Fin M → TargetInterval ny → BinaryFraction × ℕ)
    (actions : List (Fin M → TargetInterval ny)) (hne : actions ≠ []) (R : ℕ)
    (hr : ∀ action ∈ actions, ∀ i, (read i (action i)).2 ≤ R) :
    (bandFromActionsReadWithWork parent r b tau theta velocity read actions hne).1 =
      (bandFromActionsWithWork parent r b tau theta velocity (fun i q => (read i q).1) actions hne).1 ∧
    (bandFromActionsReadWithWork parent r b tau theta velocity read actions hne).2 ≤
      (bandFromActionsWithWork parent r b tau theta velocity (fun i q => (read i q).1) actions hne).2 +
        actions.length * (M * ((actions.length + 1) * (M * (R + 4)))) := by
  have costBound (a a' m g A : ℕ) (ha : a ≤ a' + A) :
      m + g + a + 2 ≤ m + g + a' + 2 + A := by
    omega
  have h := filterWithWork_extra
    (bandPredicateReadWithWork parent r b tau theta velocity actions hne read)
    (bandPredicateWithWork parent r b tau theta velocity actions hne (fun i q => (read i q).1))
    (fun _ => M * ((actions.length + 1) * (M * (R + 4)))) actions
    (fun states _ => (bandPredicateReadWithWork_eq_cost parent r b tau theta velocity actions hne read states R hr).1)
    (fun states _ => (bandPredicateReadWithWork_eq_cost parent r b tau theta velocity actions hne read states R hr).2)
  simp only [List.map_const', List.sum_replicate, smul_eq_mul] at h
  unfold bandFromActionsReadWithWork bandFromActionsWithWork
  dsimp only
  split_ifs
  · exact ⟨h.1, costBound _ _ _ _ _ h.2⟩
  · exact ⟨rfl, Nat.le_add_right _ _⟩



def representativeReadOverhead (M vertices R : ℕ) : ℕ :=
  (vertices + 1) * (M * (R + 4)) + vertices * (M * ((vertices + 1) * (M * (R + 4))))

theorem representativeFromActionsReadWithWork_eq_cost {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (sourceLength b : ℕ) (tau theta : BinaryFraction)
    (read : Fin M → TargetInterval ny → BinaryFraction × ℕ)
    (actions : List (Fin M → TargetInterval ny)) (R : ℕ)
    (hr : ∀ action ∈ actions, ∀ i, (read i (action i)).2 ≤ R) :
    (representativeFromActionsReadWithWork parent r sourceLength b tau theta read actions).1 =
      (representativeFromActionsWithWork parent r sourceLength b tau theta (fun i q => (read i q).1) actions).1 ∧
    (representativeFromActionsReadWithWork parent r sourceLength b tau theta read actions).2 ≤
      (representativeFromActionsWithWork parent r sourceLength b tau theta (fun i q => (read i q).1) actions).2 +
        representativeReadOverhead M actions.length R := by
  have costBound (a a' c c' x y z A B : ℕ)
      (ha : a ≤ a' + A) (hc : c ≤ c' + B) :
      a + x + y + z + c + 3 ≤ a' + x + y + z + c' + 3 + (A + B) := by
    omega
  have shortCostBound (a a' x A B : ℕ) (ha : a ≤ a' + A) :
      a + x + 2 ≤ a' + x + 2 + (A + B) := by
    omega
  unfold representativeFromActionsReadWithWork representativeFromActionsWithWork
  by_cases hne : actions = []
  · simp only [dite_eq_left hne]
    exact ⟨trivial, Nat.le_add_right _ _⟩
  · simp only [dite_eq_right hne]
    have hz := wideMinimumReadWithWork_cost r read actions hne R hr
    have hmono : (actions.length + 1) * (M * (R + 3)) ≤ (actions.length + 1) * (M * (R + 4)) := by
      exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
        (Nat.add_le_add_left (by decide : 3 ≤ 4) R))
    have hz' := hz.trans (Nat.add_le_add_left hmono _)
    rw [wideMinimumReadWithWork_eq]
    split_ifs
    · have hb := bandFromActionsReadWithWork_eq_cost parent r b tau theta
        (divWithWork (stateGapWithWork sourceLength r).1
          (wideMinimumWithWork r (fun i q => (read i q).1) actions hne).1).1 read actions hne R hr
      refine ⟨hb.1, ?_⟩
      exact costBound _ _ _ _ _ _ _ _ _ hz' hb.2
    · exact ⟨rfl, shortCostBound _ _ _ _ _ hz'⟩



theorem preparedRepresentativeReadWithWork_eq_cost {nx ny M : ℕ} (parent : TargetInterval nx)
    (center : TargetInterval ny) (sourceLength b P : ℕ) (tau theta : BinaryFraction)
    (read : Fin M → TargetInterval ny → BinaryFraction × ℕ) (R : ℕ)
    (hr : ∀ i q, (read i q).2 ≤ R) :
    (preparedRepresentativeReadWithWork parent center sourceLength b P tau theta read).1 =
      (preparedRepresentativeWithWork parent center sourceLength b P tau theta (fun i q => (read i q).1)).1 ∧
    (preparedRepresentativeReadWithWork parent center sourceLength b P tau theta read).2 ≤
      (preparedRepresentativeWithWork parent center sourceLength b P tau theta (fun i q => (read i q).1)).2 +
        representativeReadOverhead M (wideActionGridWithWork M parent center b P).1.length R := by
  have h := representativeFromActionsReadWithWork_eq_cost parent center sourceLength b tau theta read
    ((wideActionGridWithWork M parent center b P).1.map Vector.get) R (fun _ _ i => hr i _)
  simp only [List.length_map] at h
  unfold preparedRepresentativeReadWithWork preparedRepresentativeWithWork
  dsimp only
  exact ⟨h.1, by omega⟩

end BinaryFraction
end EditApproximation

end OAI

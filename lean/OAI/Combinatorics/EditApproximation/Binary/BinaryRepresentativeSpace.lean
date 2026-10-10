import OAI.Combinatorics.EditApproximation.Binary.BinaryBandSpace
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation.BinaryFraction



theorem bandFromActionsReadAllocation_le_work {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (b : ℕ) (tau theta velocity : BinaryFraction)
    (read : Fin M → TargetInterval ny → BinaryFraction × ℕ)
    (allocation : Fin M → TargetInterval ny → ℕ)
    (actions : List (Fin M → TargetInterval ny)) (hne : actions ≠ [])
    (h : ∀ action ∈ actions, ∀ i, allocation i (action i) ≤ (read i (action i)).2) :
    bandFromActionsReadAllocation parent r b tau theta velocity read allocation actions hne ≤
      (bandFromActionsReadWithWork parent r b tau theta velocity read actions hne).2 := by
  have hm := subAllocation_le_work one tau
  have hg := leAllocation_le_work velocity.absolute (subWithWork one tau).1
  have hf := filterAllocation_le_work
    (bandPredicateReadWithWork parent r b tau theta velocity actions hne read)
    (bandPredicateReadAllocation parent r b tau theta velocity actions hne read allocation) actions
    (fun action _ => bandPredicateReadAllocation_le_work parent r b tau theta velocity actions hne read allocation action h)
  unfold bandFromActionsReadAllocation bandFromActionsReadWithWork
  dsimp only
  split_ifs <;> dsimp only
  · exact (Nat.add_le_add (Nat.add_le_add hm hg) hf).trans (Nat.le_add_right _ 2)
  · exact Nat.add_le_add (Nat.add_le_add hm hg) (Nat.zero_le 1)



theorem representativeFromActionsReadAllocation_le_work {nx ny M : ℕ} (parent : TargetInterval nx)
    (r : TargetInterval ny) (sourceLength b : ℕ) (tau theta : BinaryFraction)
    (read : Fin M → TargetInterval ny → BinaryFraction × ℕ)
    (allocation : Fin M → TargetInterval ny → ℕ)
    (actions : List (Fin M → TargetInterval ny))
    (h : ∀ action ∈ actions, ∀ i, allocation i (action i) ≤ (read i (action i)).2) :
    representativeFromActionsReadAllocation parent r sourceLength b tau theta read allocation actions ≤
      (representativeFromActionsReadWithWork parent r sourceLength b tau theta read actions).2 := by
  have costBound (z z' p p' g g' d d' b b' : ℕ)
      (hz : z ≤ z') (hp : p ≤ p') (hg : g ≤ g') (hd : d ≤ d') (hb : b ≤ b') :
      z + p + (g + d + b) ≤ z' + p' + g' + d' + b' + 3 := by
    omega
  unfold representativeFromActionsReadAllocation representativeFromActionsReadWithWork
  by_cases hne : actions = []
  · simp only [hne, ↓reduceDIte, Nat.zero_le]
  · simp only [hne, ↓reduceDIte]
    have hz := wideMinimumReadAllocation_le_work r read allocation actions hne h
    have hp := ltAllocation_le_work zero (wideMinimumReadWithWork r read actions hne).1
    have hg := stateGapAllocation_le_work sourceLength r
    have hd := divAllocation_le_work (stateGapWithWork sourceLength r).1
      (wideMinimumReadWithWork r read actions hne).1
    have hb := bandFromActionsReadAllocation_le_work parent r b tau theta
      (divWithWork (stateGapWithWork sourceLength r).1 (wideMinimumReadWithWork r read actions hne).1).1
      read allocation actions hne h
    split_ifs <;> dsimp only
    · exact costBound _ _ _ _ _ _ _ _ _ _ hz hp hg hd hb
    · exact Nat.add_le_add (Nat.add_le_add hz hp) (by decide : 0 ≤ 2)



theorem preparedRepresentativeReadAllocation_le_work {nx ny M : ℕ} (parent : TargetInterval nx)
    (center : TargetInterval ny) (sourceLength b P : ℕ) (tau theta : BinaryFraction)
    (read : Fin M → TargetInterval ny → BinaryFraction × ℕ)
    (allocation : Fin M → TargetInterval ny → ℕ)
    (h : ∀ i q, allocation i q ≤ (read i q).2) :
    preparedRepresentativeReadAllocation parent center sourceLength b P tau theta read allocation ≤
      (preparedRepresentativeReadWithWork parent center sourceLength b P tau theta read).2 := by
  have hw := wideActionGridAllocation_le_work M parent center b P
  have hr := representativeFromActionsReadAllocation_le_work parent center sourceLength b tau theta read allocation
    ((wideActionGridWithWork M parent center b P).1.map Vector.get) (fun _ _ i => h i _)
  unfold preparedRepresentativeReadAllocation preparedRepresentativeReadWithWork
  dsimp only
  omega

end EditApproximation.BinaryFraction

end OAI

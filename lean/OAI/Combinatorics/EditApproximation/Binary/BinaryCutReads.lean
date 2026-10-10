import OAI.Combinatorics.EditApproximation.Binary.BinaryPrefixReads
import OAI.Combinatorics.EditApproximation.Binary.BinaryBandGuardWork
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

/-! Literal cut predicates and all-cut loops with costed child readers. -/

namespace EditApproximation

theorem allWithWork_extra {α : Type*} (read plain : α → Bool × ℕ) (extra : α → ℕ)
    (xs : List α) (hv : ∀ x ∈ xs, (read x).1 = (plain x).1)
    (hc : ∀ x ∈ xs, (read x).2 ≤ (plain x).2 + extra x) :
    (allWithWork read xs).1 = (allWithWork plain xs).1 ∧
      (allWithWork read xs).2 ≤ (allWithWork plain xs).2 + (xs.map extra).sum := by
  have costBound (a a' b b' A B : ℕ) (ha : a ≤ a' + A) (hb : b ≤ b' + B) :
      a + b + 3 ≤ a' + b' + 3 + (A + B) := by
    omega
  induction xs with
  | nil => exact ⟨rfl, Nat.le_refl _⟩
  | cons x xs ih =>
    have hh := hv x List.mem_cons_self
    have hhCost := hc x List.mem_cons_self
    have ht := ih (fun y hy => hv y (List.mem_cons_of_mem _ hy))
      (fun y hy => hc y (List.mem_cons_of_mem _ hy))
    constructor
    · change ((read x).1 && (allWithWork read xs).1) =
        ((plain x).1 && (allWithWork plain xs).1)
      rw [hh, ht.1]
    · change (read x).2 + (allWithWork read xs).2 + 3 ≤
        (plain x).2 + (allWithWork plain xs).2 + 3 + (extra x + (xs.map extra).sum)
      exact costBound _ _ _ _ _ _ hhCost ht.2

namespace BinaryFraction



theorem cutGuardReadWithWork_eq {nx ny M : ℕ} (parent : TargetInterval nx) (r : TargetInterval ny)
    (actions : List (Fin M → TargetInterval ny)) (hne : actions ≠ [])
    (read : Fin M → TargetInterval ny → BinaryFraction × ℕ) (states : Fin M → TargetInterval ny)
    (velocity tolerance : BinaryFraction) (j : Fin M) :
    (cutGuardReadWithWork parent r actions hne read states velocity tolerance j).1 =
      (cutGuardWithWork parent r actions hne (fun i q => (read i q).1) states velocity tolerance j).1 := by
  simp only [cutGuardReadWithWork, cutGuardWithWork]
  split_ifs
  · rfl
  · simp only [prefixMinimumReadWithWork_eq]

theorem cutGuardReadWithWork_cost {nx ny M : ℕ} (parent : TargetInterval nx) (r : TargetInterval ny)
    (actions : List (Fin M → TargetInterval ny)) (hne : actions ≠ [])
    (read : Fin M → TargetInterval ny → BinaryFraction × ℕ) (states : Fin M → TargetInterval ny)
    (velocity tolerance : BinaryFraction) (j : Fin M) (R : ℕ)
    (hr : ∀ action ∈ actions, ∀ i, (read i (action i)).2 ≤ R) :
    (cutGuardReadWithWork parent r actions hne read states velocity tolerance j).2 ≤
      (cutGuardWithWork parent r actions hne (fun i q => (read i q).1) states velocity tolerance j).2 +
        (actions.length + 1) * (M * (R + 4)) := by
  have costBound (s o p p' v u w x y A : ℕ) (hp : p ≤ p' + A) :
      s + o + p + v + u + w + x + y + 5 ≤ s + o + p' + v + u + w + x + y + 5 + A := by
    omega
  unfold cutGuardReadWithWork cutGuardWithWork
  split_ifs
  · exact Nat.le_add_right _ _
  · have h := prefixMinimumReadWithWork_cost parent r actions hne read j.val
      (subWithWork (nat (states j).lo) (nat (sourceChild parent j).lo)).1 R hr
    dsimp only
    rw [prefixMinimumReadWithWork_eq]
    exact costBound _ _ _ _ _ _ _ _ _ _ h



theorem bandPredicateReadWithWork_eq_cost {nx ny M : ℕ}
    (parent : TargetInterval nx) (r : TargetInterval ny) (b : ℕ) (tau theta velocity : BinaryFraction)
    (actions : List (Fin M → TargetInterval ny)) (hne : actions ≠ [])
    (read : Fin M → TargetInterval ny → BinaryFraction × ℕ) (states : Fin M → TargetInterval ny)
    (R : ℕ) (hr : ∀ action ∈ actions, ∀ i, (read i (action i)).2 ≤ R) :
    (bandPredicateReadWithWork parent r b tau theta velocity actions hne read states).1 =
      (bandPredicateWithWork parent r b tau theta velocity actions hne
        (fun i q => (read i q).1) states).1 ∧
    (bandPredicateReadWithWork parent r b tau theta velocity actions hne read states).2 ≤
      (bandPredicateWithWork parent r b tau theta velocity actions hne
        (fun i q => (read i q).1) states).2 + M * ((actions.length + 1) * (M * (R + 4))) := by
  have costBound (c a t k k' A : ℕ) (hk : k ≤ k' + A) :
      c + a + t + k + 4 ≤ c + a + t + k' + 4 + A := by
    omega
  have h := allWithWork_extra
    (cutGuardReadWithWork parent r actions hne read states velocity (bandToleranceWithWork tau theta b M).1)
    (cutGuardWithWork parent r actions hne (fun i q => (read i q).1) states velocity
      (bandToleranceWithWork tau theta b M).1)
    (fun _ => (actions.length + 1) * (M * (R + 4))) (List.finRange M)
    (fun i _ => cutGuardReadWithWork_eq parent r actions hne read states velocity _ i)
    (fun i _ => cutGuardReadWithWork_cost parent r actions hne read states velocity _ i R hr)
  simp only [List.map_const', List.length_finRange, List.sum_replicate, smul_eq_mul] at h
  constructor
  · simp only [bandPredicateReadWithWork, bandPredicateWithWork, h.1]
  · unfold bandPredicateReadWithWork bandPredicateWithWork
    dsimp only
    exact costBound _ _ _ _ _ _ h.2

end BinaryFraction
end EditApproximation

end OAI

import OAI.Combinatorics.EditApproximation.Binary.BinaryPrefixSpace
import OAI.Combinatorics.EditApproximation.Binary.BinaryWideSpace
import OAI.Combinatorics.EditApproximation.Binary.BinaryCutReads
import OAI.Combinatorics.EditApproximation.Definitions


namespace OAI

namespace EditApproximation

/-- List traversal, including the input index spine when it is freshly generated. -/


theorem allAllocation_le_work {α : Type*} (test : α → Bool × ℕ)
    (allocation : α → ℕ) (xs : List α) (h : ∀ x ∈ xs, allocation x ≤ (test x).2) :
    allAllocation allocation xs ≤ (allWithWork test xs).2 := by
  induction xs with
  | nil => simp only [allAllocation, allWithWork, Nat.zero_le]
  | cons x xs ih =>
    have hh := h x List.mem_cons_self
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    unfold allAllocation allWithWork
    dsimp only
    exact Nat.add_le_add (Nat.add_le_add hh ht) (by decide : 1 ≤ 3)

theorem allAllocation_with_spine {α : Type*} (test : α → Bool × ℕ)
    (allocation : α → ℕ) (xs : List α) (h : ∀ x ∈ xs, allocation x ≤ (test x).2) :
    allAllocation allocation xs + xs.length ≤ (allWithWork test xs).2 := by
  have costBound (a a' b b' l : ℕ) (ha : a ≤ a') (hb : b + l ≤ b') :
      a + b + 1 + (l + 1) ≤ a' + b' + 3 := by
    omega
  induction xs with
  | nil => simp only [allAllocation, allWithWork, List.length_nil, Nat.zero_add, Nat.zero_le]
  | cons x xs ih =>
    have hh := h x List.mem_cons_self
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    unfold allAllocation allWithWork
    dsimp only
    simp only [List.length_cons]
    exact costBound _ _ _ _ _ hh ht



theorem zeroConnectionAllocation_le_work {n : ℕ} (start finish : ℕ) (states : List (TargetInterval n)) :
    zeroConnectionAllocation start states finish ≤ (zeroConnectionWithWork start states finish).2 := by
  induction states generalizing start with
  | nil => exact naturalEqualAllocation_le_work start finish
  | cons state rest ih =>
    have hh := naturalEqualAllocation_le_work start state.lo
    have ht := ih state.hi
    unfold zeroConnectionAllocation zeroConnectionWithWork
    dsimp only
    exact Nat.add_le_add_right (Nat.add_le_add hh ht) 1



theorem translatedEndpointAllocation_le_work (reference root endpoint : ℕ) :
    translatedEndpointAllocation reference root endpoint ≤ (translatedEndpointWithWork reference root endpoint).2 := by
  have hs := bitSubtractAllocation_le_work endpoint.bits root.bits false
  have ha := binaryNaturalAddAllocation_le_work reference (bitWordValue (binaryNaturalSubtractWithWork endpoint root).1)
  unfold translatedEndpointAllocation translatedEndpointWithWork binaryNaturalSubtractWithWork
  dsimp only [binaryNaturalSubtractWithWork] at ha ⊢
  omega

namespace BinaryFraction



theorem leAllocation_le_work (a b : BinaryFraction) :
    leAllocation a b ≤ (leWithWork a b).2 := by
  have h := ltAllocation_le_work b a
  unfold leAllocation leWithWork
  dsimp only
  omega



theorem naturalDistanceLeAllocation_le_work (a b radius : ℕ) :
    naturalDistanceLeAllocation a b radius ≤ (naturalDistanceLeWithWork a b radius).2 := by
  have hd := distanceAllocation_le_work (nat a) (nat b)
  have hl := leAllocation_le_work (distanceWithWork (nat a) (nat b)).1 (nat radius)
  unfold naturalDistanceLeAllocation naturalDistanceLeWithWork
  dsimp only
  omega



theorem affineErrorAllocation_le_work (position offset velocity prediction tolerance : BinaryFraction) :
    affineErrorAllocation position offset velocity prediction tolerance ≤
      (affineErrorWithWork position offset velocity prediction tolerance).2 := by
  have hd := subAllocation_le_work position offset
  have hp := canonicalMulAllocation_le_work velocity prediction
  have he := subAllocation_le_work (subWithWork position offset).1 (canonicalMulWithWork velocity prediction).1
  have hl := leAllocation_le_work
    (subWithWork (subWithWork position offset).1 (canonicalMulWithWork velocity prediction).1).1.absolute tolerance
  unfold affineErrorAllocation affineErrorWithWork
  dsimp only
  omega



theorem bandToleranceAllocation_le_work (tau theta : BinaryFraction) (b M : ℕ) :
    bandToleranceAllocation tau theta b M ≤ (bandToleranceWithWork tau theta b M).2 := by
  have hp := canonicalMulAllocation_le_work tau theta
  have hs := canonicalMulAllocation_le_work (canonicalMulWithWork tau theta).1 (nat b)
  have hd := divAllocation_le_work (canonicalMulWithWork (canonicalMulWithWork tau theta).1 (nat b)).1 (nat M)
  unfold bandToleranceAllocation bandToleranceWithWork
  dsimp only
  omega



theorem cutGuardReadAllocation_le_work {nx ny M : ℕ} (parent : TargetInterval nx) (r : TargetInterval ny)
    (actions : List (Fin M → TargetInterval ny)) (hne : actions ≠ [])
    (read : Fin M → TargetInterval ny → BinaryFraction × ℕ)
    (allocation : Fin M → TargetInterval ny → ℕ) (states : Fin M → TargetInterval ny)
    (velocity tolerance : BinaryFraction) (j : Fin M)
    (h : ∀ action ∈ actions, ∀ i, allocation i (action i) ≤ (read i (action i)).2) :
    cutGuardReadAllocation parent r actions hne read allocation states velocity tolerance j ≤
      (cutGuardReadWithWork parent r actions hne read states velocity tolerance j).2 := by
  have hs := subAllocation_le_work (nat (states j).lo) (nat (sourceChild parent j).lo)
  have ho := subAllocation_le_work (nat r.lo) (nat parent.lo)
  have hp := prefixMinimumReadAllocation_le_work parent r actions hne read allocation j.val
    (subWithWork (nat (states j).lo) (nat (sourceChild parent j).lo)).1 h
  have he := affineErrorAllocation_le_work
    (subWithWork (nat (states j).lo) (nat (sourceChild parent j).lo)).1
    (subWithWork (nat r.lo) (nat parent.lo)).1 velocity
    (prefixMinimumReadWithWork parent r actions hne read j.val
      (subWithWork (nat (states j).lo) (nat (sourceChild parent j).lo)).1).1 tolerance
  unfold cutGuardReadAllocation cutGuardReadWithWork
  split_ifs <;> dsimp only
  · exact Nat.zero_le _
  · have hsum := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hs ho) hp) he
    exact (Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.add_le_add_right hsum _) _) _) _).trans (Nat.le_add_right _ 5)

end BinaryFraction
end EditApproximation

end OAI

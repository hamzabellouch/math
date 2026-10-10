import OAI.Probability.MatroidProphet.Pivots.Interleavings
import Mathlib.Data.Fintype.Fin

namespace OAI

namespace MatroidProphet
namespace Pivots

open Finset

variable {r q : ℕ}

def oldBefore (time : Occurrence r q → ℕ) (t : ℕ) : ℕ :=
  (Finset.univ.filter (fun i : Fin r => time (Sum.inl i) < t)).card

def movableBefore (time : Occurrence r q → ℕ) (t : ℕ) : ℕ :=
  (Finset.univ.filter (fun i : Fin q => time (Sum.inr i) < t)).card

lemma oldBefore_mono (time : Occurrence r q → ℕ) : Monotone (oldBefore time) := by
  intro u v huv
  apply Finset.card_le_card
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    lt_of_lt_of_le (Finset.mem_filter.mp hi).2 huv⟩

lemma movableBefore_mono (time : Occurrence r q → ℕ) : Monotone (movableBefore time) := by
  intro u v huv
  apply Finset.card_le_card
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    lt_of_lt_of_le (Finset.mem_filter.mp hi).2 huv⟩

lemma oldBefore_lt_after (time : Occurrence r q → ℕ) (i : Fin r) {t : ℕ}
    (hit : time (Sum.inl i) < t) :
    oldBefore time (time (Sum.inl i)) < oldBefore time t := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_trans (Finset.mem_filter.mp hj).2 hit⟩
  · intro heq
    have hi : i ∈ Finset.univ.filter (fun j : Fin r => time (Sum.inl j) < t) := by simp [hit]
    rw [← heq] at hi
    simp at hi

lemma movableBefore_lt_after (time : Occurrence r q → ℕ) (i : Fin q) {t : ℕ}
    (hit : time (Sum.inr i) < t) :
    movableBefore time (time (Sum.inr i)) < movableBefore time t := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_trans (Finset.mem_filter.mp hj).2 hit⟩
  · intro heq
    have hi : i ∈ Finset.univ.filter (fun j : Fin q => time (Sum.inr j) < t) := by simp [hit]
    rw [← heq] at hi
    simp at hi

lemma movableBefore_self_lt (time : Occurrence r q → ℕ) (i : Fin q) :
    movableBefore time (time (Sum.inr i)) < q := by
  have hcard : (Finset.univ.filter (fun j : Fin q => time (Sum.inr j) < time (Sum.inr i))).card <
      (Finset.univ : Finset (Fin q)).card := by
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.filter_subset _ _, ?_⟩
    intro heq
    have hi : i ∈ (Finset.univ : Finset (Fin q)) := Finset.mem_univ _
    rw [← heq] at hi
    simp at hi
  simpa [movableBefore] using hcard

lemma old_time_lt_iff (time : Occurrence r q → ℕ) (horder : OldOrdered time)
    (i j : Fin r) : time (Sum.inl i) < time (Sum.inl j) ↔ i < j := by
  refine ⟨fun hij => ?_, fun hij => horder i j hij⟩
  by_contra h
  rcases lt_or_eq_of_le (le_of_not_gt h) with hji | rfl
  · exact Nat.lt_asymm (horder j i hji) hij
  · exact Nat.lt_irrefl _ hij

lemma oldBefore_self (time : Occurrence r q → ℕ) (horder : OldOrdered time) (i : Fin r) :
    oldBefore time (time (Sum.inl i)) = i.val := by
  unfold oldBefore
  have heq : Finset.univ.filter (fun j : Fin r => time (Sum.inl j) < time (Sum.inl i)) =
      Finset.Iio i := by
    ext j
    simp [old_time_lt_iff time horder]
  rw [heq, Fin.card_Iio]

def scoreExponent (s : ℕ) (time : Occurrence r q → ℕ) : Occurrence r q → ℕ
  | Sum.inl i => (s + 1) * (i.val + 1)
  | Sum.inr i => (s + 1) * oldBefore time (time (Sum.inr i)) +
      movableBefore time (time (Sum.inr i)) + 1

@[simp] lemma scoreExponent_old (s : ℕ) (time : Occurrence r q → ℕ) (i : Fin r) :
    scoreExponent s time (Sum.inl i) = (s + 1) * (i.val + 1) := rfl

lemma scoreExponent_preserves_order (s : ℕ) (hqs : q ≤ s)
    (time : Occurrence r q → ℕ) (horder : OldOrdered time)
    {o p : Occurrence r q} (hop : time o < time p) :
    scoreExponent s time o < scoreExponent s time p := by
  cases o with
  | inl i =>
    cases p with
    | inl j =>
      have hij := (old_time_lt_iff time horder i j).mp hop
      exact Nat.mul_lt_mul_of_pos_left (Nat.add_lt_add_right hij 1) (by omega)
    | inr j =>
      have hcnt := oldBefore_lt_after time i hop
      rw [oldBefore_self time horder i] at hcnt
      have hmul := Nat.mul_le_mul_left (s + 1) (Nat.succ_le_of_lt hcnt)
      simp only [Nat.succ_eq_add_one] at hmul
      simp only [scoreExponent]
      omega
  | inr i =>
    have hbound := lt_of_lt_of_le (movableBefore_self_lt time i) hqs
    have hmono := oldBefore_mono time (Nat.le_of_lt hop)
    cases p with
    | inl j =>
      rw [oldBefore_self time horder j] at hmono
      have hmul := Nat.mul_le_mul_left (s + 1) hmono
      simp only [scoreExponent, Nat.mul_add, Nat.mul_one]
      omega
    | inr j =>
      have hstrict := movableBefore_lt_after time i hop
      rcases Nat.eq_or_lt_of_le hmono with heq | hlt
      · simp only [scoreExponent]
        rw [heq]
        omega
      · have hmul := Nat.mul_le_mul_left (s + 1) (Nat.succ_le_of_lt hlt)
        simp only [Nat.succ_eq_add_one, Nat.mul_add, Nat.mul_one] at hmul
        simp only [scoreExponent]
        omega

lemma scoreExponent_injective (s : ℕ) (hqs : q ≤ s)
    (time : Occurrence r q → ℕ) (horder : OldOrdered time) (htime : Function.Injective time) :
    Function.Injective (scoreExponent s time) := by
  intro o p heq
  apply htime
  apply le_antisymm
  · by_contra h
    have hlt := scoreExponent_preserves_order s hqs time horder (Nat.lt_of_not_ge h)
    omega
  · by_contra h
    have hlt := scoreExponent_preserves_order s hqs time horder (Nat.lt_of_not_ge h)
    omega

end Pivots
end MatroidProphet

end OAI

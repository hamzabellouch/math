import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.ZMod.Basic

namespace OAI


namespace PerfectCompleteness.OddLists

open scoped BigOperators

variable {A B : Type*} {s : Nat}

abbrev OddList (s : Nat) (A : Type*) :=
  {L : Finset A // Odd L.card ∧ L.card ≤ s}

namespace OddList

theorem odd (L : OddList s A) : Odd L.val.card := L.property.1

theorem card_le (L : OddList s A) : L.val.card ≤ s := L.property.2

theorem card_pos (L : OddList s A) : 0 < L.val.card := by
  apply Nat.pos_of_ne_zero
  intro hzero
  have hodd := L.odd
  rw [hzero] at hodd
  exact Nat.not_odd_zero hodd

theorem nonempty (L : OddList s A) : L.val.Nonempty :=
  Finset.card_pos.mp L.card_pos

def singleton (positive : 0 < s) (a : A) : OddList s A :=
  ⟨{a}, by
    simp only [Finset.card_singleton]
    exact ⟨odd_one, Nat.succ_le_of_lt positive⟩⟩

@[simp] theorem singleton_val (positive : 0 < s) (a : A) :
    (singleton positive a).val = {a} := rfl

theorem nonempty_type [Nonempty A] (positive : 0 < s) : Nonempty (OddList s A) := by
  obtain ⟨a⟩ := ‹Nonempty A›
  exact ⟨singleton positive a⟩

instance [Nonempty A] [NeZero s] : Nonempty (OddList s A) :=
  nonempty_type (Nat.pos_of_ne_zero (NeZero.ne s))

end OddList

section Parity

variable [Fintype B] [DecidableEq B]

def parityPushforward (π : A → B) (L : Finset A) : Finset B :=
  Finset.univ.filter fun b => Odd ((L.filter fun a => π a = b).card)

@[simp] theorem mem_parityPushforward (π : A → B) (L : Finset A) (b : B) :
    b ∈ parityPushforward π L ↔ Odd ((L.filter fun a => π a = b).card) := by
  simp only [parityPushforward, Finset.mem_filter, Finset.mem_univ, true_and]

theorem parityPushforward_preimage (π : A → B) (L : Finset A) (b : B)
    (member : b ∈ parityPushforward π L) : ∃ a ∈ L, π a = b := by
  have hodd := (mem_parityPushforward π L b).mp member
  have hpos : 0 < (L.filter fun a => π a = b).card := by
    apply Nat.pos_of_ne_zero
    intro hzero
    rw [hzero] at hodd
    exact Nat.not_odd_zero hodd
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
  exact ⟨a, (Finset.mem_filter.mp ha).1, (Finset.mem_filter.mp ha).2⟩

theorem parityPushforward_subset_image (π : A → B) (L : Finset A) :
    parityPushforward π L ⊆ L.image π := by
  intro b hb
  obtain ⟨a, ha, hab⟩ := parityPushforward_preimage π L b hb
  exact Finset.mem_image.mpr ⟨a, ha, hab⟩

theorem parityPushforward_card_le (π : A → B) (L : Finset A) :
    (parityPushforward π L).card ≤ L.card :=
  (Finset.card_le_card (parityPushforward_subset_image π L)).trans Finset.card_image_le

theorem sum_fiber_card (π : A → B) (L : Finset A) :
    (∑ b : B, (L.filter fun a => π a = b).card) = L.card := by
  simpa using Finset.sum_card_fiberwise_eq_card_filter L Finset.univ π

theorem mod_two_eq_odd_indicator (n : Nat) :
    n % 2 = if Odd n then 1 else 0 := by
  by_cases hodd : Odd n
  · rw [ite_eq_left hodd]
    exact Nat.odd_iff.mp hodd
  · rw [ite_eq_right hodd]
    exact Nat.not_odd_iff.mp hodd

theorem parityPushforward_card_mod_two (π : A → B) (L : Finset A) :
    (parityPushforward π L).card % 2 = L.card % 2 := by
  have hcount : (parityPushforward π L).card =
      ∑ b : B, (L.filter fun a => π a = b).card % 2 := by
    simp only [mod_two_eq_odd_indicator, Finset.sum_boole, parityPushforward, Nat.cast_id]
  rw [hcount, ← Finset.sum_nat_mod, sum_fiber_card]

theorem parityPushforward_odd (π : A → B) (L : Finset A) (odd : Odd L.card) :
    Odd (parityPushforward π L).card := by
  apply Nat.odd_iff.mpr
  rw [parityPushforward_card_mod_two]
  exact Nat.odd_iff.mp odd

theorem mem_parityPushforward_iff_sum (π : A → B) (L : Finset A) (b : B) :
    b ∈ parityPushforward π L ↔
      (∑ a ∈ L, if π a = b then (1 : ZMod 2) else 0) = 1 := by
  rw [mem_parityPushforward, Finset.sum_boole]
  exact ZMod.natCast_eq_one_iff_odd.symm

namespace OddList

def map (π : A → B) (L : OddList s A) : OddList s B :=
  ⟨parityPushforward π L.val, parityPushforward_odd π L.val L.odd,
    (parityPushforward_card_le π L.val).trans L.card_le⟩

@[simp] theorem map_val (π : A → B) (L : OddList s A) :
    (map π L).val = parityPushforward π L.val := rfl

theorem exists_preimage (π : A → B) (L : OddList s A) (b : B)
    (member : b ∈ (map π L).val) : ∃ a ∈ L.val, π a = b :=
  parityPushforward_preimage π L.val b member

theorem exists_accepting_pair (π : A → B) (L : OddList s A) :
    ∃ a ∈ L.val, ∃ b ∈ (map π L).val, π a = b := by
  obtain ⟨b, hb⟩ := (map π L).nonempty
  obtain ⟨a, ha, hab⟩ := exists_preimage π L b hb
  exact ⟨a, ha, b, hb, hab⟩

theorem exists_accepting_pair_of_eq (π : A → B) (L : OddList s A) (R : OddList s B)
    (accepted : map π L = R) : ∃ a ∈ L.val, ∃ b ∈ R.val, π a = b := by
  rw [← accepted]
  exact exists_accepting_pair π L

end OddList
end Parity

section Supports

variable [Fintype A]

def support (f : A → ZMod 2) : Finset A :=
  Finset.univ.filter fun a => f a = 1

@[simp] theorem mem_support (f : A → ZMod 2) (a : A) :
    a ∈ support f ↔ f a = 1 := by
  simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]

private theorem binary_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  have h : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  exact h x

theorem support_card_cast (f : A → ZMod 2) :
    ((support f).card : ZMod 2) = ∑ a, f a := by
  unfold support
  rw [Finset.natCast_card_filter]
  apply Finset.sum_congr rfl
  intro a _
  rcases binary_cases (f a) with hzero | hone
  · simp only [hzero, zero_ne_one, ite_false]
  · simp only [hone, ite_true]

theorem support_odd_of_sum_one (f : A → ZMod 2) (normalized : (∑ a, f a) = 1) :
    Odd (support f).card :=
  ZMod.natCast_eq_one_iff_odd.mp ((support_card_cast f).trans normalized)

theorem parityPushforward_support [Fintype B] [DecidableEq B]
    (π : A → B) (f : A → ZMod 2) :
    parityPushforward π (support f) =
      support (fun b => ∑ a, if π a = b then f a else 0) := by
  ext b
  rw [mem_parityPushforward_iff_sum, mem_support]
  have hsum : (∑ a ∈ support f, if π a = b then (1 : ZMod 2) else 0) =
      ∑ a, if π a = b then f a else 0 := by
    unfold support
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a _
    rcases binary_cases (f a) with hzero | hone
    · simp [hzero]
    · simp [hone]
  rw [hsum]

end Supports

namespace OddList

def extract (positive : 0 < s) (fallback : A) (candidate : Finset A) : OddList s A :=
  if valid : Odd candidate.card ∧ candidate.card ≤ s then
    ⟨candidate, valid⟩ else singleton positive fallback

@[simp] theorem extract_valid (positive : 0 < s) (fallback : A) (candidate : Finset A)
    (valid : Odd candidate.card ∧ candidate.card ≤ s) :
    (extract positive fallback candidate).val = candidate := by
  simp only [extract, dite_eq_left valid]

theorem extract_invalid (positive : 0 < s) (fallback : A) (candidate : Finset A)
    (invalid : ¬ (Odd candidate.card ∧ candidate.card ≤ s)) :
    (extract positive fallback candidate).val = {fallback} := by
  simp only [extract, dite_eq_right invalid, singleton_val]

def extractOption (positive : 0 < s) (fallback : A) : Option (Finset A) → OddList s A
  | none => singleton positive fallback
  | some candidate => extract positive fallback candidate

@[simp] theorem extractOption_none (positive : 0 < s) (fallback : A) :
    (extractOption positive fallback none).val = {fallback} := rfl

@[simp] theorem extractOption_some_valid (positive : 0 < s) (fallback : A)
    (candidate : Finset A) (valid : Odd candidate.card ∧ candidate.card ≤ s) :
    (extractOption positive fallback (some candidate)).val = candidate :=
  extract_valid positive fallback candidate valid

noncomputable def defaultList [Nonempty A] (positive : 0 < s) : OddList s A :=
  singleton positive (Classical.choice ‹Nonempty A›)

noncomputable def extractDefault [Nonempty A] (positive : 0 < s)
    (candidate : Option (Finset A)) : OddList s A :=
  extractOption positive (Classical.choice ‹Nonempty A›) candidate

end OddList

end PerfectCompleteness.OddLists

end OAI

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import OAI.NumberTheory.Ostmann.Basic

namespace OAI

/-! # Actual finite tails of the two summands -/

namespace Ostmann

open scoped Classical

noncomputable def summandPrefix (A : Set ℕ) (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter fun n => n ∈ A

noncomputable def summandTail (A : Set ℕ) (lo hi : ℕ) : Finset ℕ :=
  (Finset.Ioc lo hi).filter fun n => n ∈ A

noncomputable def positiveSummandTail (A : Set ℕ) (lo hi : ℕ) : Finset ℤ :=
  (summandTail A lo hi).image fun n : ℕ => (n : ℤ)

noncomputable def negativeSummandTail (B : Set ℕ) (lo hi : ℕ) : Finset ℤ :=
  (summandTail B lo hi).image fun n : ℕ => -(n : ℤ)

@[simp] theorem mem_summandPrefix (A : Set ℕ) (N n : ℕ) :
    n ∈ summandPrefix A N ↔ n ∈ A ∧ n ≤ N := by
  simp only [summandPrefix, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
  tauto

@[simp] theorem mem_summandTail (A : Set ℕ) (lo hi n : ℕ) :
    n ∈ summandTail A lo hi ↔ n ∈ A ∧ lo < n ∧ n ≤ hi := by
  simp only [summandTail, Finset.mem_filter, Finset.mem_Ioc]
  tauto

theorem summandPrefix_card_split (A : Set ℕ) (lo hi : ℕ) (hle : lo ≤ hi) :
    (summandPrefix A hi).card = (summandPrefix A lo).card + (summandTail A lo hi).card := by
  have hlo : (summandPrefix A hi).filter (fun n => n ≤ lo) = summandPrefix A lo := by
    ext n
    simp only [Finset.mem_filter, mem_summandPrefix]
    constructor
    · rintro ⟨⟨ha, _⟩, hn⟩; exact ⟨ha, hn⟩
    · rintro ⟨ha, hn⟩; exact ⟨⟨ha, hn.trans hle⟩, hn⟩
  have hhi : (summandPrefix A hi).filter (fun n => ¬ n ≤ lo) = summandTail A lo hi := by
    ext n
    simp only [Finset.mem_filter, mem_summandPrefix, mem_summandTail]
    constructor
    · rintro ⟨⟨ha, hh⟩, hn⟩; exact ⟨ha, Nat.lt_of_not_ge hn, hh⟩
    · rintro ⟨ha, hn, hh⟩; exact ⟨⟨ha, hh⟩, Nat.not_le_of_lt hn⟩
  have hh := Finset.card_filter_add_card_filter_not (s := summandPrefix A hi) (fun n => n ≤ lo)
  rw [hlo, hhi] at hh
  exact hh.symm

@[simp] theorem positiveSummandTail_card (A : Set ℕ) (lo hi : ℕ) :
    (positiveSummandTail A lo hi).card = (summandTail A lo hi).card := by
  apply Finset.card_image_of_injective
  intro a b hab
  change (a : ℤ) = (b : ℤ) at hab
  exact_mod_cast hab

@[simp] theorem negativeSummandTail_card (B : Set ℕ) (lo hi : ℕ) :
    (negativeSummandTail B lo hi).card = (summandTail B lo hi).card := by
  apply Finset.card_image_of_injective
  intro a b hab
  exact_mod_cast neg_injective hab

theorem positiveSummandTail_bounds (A : Set ℕ) (lo hi : ℕ) {x : ℤ}
    (hx : x ∈ positiveSummandTail A lo hi) : (lo : ℤ) < x ∧ x ≤ hi := by
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨_, hnlo, hnhi⟩ := (mem_summandTail A lo hi n).mp hn
  exact ⟨by exact_mod_cast hnlo, by exact_mod_cast hnhi⟩

theorem negativeSummandTail_bounds (B : Set ℕ) (lo hi : ℕ) {x : ℤ}
    (hx : x ∈ negativeSummandTail B lo hi) : -(hi : ℤ) ≤ x ∧ x < -(lo : ℤ) := by
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨_, hnlo, hnhi⟩ := (mem_summandTail B lo hi n).mp hn
  constructor <;> omega

theorem EventuallyPrimeSumset.tail_prime_differences {A B : Set ℕ}
    (h : EventuallyPrimeSumset A B) :
    ∃ N : ℕ, ∀ lo hi : ℕ, N ≤ lo →
      ∀ x ∈ positiveSummandTail A lo hi, ∀ y ∈ negativeSummandTail B lo hi,
        (x - y).natAbs.Prime ∧ (lo : ℤ) < x - y := by
  obtain ⟨N, hN⟩ := h.prime_add
  refine ⟨N, ?_⟩
  intro lo hi hNlo x hx y hy
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨haA, halo, _⟩ := (mem_summandTail A lo hi a).mp ha
  obtain ⟨hbB, _, _⟩ := (mem_summandTail B lo hi b).mp hb
  have hab : (a : ℤ) - -(b : ℤ) = ((a + b : ℕ) : ℤ) := by push_cast; ring
  rw [hab, Int.natAbs_natCast]
  exact ⟨hN a haA b hbB (by omega), by exact_mod_cast (by omega : lo < a + b)⟩

end Ostmann

end OAI

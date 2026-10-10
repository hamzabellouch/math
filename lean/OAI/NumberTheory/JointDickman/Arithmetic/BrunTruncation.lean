import OAI.NumberTheory.JointDickman.Arithmetic.UpperSieveInput
import Mathlib.Data.Nat.Choose.Sum

namespace OAI

/-! # Even inclusion-exclusion truncations for the finite sieve -/
namespace JointDickman
open Finset

noncomputable def brunTruncation (S : Finset ℕ) (m : ℕ) : ℝ :=
  ∑ D ∈ S.powerset.filter (fun D => D.card ≤ m), (-1 : ℝ)^D.card

 theorem brunTruncation_eq_choose_sum (S : Finset ℕ) (m : ℕ) :
    brunTruncation S m = ∑ k ∈ range (m+1), (-1 : ℝ)^k*(S.card.choose k) := by
  classical
  have hf := sum_fiberwise_of_maps_to (g := Finset.card)
    (s := S.powerset.filter (fun D => D.card ≤ m)) (t := range (m+1))
    (fun D hD => mem_range.mpr (Nat.lt_succ_of_le (mem_filter.mp hD).2))
    (fun D => (-1 : ℝ)^D.card)
  rw [brunTruncation, ← hf]
  apply sum_congr rfl
  intro k hk
  have hkm : k ≤ m := Nat.le_of_lt_succ (mem_range.mp hk)
  have he : (S.powerset.filter (fun D => D.card ≤ m)).filter (fun D => D.card = k) =
      S.powersetCard k := by
    ext D
    simp only [mem_filter, mem_powerset, mem_powersetCard]
    constructor
    · rintro ⟨⟨hDS,_⟩,hDk⟩
      exact ⟨hDS,hDk⟩
    · rintro ⟨hDS,hDk⟩
      exact ⟨⟨hDS,hDk.trans_le hkm⟩,hDk⟩
  rw [he]
  trans ∑ _D ∈ S.powersetCard k, (-1 : ℝ)^k
  · apply sum_congr rfl
    intro D hD
    rw [(mem_powersetCard.mp hD).2]
  · simp [mul_comm]

 theorem brunTruncation_even (S : Finset ℕ) (r : ℕ) :
    brunTruncation S (2*r) = if S = ∅ then 1 else ((S.card-1).choose (2*r) : ℝ) := by
  classical
  rw [brunTruncation_eq_choose_sum]
  by_cases hS : S = ∅
  · subst S
    rw [ite_eq_left rfl, sum_eq_single 0]
    · simp
    · intro k _ hk
      simp only [card_empty]
      rw [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hk)]
      simp
    · simp
  · rw [ite_eq_right hS]
    have hs : S.card = (S.card-1)+1 := by have := card_pos.mpr (nonempty_iff_ne_empty.mpr hS); omega
    have h := Int.alternating_sum_range_choose_eq_choose (n := S.card-1) (m := 2*r)
    have hr : (-1 : ℤ)^(2*r) = 1 := by simp [pow_mul]
    rw [← hs,hr,one_mul] at h
    exact_mod_cast h

 theorem brunTruncation_nonneg (S : Finset ℕ) (r : ℕ) : 0 ≤ brunTruncation S (2*r) := by
  rw [brunTruncation_even]
  split_ifs <;> positivity

 theorem brunTruncation_upper (P E : Finset ℕ) (r : ℕ) :
    avoidsSelected P E ≤ brunTruncation (P ∩ E) (2*r) := by
  classical
  rw [avoidsSelected, brunTruncation_even]
  by_cases h : Disjoint P E
  · simp [h, disjoint_iff_inter_eq_empty.mp h]
  · have hne : P ∩ E ≠ ∅ := fun he => h (disjoint_iff_inter_eq_empty.mpr he)
    simp only [h, ite_false, hne]
    positivity

end JointDickman

end OAI

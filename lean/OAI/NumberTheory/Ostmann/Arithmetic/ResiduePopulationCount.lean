import Mathlib.Data.Finset.Max
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Dist
import OAI.NumberTheory.Ostmann.Construction.IntegerIntervalDistribution

namespace OAI

/-! # Counting bounded populations in their occupied residue classes -/

namespace Ostmann

open scoped BigOperators Classical

theorem nat_progression_population_card_le (S : Finset ℕ) (q D : ℕ) (hq : 0 < q)
    (hdiam : ∀ a ∈ S, ∀ b ∈ S, Nat.dist a b ≤ D)
    (hcongr : ∀ a ∈ S, ∀ b ∈ S, a ≡ b [MOD q]) :
    (S.card : ℝ) ≤ (D : ℝ) / q + 2 := by
  by_cases hS : S.Nonempty
  · let a := S.min' hS
    have ha : a ∈ S := Finset.min'_mem _ _
    have hsub : S.erase a ⊆ (Finset.Ioc a (a + D)).filter (fun n => n ≡ a [MOD q]) := by
      intro b hb
      obtain ⟨hne, hbS⟩ := Finset.mem_erase.mp hb
      have hab : a ≤ b := Finset.min'_le S b hbS
      have hd := hdiam a ha b hbS
      rw [Nat.dist_eq_sub_of_le hab] at hd
      exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, by omega⟩, hcongr b hbS a ha⟩
    have hc : ((S.erase a).card : ℝ) ≤
        (((Finset.Ioc a (a + D)).filter (fun n => n ≡ a [MOD q])).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have he := (abs_le.mp (integer_interval_residue_error a (a + D) q a (by omega) hq)).2
    have hcard : (S.card : ℝ) = ((S.erase a).card : ℝ) + 1 := by
      exact_mod_cast (Finset.card_erase_add_one ha).symm
    rw [Nat.cast_add, add_sub_cancel_left] at he
    linarith
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

theorem nat_residue_population_card_le (S : Finset ℕ) (q D : ℕ) (hq : 0 < q)
    (hdiam : ∀ a ∈ S, ∀ b ∈ S, Nat.dist a b ≤ D) :
    (S.card : ℝ) ≤ ((S.image (fun n : ℕ => (n : ZMod q))).card : ℝ) * ((D : ℝ) / q + 2) := by
  let R := S.image (fun n : ℕ => (n : ZMod q))
  have hf (r : ZMod q) : ((S.filter fun n : ℕ => (n : ZMod q) = r).card : ℝ) ≤ (D : ℝ) / q + 2 := by
    apply nat_progression_population_card_le _ q D hq
    · intro a ha b hb
      exact hdiam a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1
    · intro a ha b hb
      exact (ZMod.natCast_eq_natCast_iff a b q).mp
        ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)
  have heq := Finset.card_eq_sum_card_image (fun n : ℕ => (n : ZMod q)) S
  calc
    (S.card : ℝ) = ∑ r ∈ R, ((S.filter fun n : ℕ => (n : ZMod q) = r).card : ℝ) := by
      exact_mod_cast heq
    _ ≤ ∑ _r ∈ R, ((D : ℝ) / q + 2) := Finset.sum_le_sum fun r _ => hf r
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      rfl

end Ostmann

end OAI

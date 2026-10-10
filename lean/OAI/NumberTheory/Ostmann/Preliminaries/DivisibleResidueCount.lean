import Mathlib.Data.Nat.ModEq
import OAI.NumberTheory.Ostmann.Construction.IntegerIntervalDistribution

namespace OAI

/-! # Uniform counts of multiples in a prescribed coprime residue class -/

namespace Ostmann

theorem divisible_residue_class_count (lo hi L r a : ℕ)
    (hlo : lo ≤ hi) (hL : 0 < L) (hr : 0 < r) (hcop : L.Coprime r) :
    (((Finset.Ioc lo hi).filter (fun n => Nat.ModEq L n a ∧ r ∣ n)).card : ℝ) ≤
      ((hi : ℝ) - lo) / (L * r) + 1 := by
  classical
  let T := (Finset.Ioc lo hi).filter (fun n => Nat.ModEq L n a ∧ r ∣ n)
  change (T.card : ℝ) ≤ _
  by_cases hT : T.Nonempty
  · obtain ⟨x, hx⟩ := hT
    have hx' := (Finset.mem_filter.mp hx).2
    have hsub : T ⊆ (Finset.Ioc lo hi).filter (fun n => Nat.ModEq (L * r) n x) := by
      intro n hn
      obtain ⟨hnI, hnL, hnr⟩ := Finset.mem_filter.mp hn
      refine Finset.mem_filter.mpr ⟨hnI, ?_⟩
      apply (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp
      exact ⟨hnL.trans hx'.1.symm,
        (Nat.modEq_zero_iff_dvd.mpr hnr).trans (Nat.modEq_zero_iff_dvd.mpr hx'.2).symm⟩
    have hcard : (T.card : ℝ) ≤
        (((Finset.Ioc lo hi).filter (fun n => Nat.ModEq (L * r) n x)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have hh := (abs_le.mp (integer_interval_residue_error lo hi (L * r) x hlo (Nat.mul_pos hL hr))).2
    push_cast at hh
    linarith
  · have he : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
    rw [he, Finset.card_empty, Nat.cast_zero]
    have hwidth : (0 : ℝ) ≤ (hi : ℝ) - lo := sub_nonneg.mpr (Nat.cast_le.mpr hlo)
    positivity

theorem dyadic_divisible_residue_class_count (N L r a : ℕ)
    (hL : 0 < L) (hr : 0 < r) (hcop : L.Coprime r) (hsize : L * r ≤ N) :
    (((Finset.Ioc N (2 * N)).filter (fun n => Nat.ModEq L n a ∧ r ∣ n)).card : ℝ) ≤
      2 * (N : ℝ) / (L * r) := by
  have hb := divisible_residue_class_count N (2 * N) L r a (by omega) hL hr hcop
  have hden : (0 : ℝ) < L * r := by positivity
  have hs : (L : ℝ) * r ≤ N := by exact_mod_cast hsize
  have hone : (1 : ℝ) ≤ (N : ℝ) / (L * r) := (one_le_div hden).mpr hs
  push_cast at hb
  ring_nf at hb hone ⊢
  linarith

/-- The dyadic range absorbs the additive residue-count error for every
half kernel of size at most the square root of its upper endpoint. -/
theorem half_kernel_modulus_le (L N r : ℕ) (hN : 2 * L ^ 2 ≤ N) (hr : r ^ 2 ≤ 2 * N) :
    L * r ≤ N := by
  have hs : (L * r) ^ 2 ≤ N ^ 2 := by
    calc
      _ = L ^ 2 * r ^ 2 := mul_pow _ _ _
      _ ≤ L ^ 2 * (2 * N) := Nat.mul_le_mul_left _ hr
      _ = (2 * L ^ 2) * N := by ring
      _ ≤ N * N := Nat.mul_le_mul_right _ hN
      _ = _ := (pow_two N).symm
  exact le_of_pow_le_pow_left₀ (by decide : 2 ≠ 0) (Nat.zero_le N) hs

end Ostmann

end OAI

import Mathlib.Algebra.BigOperators.Intervals
import OAI.NumberTheory.Ostmann.Quadratic.QuadraticSmallDivisorTail

namespace OAI

/-! # Uniform finite tails of the inverse-square series -/

namespace Ostmann

open scoped Classical BigOperators

 theorem quadratic_inverse_square_tail (S : Finset ℕ) {V : ℝ} (hV : 0 < V)
    (hS : ∀ d ∈ S, V < (d : ℝ)) :
    (∑ d ∈ S, 1 / (d : ℝ) ^ 2) ≤ 2 / V := by
  by_cases hs : S.Nonempty
  · let M : ℕ := ⌊V⌋₊ + 1
    let B : ℕ := S.sup id
    have hM : 0 < M := by dsimp [M]; omega
    have hMV : V < (M : ℝ) := by simpa only [M, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one V
    have hMd : ∀ d ∈ S, M ≤ d := by
      intro d hd
      by_contra hn
      have hdF : d ≤ ⌊V⌋₊ := by dsimp [M] at hn; omega
      have hle := (Nat.cast_le.mpr hdF).trans (Nat.floor_le hV.le)
      exact (not_lt_of_ge hle) (hS d hd)
    have hMB : M ≤ B + 1 := by
      obtain ⟨d, hd⟩ := hs
      have hdb : d ≤ B := Finset.le_sup (f := id) hd
      exact (hMd d hd).trans (by omega)
    have hsub : S ⊆ Finset.Ico M (B + 1) := by
      intro d hd
      exact Finset.mem_Ico.mpr ⟨hMd d hd, Nat.lt_succ_of_le (Finset.le_sup (f := id) hd)⟩
    have hpoint (d : ℕ) (hd : d ∈ Finset.Ico M (B + 1)) :
        1 / (d : ℝ) ^ 2 ≤ 2 / (d : ℝ) - 2 / ((d : ℝ) + 1) := by
      have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hM.trans_le (Finset.mem_Ico.mp hd).1
      have hd0 : (0 : ℝ) < d := by linarith
      have hid : 2 / (d : ℝ) - 2 / ((d : ℝ) + 1) = 2 / ((d : ℝ) * (d + 1)) := by
        field_simp
        ring
      rw [hid]
      apply (div_le_div_iff₀ (sq_pos_of_pos hd0) (mul_pos hd0 (by linarith))).mpr
      nlinarith
    calc
      _ ≤ ∑ d ∈ Finset.Ico M (B + 1), 1 / (d : ℝ) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
      _ ≤ ∑ d ∈ Finset.Ico M (B + 1), (2 / (d : ℝ) - 2 / ((d : ℝ) + 1)) :=
        Finset.sum_le_sum hpoint
      _ = 2 / (M : ℝ) - 2 / ((B : ℝ) + 1) := by
        have hh := Finset.sum_Ico_sub (f := fun n : ℕ => -(2 / (n : ℝ))) hMB
        simpa only [Nat.cast_add, Nat.cast_one, sub_neg_eq_add, neg_add_eq_sub] using hh
      _ ≤ 2 / (M : ℝ) := sub_le_self _ (by positivity)
      _ ≤ 2 / V := div_le_div_of_nonneg_left (by norm_num) hV hMV.le
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hs, Finset.sum_empty]
    positivity

end Ostmann

end OAI

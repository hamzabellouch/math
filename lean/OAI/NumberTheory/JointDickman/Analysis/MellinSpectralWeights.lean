import OAI.NumberTheory.JointDickman.Analysis.MellinPacketScale
import Mathlib.Analysis.PSeries

namespace OAI

/-! # Summable unit-interval bounds for a Schwartz spectral weight -/
namespace JointDickman
open scoped SchwartzMap

/-- A fixed Schwartz window has a summable quadratic Fourier majorant on
unit intervals. This will weight the local Dirichlet mean-square estimates. -/
theorem schwartz_cell_norm_sq_bound (w : 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℤ) (u : ℝ), (n : ℝ) ≤ u → u ≤ n + 1 →
      ‖w u‖ ^ 2 ≤ C / (1 + |(n : ℝ)|) ^ 4 := by
  let C := 2 * (SchwartzMap.seminorm ℝ 0 0 w + SchwartzMap.seminorm ℝ 2 0 w) + 1
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨16 * C ^ 2, by positivity, ?_⟩
  intro n u hnu hun
  have h0 := SchwartzMap.norm_le_seminorm ℝ w u
  have h2 := SchwartzMap.norm_pow_mul_le_seminorm ℝ w 2 u
  rw [Real.norm_eq_abs] at h2
  have hw : (1 + |u|) ^ 2 * ‖w u‖ ≤ C := by
    have hh := mul_nonneg (sq_nonneg (|u| - 1)) (norm_nonneg (w u))
    dsimp [C]
    nlinarith
  have hnu' : |(n : ℝ)| ≤ |u| + 1 := by
    apply abs_le.mpr
    constructor <;> linarith [le_abs_self u, neg_abs_le u]
  have hq : 0 < 1 + |(n : ℝ)| := by positivity
  have hrel : (1 + |(n : ℝ)|) ^ 2 ≤ (2 * (1 + |u|)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith [abs_nonneg u]) 2
  have hprod : (1 + |(n : ℝ)|) ^ 2 * ‖w u‖ ≤ 4 * C := by
    have hh := mul_le_mul_of_nonneg_right hrel (norm_nonneg (w u))
    nlinarith
  have hs := pow_le_pow_left₀
    (mul_nonneg (sq_nonneg (1 + |(n : ℝ)|)) (norm_nonneg (w u))) hprod 2
  apply (le_div_iff₀ (pow_pos hq 4)).mpr
  convert hs using 1 <;> ring

lemma summable_integer_window_weights :
    Summable (fun n : ℤ => 1 / (1 + |(n : ℝ)|) ^ 3) := by
  have hs : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 3) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have ht := (summable_nat_add_iff 1).mpr hs
  apply Summable.of_nat_of_neg
  · apply ht.congr
    intro n
    simp only [Int.cast_natCast, Nat.cast_add, Nat.cast_one,
      abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n), add_comm]
  · apply ht.congr
    intro n
    simp only [Int.cast_neg, Int.cast_natCast, abs_neg, Nat.cast_add, Nat.cast_one,
      abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n), add_comm]

end JointDickman

end OAI

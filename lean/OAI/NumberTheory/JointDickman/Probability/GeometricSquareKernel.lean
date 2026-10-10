import OAI.NumberTheory.JointDickman.Arithmetic.SmoothedBilinear

namespace OAI

/-! # The squared geometric kernel in the smoothed bilinear estimate -/
namespace JointDickman
open Finset
open scoped ComplexConjugate

noncomputable def geometricSquareKernel (N : ℕ) (t : ℝ) : ℝ :=
  ‖∑ n ∈ range N, additivePhase (t*n)‖^2

lemma additivePhase_nat_mul (t : ℝ) (n : ℕ) :
    additivePhase (t*n) = additivePhase t ^ n := by
  induction n with
  | zero => simp [additivePhase]
  | succ n ih =>
    rw [Nat.cast_add,Nat.cast_one,mul_add,mul_one,additivePhase_add,ih,pow_succ]

lemma geometricSquareKernel_nonneg (N : ℕ) (t : ℝ) :
    0 ≤ geometricSquareKernel N t := sq_nonneg _

lemma geometricSquareKernel_neg (N : ℕ) (t : ℝ) :
    geometricSquareKernel N (-t) = geometricSquareKernel N t := by
  unfold geometricSquareKernel
  have he : (∑ n ∈ range N, additivePhase (-t*n)) =
      conj (∑ n ∈ range N, additivePhase (t*n)) := by
    rw [map_sum]
    apply sum_congr rfl
    intro n hn
    rw [additivePhase_conj,neg_mul]
  rw [he,Complex.norm_conj]

lemma geometricSquareKernel_zero (N : ℕ) :
    geometricSquareKernel N 0 = (N:ℝ)^2 := by
  simp [geometricSquareKernel,additivePhase]

lemma geometricSquareKernel_le (N : ℕ) (t : ℝ) :
    geometricSquareKernel N t ≤ (N:ℝ)^2 := by
  apply pow_le_pow_left₀ (norm_nonneg _)
  calc
    _ ≤ ∑ n ∈ range N, ‖additivePhase (t*n)‖ := norm_sum_le _ _
    _ = _ := by simp [norm_additivePhase]

lemma geometricSquareKernel_decay (N : ℕ) (t : ℝ) :
    geometricSquareKernel N t * ‖1-additivePhase t‖^2 ≤ 4 := by
  have hb : ‖∑ n ∈ range N, additivePhase (t*n)‖ * ‖1-additivePhase t‖ ≤ 2 := by
    simp_rw [additivePhase_nat_mul]
    rw [←norm_mul,geom_sum_mul_neg]
    calc
      _ ≤ ‖(1:ℂ)‖ + ‖additivePhase t^N‖ := norm_sub_le _ _
      _ = 2 := by norm_num [norm_additivePhase]
  have hh := pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hb 2
  simpa only [mul_pow,geometricSquareKernel,show (2:ℝ)^2=4 by norm_num] using hh

lemma geometricSquareKernel_le_div (N : ℕ) (t : ℝ) (ht : additivePhase t ≠ 1) :
    geometricSquareKernel N t ≤ 4/‖1-additivePhase t‖^2 := by
  apply (le_div_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr ht.symm)))).mpr
  exact geometricSquareKernel_decay N t

lemma geometricSquareKernel_int_Ico (N : ℕ) (t : ℝ) :
    ‖∑ u ∈ Ico (0:ℤ) N, additivePhase (t*u)‖^2 = geometricSquareKernel N t := by
  rw [Int.Ico_eq_finset_map,sum_map]
  simp [geometricSquareKernel]

end JointDickman

end OAI

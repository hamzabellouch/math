import OAI.NumberTheory.JointDickman.Counting.HyperbolaBlockBound
import Mathlib.Analysis.SpecialFunctions.Log.Base

namespace OAI

/-! # Exact dyadic partition of a finite prime set -/
namespace JointDickman
open Finset

lemma sum_monotone_blocks {R : Type*} [AddCommMonoid R]
    (P : Finset ℕ) (F : ℕ → R) (L : ℕ → ℕ) (hL : Monotone L) (J : ℕ) :
    (∑ j ∈ range J, ∑ p ∈ P.filter (fun p => L j < p ∧ p ≤ L (j+1)), F p) =
      ∑ p ∈ P.filter (fun p => L 0 < p ∧ p ≤ L J), F p := by
  induction J with
  | zero =>
    simp only [range_zero,sum_empty,sum_filter]
    symm
    apply sum_eq_zero
    intro p hp
    split_ifs with h
    · omega
    · rfl
  | succ J ih =>
    rw [sum_range_succ,ih]
    simp only [sum_filter]
    rw [←sum_add_distrib]
    apply sum_congr rfl
    intro p hp
    have h0J := hL (Nat.zero_le J)
    have hJS := hL (Nat.le_succ J)
    by_cases h0 : L 0 < p
    · by_cases hJ : p ≤ L J
      · have hS : p ≤ L (J+1) := hJ.trans hJS
        have hn : ¬ L J < p := by omega
        simp [h0,hJ,hS,hn]
      · have hJ' : L J < p := by omega
        by_cases hS : p ≤ L (J+1) <;> simp [h0,hJ,hJ',hS]
    · have hJ : ¬ L J < p := by omega
      simp [h0,hJ]

lemma sum_dyadic_blocks {R : Type*} [AddCommMonoid R]
    (P : Finset ℕ) (F : ℕ → R) (Z J : ℕ)
    (hP : ∀ p ∈ P, Z < p ∧ p ≤ 2^J*Z) :
    (∑ p ∈ P, F p) = ∑ j ∈ range J,
      ∑ p ∈ P.filter (fun p => 2^j*Z < p ∧ p ≤ 2^(j+1)*Z), F p := by
  rw [sum_monotone_blocks P F (fun j => 2^j*Z)
    (fun i j hij => Nat.mul_le_mul_right Z (Nat.pow_le_pow_right (by norm_num) hij))]
  simp only [pow_zero,one_mul]
  symm
  apply sum_filter_of_ne
  intro p hp hn
  exact hP p hp

lemma dyadic_cover_integer (N Z : ℕ) (hZ : 0 < Z) :
    N ≤ 2^(Nat.log 2 N+1)*Z := by
  apply (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) N).le.trans
  exact Nat.le_mul_of_pos_right _ hZ

lemma dyadic_block_count_le (N : ℕ) :
    ((Nat.log 2 N+1:ℕ):ℝ) ≤ 1+Real.log N/Real.log 2 := by
  have h := Real.natLog_le_logb N 2
  simpa only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,Real.logb,add_comm] using
    add_le_add h (le_refl (1:ℝ))

end JointDickman

end OAI

import OAI.NumberTheory.Ostmann.Characters.SparseWeightUniformBound
import OAI.NumberTheory.Ostmann.Characters.SparseConductorCutoff

namespace OAI

/-! # The truncated weight grows more slowly than every fixed power of X -/
namespace Ostmann
open Filter

theorem sparse_weight_uniform_exponential (C L : ℝ) (hC : 0 ≤ C) (hL : 1 ≤ L)
    (n : ℕ) (hn : (n : ℝ) ≤ Real.exp (Real.exp ((9 / 10 : ℝ) * L))) :
    (((sparseTruncationDegree C L : ℕ) + 1 : ℝ) *
      (n + 1 : ℝ) ^ sparseTruncationDegree C L) ^ 2 ≤
      Real.exp ((6 * C + 8) * L * Real.exp ((9 / 10 : ℝ) * L)) := by
  let K := sparseTruncationDegree C L
  let E := Real.exp ((9 / 10 : ℝ) * L)
  have hE : 1 ≤ E := Real.one_le_exp (by positivity)
  have hK : (K : ℝ) ≤ (C + 1) * L := by
    have hh := (Nat.ceil_lt_add_one (mul_nonneg hC (show 0 ≤ L by linarith))).le
    change (K : ℝ) ≤ C * L + 1 at hh
    nlinarith
  have hKexp : (K + 1 : ℝ) ≤ Real.exp ((C + 2) * L) := by
    apply le_trans _ (Real.add_one_le_exp ((C + 2) * L))
    nlinarith
  have hnexp : (n + 1 : ℝ) ≤ Real.exp (2 * E) := by
    have he := Real.add_one_le_exp E
    have hh : (n + 1 : ℝ) ≤ 2 * Real.exp E := by
      have hh' : 1 ≤ Real.exp E := Real.one_le_exp (by linarith)
      dsimp [E] at hh'
      linarith
    apply hh.trans
    calc
      _ ≤ Real.exp E * Real.exp E := mul_le_mul_of_nonneg_right (by linarith) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hp : (n + 1 : ℝ) ^ K ≤ Real.exp ((K : ℝ) * (2 * E)) := by
    calc
      _ ≤ (Real.exp (2 * E)) ^ K := pow_le_pow_left₀ (by positivity) hnexp K
      _ = _ := (Real.exp_nat_mul _ _).symm
  have hh : ((K + 1 : ℝ) * (n + 1 : ℝ) ^ K) ^ 2 ≤
      (Real.exp ((C + 2) * L) * Real.exp ((K : ℝ) * (2 * E))) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (mul_le_mul hKexp hp (by positivity) (Real.exp_nonneg _)) 2
  apply hh.trans
  rw [← Real.exp_add, ← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have hmul := mul_le_mul_of_nonneg_right hK (show 0 ≤ E by linarith)
  have hCmul := mul_le_mul_of_nonneg_left hE (show 0 ≤ (C + 2) * L by positivity)
  dsimp [K, E] at *
  norm_num
  nlinarith

 theorem eventual_sparse_weight_subpower (C δ : ℝ) (hC : 0 ≤ C) (hδ : 0 < δ) :
    ∀ᶠ L : ℝ in atTop, ∀ n : ℕ,
      (n : ℝ) ≤ Real.exp (Real.exp ((9 / 10 : ℝ) * L)) →
      (((sparseTruncationDegree C L : ℕ) + 1 : ℝ) *
        (n + 1 : ℝ) ^ sparseTruncationDegree C L) ^ 2 ≤
        Real.exp (δ * Real.exp L) := by
  have hs := ((isLittleO_pow_exp_pos_mul_atTop 1
    (show (0 : ℝ) < 1 / 10 by norm_num)).const_mul_left (6 * C + 8)).bound hδ
  filter_upwards [hs, eventually_ge_atTop (1 : ℝ)] with L hsmall hL n hn
  apply (sparse_weight_uniform_exponential C L hC hL n hn).trans
  apply Real.exp_le_exp.mpr
  have hsmall' : (6 * C + 8) * L ≤ δ * Real.exp ((1 / 10 : ℝ) * L) := by
    simpa only [pow_one, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (6 * C + 8) * L),
      abs_of_pos (Real.exp_pos _)] using hsmall
  have hh := mul_le_mul_of_nonneg_right hsmall' (Real.exp_nonneg ((9 / 10 : ℝ) * L))
  have he : Real.exp ((1 / 10 : ℝ) * L) * Real.exp ((9 / 10 : ℝ) * L) = Real.exp L := by
    rw [← Real.exp_add]
    congr 1
    ring
  rwa [mul_assoc δ, he] at hh

end Ostmann

end OAI

import OAI.NumberTheory.TwoPoint.Walks.RankDecay
import OAI.NumberTheory.TwoPoint.Bounds.CrudeHarmonicMass

namespace OAI

/-! Explicit enumeration costs before the high-rank saving. -/

namespace TwoPointCorrelations

open Finset

/-- Count the column and the ordered choices of its controlling pairs. -/
lemma rankPairChoices_exp_bound (J R r a b : ℕ) (L : ℝ)
    (hL : 1 ≤ L) (hJ : (J : ℝ) ≤ L ^ a)
    (hR : (R : ℝ) + 1 ≤ L ^ b) (hr : (r : ℝ) ≤ L) :
    (J * R ^ (2 * r) : ℕ) ≤
      Real.exp (((a : ℝ) + 2 * b) * L * Real.log L) := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL
  have hj : (J : ℝ) ≤ Real.exp ((a : ℝ) * Real.log L) := by
    simpa only [Real.exp_nat_mul, Real.exp_log hLp] using hJ
  have hlogR : Real.log ((R : ℝ) + 1) ≤ (b : ℝ) * Real.log L := by
    have ht := Real.log_le_log (by positivity : (0 : ℝ) < R + 1) hR
    simpa only [Real.log_pow] using ht
  have hp : (R : ℝ) ^ (2 * r) ≤
      Real.exp (((2 * r : ℕ) : ℝ) * ((b : ℝ) * Real.log L)) := by
    calc
      _ ≤ ((R : ℝ) + 1) ^ (2 * r) :=
        pow_le_pow_left₀ (by positivity) (by linarith) _
      _ = Real.exp (((2 * r : ℕ) : ℝ) * Real.log ((R : ℝ) + 1)) := by
        rw [Real.exp_nat_mul, Real.exp_log (by positivity : (0 : ℝ) < R + 1)]
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hlogR (by positivity))
  calc
    _ = (J : ℝ) * (R : ℝ) ^ (2 * r) := by push_cast; rfl
    _ ≤ Real.exp ((a : ℝ) * Real.log L) *
        Real.exp (((2 * r : ℕ) : ℝ) * ((b : ℝ) * Real.log L)) := by
      exact mul_le_mul hj hp (by positivity) (by positivity)
    _ = Real.exp ((a : ℝ) * Real.log L +
        ((2 * r : ℕ) : ℝ) * ((b : ℝ) * Real.log L)) := (Real.exp_add _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have ha := mul_le_mul_of_nonneg_left hL (show 0 ≤ (a : ℝ) * Real.log L by positivity)
      have hb := mul_le_mul_of_nonneg_left hr (show 0 ≤ (2 : ℝ) * b * Real.log L by positivity)
      push_cast
      nlinarith

/-- A reciprocal mass bounded by `L²` costs only two logarithms per slot. -/
lemma harmonic_power_exp_bound (V L C : ℝ) (n : ℕ)
    (hL : 0 < L) (hV : 0 ≤ V) (hV' : V ≤ L ^ (2 : ℕ))
    (hn : (n : ℝ) ≤ C * L * Real.log L) (hlog : 0 ≤ Real.log L) :
    V ^ n ≤ Real.exp (2 * C * L * (Real.log L) ^ 2) := by
  calc
    _ ≤ (L ^ (2 : ℕ)) ^ n := pow_le_pow_left₀ hV hV' n
    _ = (Real.exp (2 * Real.log L)) ^ n := by
      congr 1
      rw [show 2 * Real.log L = Real.log L + Real.log L by ring,
        Real.exp_add, Real.exp_log hL]
      ring
    _ = Real.exp ((n : ℝ) * (2 * Real.log L)) := by rw [Real.exp_nat_mul]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hm := mul_le_mul_of_nonneg_right hn (show 0 ≤ 2 * Real.log L by positivity)
      nlinarith

/-- The crude pattern, selected-pair, harmonic, and external costs, all
before imposing any congruences. The constants describe only fixed
polynomial alphabets and the slot budget. -/
theorem rank_enumeration_exp_bound (J R N D d a b r n : ℕ)
    (L C Cmass Cweight V W : ℝ)
    (hL : 1 ≤ Real.log L) (hL' : 1 ≤ L)
    (hRN : R ≤ N) (hR : (R : ℝ) ≤ 2 * L) (hC : 0 ≤ C)
    (hslots : (N : ℝ) ≤ C * R * Real.log L)
    (hN : (N : ℝ) + 1 ≤ L ^ (2 : ℕ)) (hD : (D : ℝ) + 1 ≤ L ^ d)
    (hJ : (J : ℝ) ≤ L ^ a) (hRpoly : (R : ℝ) + 1 ≤ L ^ b)
    (hr : (r : ℝ) ≤ L)
    (hV : 0 ≤ V) (hV' : V ≤ L ^ (2 : ℕ))
    (hn : (n : ℝ) ≤ Cmass * L * Real.log L)
    (hW : 0 ≤ W) (hW' : W ≤ Real.exp (Cweight * L * (Real.log L) ^ 2)) :
    (Fintype.card (CrudeWordCode R N D) : ℝ) *
        (J * R ^ (2 * r) : ℕ) * W * V ^ n ≤
      Real.exp ((2 * ((d : ℝ) + 4) * C + ((a : ℝ) + 2 * b) + Cweight + 2 * Cmass) *
        L * (Real.log L) ^ 2) := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL'
  have hc := crudeWordCode_bound R N D d L C hL hRN hslots hN hD
  have hc' : (Fintype.card (CrudeWordCode R N D) : ℝ) ≤
      Real.exp ((2 * ((d : ℝ) + 4) * C) * L * (Real.log L) ^ 2) := by
    apply hc.trans
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_left hR
      (show 0 ≤ ((d : ℝ) + 4) * C * (Real.log L) ^ 2 by positivity)
    nlinarith
  have hp := rankPairChoices_exp_bound J R r a b L hL' hJ hRpoly hr
  have hp' : (J * R ^ (2 * r) : ℕ) ≤
      Real.exp (((a : ℝ) + 2 * b) * L * (Real.log L) ^ 2) := by
    apply hp.trans
    apply Real.exp_le_exp.mpr
    have hl : Real.log L ≤ (Real.log L) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_left hl (by positivity)
  have hv := harmonic_power_exp_bound V L Cmass n hLp hV hV' hn (by linarith)
  calc
    _ ≤ Real.exp ((2 * ((d : ℝ) + 4) * C) * L * (Real.log L) ^ 2) *
        Real.exp (((a : ℝ) + 2 * b) * L * (Real.log L) ^ 2) *
        Real.exp (Cweight * L * (Real.log L) ^ 2) *
        Real.exp (2 * Cmass * L * (Real.log L) ^ 2) := by
      apply mul_le_mul _ hv (by positivity) (by positivity)
      apply mul_le_mul _ hW' hW (by positivity)
      exact mul_le_mul hc' hp' (by positivity) (by positivity)
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

end TwoPointCorrelations

end OAI

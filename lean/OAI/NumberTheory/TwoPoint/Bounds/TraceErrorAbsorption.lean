import OAI.NumberTheory.TwoPoint.Bounds.GoodTraceCost

namespace OAI

/-! The three exceptional trace classes are absorbed by an absolute change
of the square-root harmonic-mass constant. -/

namespace TwoPointCorrelations

open Filter

lemma eventually_trace_exceptional_cost :
    ∀ᶠ L : ℝ in atTop,
      Real.exp (108 * L) * (Real.exp (-L ^ (21 / 20 : ℝ)) +
        2 * Real.exp (-L ^ (101 / 100 : ℝ))) ≤ 1 := by
  have hgrow := (tendsto_rpow_atTop (show 0 < (1 / 100 : ℝ) by norm_num)).eventually
    (eventually_ge_atTop 110)
  filter_upwards [eventually_ge_atTop (1 : ℝ), hgrow] with L hL hgrow
  have hLp : 0 < L := by linarith
  have hpower : L * L ^ (1 / 100 : ℝ) = L ^ (101 / 100 : ℝ) := by
    rw [show (101 / 100 : ℝ) = 1 + 1 / 100 by norm_num,
      Real.rpow_add hLp, Real.rpow_one]
  have hlarge : 110 * L ≤ L ^ (101 / 100 : ℝ) := by
    have hb := mul_le_mul_of_nonneg_left hgrow hLp.le
    rw [hpower] at hb
    linarith
  have hs : Real.exp (-L ^ (21 / 20 : ℝ)) ≤ Real.exp (-L ^ (101 / 100 : ℝ)) := by
    apply Real.exp_le_exp.mpr
    exact neg_le_neg (Real.rpow_le_rpow_of_exponent_le hL (by norm_num))
  have hthree : (3 : ℝ) ≤ Real.exp (2 * L) := by
    apply le_trans (show (3 : ℝ) ≤ Real.exp 2 by linarith [Real.add_one_le_exp (2 : ℝ)])
    exact Real.exp_le_exp.mpr (by linarith)
  calc
    _ ≤ Real.exp (108 * L) * (Real.exp (-L ^ (101 / 100 : ℝ)) +
        2 * Real.exp (-L ^ (101 / 100 : ℝ))) :=
      mul_le_mul_of_nonneg_left (add_le_add hs le_rfl) (Real.exp_pos _).le
    _ = 3 * Real.exp (108 * L - L ^ (101 / 100 : ℝ)) := by
      rw [sub_eq_add_neg, Real.exp_add]
      ring
    _ ≤ 3 * Real.exp (-(2 * L)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num)
    _ ≤ Real.exp (2 * L) * Real.exp (-(2 * L)) :=
      mul_le_mul_of_nonneg_right hthree (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add]; simp

lemma trace_base_double_absorbs_one (J k : ℕ) (K W : ℝ)
    (hJ : 1 ≤ J) (hk : 1 ≤ k) (hK : 1 ≤ K) (hW : 1 ≤ W) :
    1 + (K * (Real.exp 150 * Real.sqrt W) ^ J) ^ (2 * k) ≤
      (K * (2 * Real.exp 150 * Real.sqrt W) ^ J) ^ (2 * k) := by
  let b := Real.exp 150 * Real.sqrt W
  have hb : 1 ≤ b := by
    have he : (1 : ℝ) ≤ Real.exp 150 := Real.one_le_exp (by norm_num)
    have hw : (1 : ℝ) ≤ Real.sqrt W := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hW
    exact one_le_mul_of_one_le_of_one_le he hw
  have hA : 1 ≤ (K * b ^ J) ^ (2 * k) :=
    one_le_pow₀ (one_le_mul_of_one_le_of_one_le hK (one_le_pow₀ hb))
  have ht : 2 ≤ (2 : ℝ) ^ (J * (2 * k)) := by
    have hn : 1 ≤ J * (2 * k) := Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (by omega) (by omega))
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℝ)) hn
  calc
    _ = 1 + (K * b ^ J) ^ (2 * k) := rfl
    _ ≤ 2 * (K * b ^ J) ^ (2 * k) := by linarith
    _ ≤ 2 ^ (J * (2 * k)) * (K * b ^ J) ^ (2 * k) :=
      mul_le_mul_of_nonneg_right ht (by positivity)
    _ = (K * (2 * Real.exp 150 * Real.sqrt W) ^ J) ^ (2 * k) := by
      rw [pow_mul, ← mul_pow]
      congr 1
      dsimp [b]
      simp only [mul_pow]
      ring

theorem eventually_trace_absorption :
    ∀ᶠ L : ℝ in atTop, ∀ (J k : ℕ) (K W M : ℝ),
      1 ≤ J → 1 ≤ k → 1 ≤ K → 1 ≤ W →
      M ≤ Real.exp (108 * L) * (Real.exp (-L ^ (21 / 20 : ℝ)) +
        2 * Real.exp (-L ^ (101 / 100 : ℝ))) +
        (K * (Real.exp 150 * Real.sqrt W) ^ J) ^ (2 * k) →
      M ≤ (K * (2 * Real.exp 150 * Real.sqrt W) ^ J) ^ (2 * k) := by
  filter_upwards [eventually_trace_exceptional_cost] with L herr
  intro J k K W M hJ hk hK hW hM
  exact (hM.trans (add_le_add herr le_rfl)).trans (trace_base_double_absorbs_one J k K W hJ hk hK hW)

end TwoPointCorrelations

end OAI

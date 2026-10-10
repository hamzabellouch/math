import OAI.NumberTheory.TwoPoint.Walks.RankDecay

namespace OAI

/-! A single prime saving dominates the short prohibited-word enumeration. -/

namespace TwoPointCorrelations

open Filter

lemma eventually_short_word_cost (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop,
      C * L ^ (1 / 10 : ℝ) * (Real.log L) ^ 2 ≤
        (1 / 2 : ℝ) * L ^ (199 / 200 : ℝ) := by
  have h := (isLittleO_log_rpow_rpow_atTop (2 : ℝ)
    (s := (179 / 200 : ℝ)) (by norm_num)).bound
      (show 0 < (1 / 2 : ℝ) / (C + 1) by positivity)
  filter_upwards [eventually_ge_atTop 1, h] with L hL hh
  have hLp : 0 < L := by linarith
  rw [Real.norm_eq_abs, Real.rpow_two, abs_of_nonneg (sq_nonneg _),
    Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hLp _)] at hh
  have hs : C * (Real.log L) ^ 2 ≤ (1 / 2 : ℝ) * L ^ (179 / 200 : ℝ) := by
    calc
      _ ≤ (C + 1) * (Real.log L) ^ 2 := by nlinarith [sq_nonneg (Real.log L)]
      _ ≤ (C + 1) * (((1 / 2 : ℝ) / (C + 1)) * L ^ (179 / 200 : ℝ)) :=
        mul_le_mul_of_nonneg_left hh (by positivity)
      _ = _ := by field_simp [show C + 1 ≠ 0 by linarith]
  have ht := mul_le_mul_of_nonneg_right hs (Real.rpow_nonneg hLp.le (1 / 10 : ℝ))
  have he : L ^ (179 / 200 : ℝ) * L ^ (1 / 10 : ℝ) = L ^ (199 / 200 : ℝ) := by
    rw [← Real.rpow_add hLp]
    norm_num
  nlinarith

/-- The complete short-word cost may include pattern and endpoint choices,
all reciprocal masses, and summation over lengths. No further saving is
used beyond the single nondegenerate last-prime relation. -/
theorem eventually_bad_event_decay (C : ℝ) (hC : 0 ≤ C) :
    ∀ᶠ L : ℝ in atTop, ∀ (s : ℕ) (H B cost total : ℝ),
      (s : ℝ) ≤ L ^ (1 / 10 : ℝ) → Real.exp (L ^ (199 / 200 : ℝ)) ≤ H →
      1 ≤ B → B ≤ Real.exp L →
      cost ≤ Real.exp (C * s * (Real.log L) ^ 2) →
      total ≤ cost * (H⁻¹ + (1 + Real.log B) / H) →
      total ≤ Real.exp (-(1 / 2 : ℝ) * L ^ (199 / 200 : ℝ)) := by
  filter_upwards [eventually_ge_atTop 2,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1),
    eventually_short_word_cost (C + 2) (by positivity)] with L hL hlog hshort
  intro s H B cost total hs hH hB hBupper hcost htotal
  have hLp : 0 < L := by linarith
  have hHp : 0 < H := (Real.exp_pos _).trans_le hH
  have hBp : 0 < B := by linarith
  have hlogB : Real.log B ≤ L := by
    have hh := Real.log_le_log hBp hBupper
    simpa only [Real.log_exp] using hh
  have hlogBpos : 0 ≤ Real.log B := Real.log_nonneg hB
  have hinv : H⁻¹ ≤ Real.exp (-L ^ (199 / 200 : ℝ)) := by
    rw [Real.exp_neg]
    exact inv_anti₀ (Real.exp_pos _) hH
  have hpoly : 2 + Real.log B ≤ Real.exp (2 * Real.log L) := by
    have he : Real.exp (2 * Real.log L) = L ^ (2 : ℕ) := by
      simpa only [Nat.cast_ofNat, Real.exp_log hLp] using Real.exp_nat_mul (Real.log L) 2
    rw [he]
    nlinarith
  have hbase : H⁻¹ + (1 + Real.log B) / H ≤
      Real.exp (2 * Real.log L - L ^ (199 / 200 : ℝ)) := by
    calc
      _ = (2 + Real.log B) * H⁻¹ := by ring
      _ ≤ Real.exp (2 * Real.log L) * Real.exp (-L ^ (199 / 200 : ℝ)) :=
        mul_le_mul hpoly hinv (inv_nonneg.mpr hHp.le) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; rfl
  have hone : 1 ≤ L ^ (1 / 10 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hexp : C * s * (Real.log L) ^ 2 + 2 * Real.log L ≤
      (C + 2) * L ^ (1 / 10 : ℝ) * (Real.log L) ^ 2 := by
    have hterm := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hs hC) (sq_nonneg (Real.log L))
    have hlog2 : Real.log L ≤ (Real.log L) ^ 2 := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hone) (sq_nonneg (Real.log L))]
  calc
    total ≤ Real.exp (C * s * (Real.log L) ^ 2) *
        (H⁻¹ + (1 + Real.log B) / H) :=
      htotal.trans (mul_le_mul_of_nonneg_right hcost (by positivity))
    _ ≤ Real.exp (C * s * (Real.log L) ^ 2) *
        Real.exp (2 * Real.log L - L ^ (199 / 200 : ℝ)) :=
      mul_le_mul_of_nonneg_left hbase (Real.exp_pos _).le
    _ = Real.exp (C * s * (Real.log L) ^ 2 + 2 * Real.log L - L ^ (199 / 200 : ℝ)) := by
      rw [← Real.exp_add]; congr 1; ring
    _ ≤ _ := by apply Real.exp_le_exp.mpr; linarith

end TwoPointCorrelations

end OAI

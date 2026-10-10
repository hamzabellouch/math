import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTWeakHurwitzGrowth

namespace OAI

/-! Normalize the weak Hurwitz growth bound without losing a power of the
height. The logarithmic disk budget is O(1+log q+loglog |t|), uniformly in q. -/

namespace TwoPointCorrelations

open Complex
open scoped Classical

noncomputable def mrtVKWeight (q : ℕ) (t : ℝ) : ℝ :=
  1 + Real.log (q : ℝ) + Real.log (mrtVKLog t)

lemma mrt_moving_growth_budget {x H C : ℝ} (hx : 1 ≤ x) (hH : 1 ≤ H) (hC : 0 < C) :
    x * (x ^ 2 + H ^ C) * H ^ (2 / 3 : ℝ) ≤
      Real.exp ((C + 4) * (1 + Real.log x + Real.log H)) := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hH0 : 0 < H := zero_lt_one.trans_le hH
  have hHC : 1 ≤ H ^ C := Real.one_le_rpow hH hC.le
  have hx3 : x ≤ x ^ 3 := by
    have hm := mul_nonneg (sub_nonneg.mpr hx) (show 0 ≤ x * (x + 1) by positivity)
    nlinarith only [hm]
  have hx30 : 0 ≤ x ^ 3 := pow_nonneg hx0.le _
  have ha : x * (x ^ 2 + H ^ C) ≤ 2 * x ^ 3 * H ^ C := by
    have ha1 := mul_le_mul_of_nonneg_left hHC hx30
    have ha2 := mul_le_mul_of_nonneg_right hx3 (Real.rpow_nonneg hH0.le C)
    nlinarith only [ha1, ha2]
  have hxpow : x ^ 3 ≤ x ^ (C + 4) := by
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hx
    norm_num
    linarith
  have hHpow : H ^ (C + 2 / 3) ≤ H ^ (C + 4) :=
    Real.rpow_le_rpow_of_exponent_le hH (by linarith)
  have hE : 2 ≤ Real.exp (C + 4) := by linarith [Real.add_one_le_exp (C + 4)]
  have he : Real.exp ((C + 4) * (1 + Real.log x + Real.log H)) =
      Real.exp (C + 4) * x ^ (C + 4) * H ^ (C + 4) := by
    rw [Real.rpow_def_of_pos hx0, Real.rpow_def_of_pos hH0,
      ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc
    _ ≤ (2 * x ^ 3 * H ^ C) * H ^ (2 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_right ha (Real.rpow_nonneg hH0.le _)
    _ = 2 * x ^ 3 * H ^ (C + 2 / 3) := by rw [Real.rpow_add hH0]; ring
    _ ≤ Real.exp (C + 4) * x ^ (C + 4) * H ^ (C + 4) := by
      exact mul_le_mul (mul_le_mul hE hxpow hx30 (Real.exp_nonneg _)) hHpow
        (Real.rpow_nonneg hH0.le _) (by positivity)
    _ = _ := he.symm

lemma mrt_VKWeight_ge_one {q : ℕ} [NeZero q] {t : ℝ} (hH : 1 ≤ mrtVKLog t) :
    1 ≤ mrtVKWeight q t := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  unfold mrtVKWeight
  linarith [Real.log_nonneg hq, Real.log_nonneg hH]

/-- A weak Hurwitz bound gives the normalized moving-disk growth budget,
with a single absolute small-radius threshold. -/
theorem MRTWeakHurwitzGrowthInput.normalized_disk (h : MRTWeakHurwitzGrowthInput) :
    ∃ C T r₀ : ℝ, 0 < C ∧ 0 < T ∧ 0 < r₀ ∧ r₀ ≤ 1 / 5 ∧
      ∀ t : ℝ, T ≤ |t| → 1 ≤ mrtVKLog t → mrtVKRadius t ≤ r₀ →
      ∀ (q : ℕ) [NeZero q], ∀ (χ : DirichletCharacter ℂ q),
      ∀ z ∈ Metric.closedBall (0 : ℂ) (15 / 16),
        ‖mrtMovingLFunction χ (mrtVKRadius t) t z‖ ≤
          Real.exp (C * mrtVKWeight q t) := by
  obtain ⟨C, T, hC, hT, hg⟩ := h.character_disk
  obtain ⟨r₀, hr₀, _, hi⟩ := mrt_moving_center_inverse
  refine ⟨C + 4, T, min r₀ (1 / 5), by linarith, hT,
    lt_min hr₀ (by norm_num), min_le_right _ _, ?_⟩
  intro t ht hH hr q _ χ
  have hH0 : 0 < mrtVKLog t := zero_lt_one.trans_le hH
  have hrpos : 0 < mrtVKRadius t := Real.rpow_pos_of_pos hH0 _
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hpoint := hg t ht (hr.trans (min_le_right _ _)) q χ
  have hinv := hi (mrtVKRadius t) hrpos (hr.trans (min_le_left _ _)) q χ t
  have hbudget := mrt_moving_growth_budget hq hH hC
  have hrinv : (mrtVKRadius t)⁻¹ = (mrtVKLog t) ^ (2 / 3 : ℝ) := by
    rw [mrtVKRadius, Real.rpow_neg hH0.le, inv_inv]
  have hprod : ((q : ℝ) * ((q : ℝ) ^ 2 + (mrtVKLog t) ^ C)) /
      mrtVKRadius t ≤ Real.exp ((C + 4) * mrtVKWeight q t) := by
    rw [div_eq_mul_inv, hrinv]
    exact hbudget
  apply mrt_moving_LFunction_growth χ (by positivity)
    (fun z hz => hpoint z (by
      have hh : ‖z‖ ≤ 15 / 16 := by simpa using hz
      linarith))
    hinv
  simpa only [← div_eq_mul_inv, one_div] using hprod

end TwoPointCorrelations

end OAI

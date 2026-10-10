import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTMovingGrowth

namespace OAI

/-! The same weak Hurwitz estimate controls all nearby character disks.
Using radius R(2t)/16 leaves room for both the first and doubled heights. -/

namespace TwoPointCorrelations

open Complex
open scoped Classical

lemma mrt_VKLog_pos (t : ℝ) : 0 < mrtVKLog t :=
  Real.log_pos (by linarith [abs_nonneg t])

lemma mrt_VKLog_double (t : ℝ) : mrtVKLog t ≤ mrtVKLog (2 * t) := by
  apply Real.log_le_log (by positivity : 0 < |t| + 3)
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith [abs_nonneg t]

lemma mrt_VKRadius_double (t : ℝ) : mrtVKRadius (2 * t) ≤ mrtVKRadius t := by
  exact Real.rpow_le_rpow_of_nonpos (mrt_VKLog_pos t) (mrt_VKLog_double t) (by norm_num)

lemma mrt_moving_shifted_region {r R v t : ℝ} (hr : 0 ≤ r) (hR : r ≤ R)
    (hshift : 3 * r + |v - t| ≤ 3 * R) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    1 - R ≤ (mrtMovingPoint r v z).re ∧
      (mrtMovingPoint r v z).re ≤ 1 + 5 * R ∧
      |(mrtMovingPoint r v z).im - t| ≤ 3 * R := by
  have hreg := mrt_moving_point_region (t := v) hr hz
  refine ⟨by linarith [hreg.1], by linarith [hreg.2.1], ?_⟩
  calc
    _ = |((mrtMovingPoint r v z).im - v) + (v - t)| := by congr 1; ring
    _ ≤ |(mrtMovingPoint r v z).im - v| + |v - t| := abs_add_le _ _
    _ ≤ 3 * r + |v - t| := add_le_add_left hreg.2.2 _
    _ ≤ _ := hshift

/-- The actual nearby disks satisfy a common logarithmic growth budget;
there is no independent regularity-in-height premise. -/
theorem MRTWeakHurwitzGrowthInput.local_disks (h : MRTWeakHurwitzGrowthInput) :
    ∃ D T r₀ : ℝ, 1 ≤ D ∧ 0 < T ∧ 0 < r₀ ∧ r₀ ≤ 1 / 5 ∧
      ∀ t : ℝ, T ≤ |t| → 1 ≤ mrtVKLog (2 * t) →
        mrtVKRadius (2 * t) / 16 ≤ r₀ →
        ∀ (q : ℕ) [NeZero q], ∀ (χ : DirichletCharacter ℂ q),
        ∀ v : ℝ, |v - t| ≤ 3 * (mrtVKRadius (2 * t) / 16) →
          (∀ z ∈ Metric.closedBall (0 : ℂ) (15 / 16),
            ‖mrtMovingLFunction χ (mrtVKRadius (2 * t) / 16) v z‖ ≤
              Real.exp (D * mrtVKWeight q (2 * t))) ∧
          (∀ z ∈ Metric.closedBall (0 : ℂ) (15 / 16),
            ‖mrtMovingLFunction (χ ^ 2) (mrtVKRadius (2 * t) / 16) (2 * v) z‖ ≤
              Real.exp (D * mrtVKWeight q (2 * t))) := by
  obtain ⟨C, T, hC, hT, hg⟩ := h
  obtain ⟨r₀, hr₀, _, hi⟩ := mrt_moving_center_inverse
  have hl16 : 0 ≤ Real.log 16 := Real.log_nonneg (by norm_num)
  refine ⟨C + 4 + Real.log 16, T, min r₀ (1 / 5), by linarith, hT,
    lt_min hr₀ (by norm_num), min_le_right _ _, ?_⟩
  intro t ht hH hr q _ χ v hv
  let H := mrtVKLog (2 * t)
  let r := mrtVKRadius (2 * t) / 16
  let A := (q : ℝ) * ((q : ℝ) ^ 2 + H ^ C)
  have hH0 : 0 < H := mrt_VKLog_pos (2 * t)
  have hrp : 0 < r := div_pos (Real.rpow_pos_of_pos hH0 _) (by norm_num)
  have hrsmall : r ≤ 1 / 5 := hr.trans (min_le_right _ _)
  have hrR2 : r ≤ mrtVKRadius (2 * t) := by
    have hR : 0 < mrtVKRadius (2 * t) := Real.rpow_pos_of_pos hH0 _
    dsimp [r]
    linarith
  have hrR : r ≤ mrtVKRadius t := hrR2.trans (mrt_VKRadius_double t)
  have ht2 : T ≤ |2 * t| := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [abs_nonneg t]
  have hraw (ψ : DirichletCharacter ℂ q) (w u : ℝ)
      (hu : T ≤ |u|) (hru : r ≤ mrtVKRadius u)
      (hshift : 3 * r + |w - u| ≤ 3 * mrtVKRadius u)
      (hHu : mrtVKLog u ≤ H) :
      ∀ z ∈ Metric.closedBall (0 : ℂ) (15 / 16),
        ‖DirichletCharacter.LFunction ψ (mrtMovingPoint r w z)‖ ≤ A := by
    intro z hz
    have hzn : ‖z‖ ≤ 1 := by
      have hh : ‖z‖ ≤ 15 / 16 := by simpa using hz
      linarith
    have hreg := mrt_moving_shifted_region hrp.le hru hshift hzn
    have hown := mrt_moving_point_region (t := w) hrp.le hzn
    apply mrt_character_of_hurwitz_growth ψ (by linarith [hown.1])
      (by linarith [hown.2.1])
    intro a ha
    exact (hg u hu a ha _ hreg.1 hreg.2.1 hreg.2.2).trans
      (Real.rpow_le_rpow (mrt_VKLog_pos u).le hHu hC.le)
  have hraw1 := hraw χ v t ht hrR (by
    change |v - t| ≤ 3 * r at hv
    have hRR := mrt_VKRadius_double t
    have heR : 16 * r = mrtVKRadius (2 * t) := by dsimp [r]; ring
    nlinarith) (mrt_VKLog_double t)
  have hshift2 : 3 * r + |2 * v - 2 * t| ≤ 3 * mrtVKRadius (2 * t) := by
    have he : 2 * v - 2 * t = 2 * (v - t) := by ring
    rw [he, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    change |v - t| ≤ 3 * r at hv
    have heR : 16 * r = mrtVKRadius (2 * t) := by dsimp [r]; ring
    nlinarith
  have hraw2 := hraw (χ ^ 2) (2 * v) (2 * t) ht2 hrR2 hshift2 le_rfl
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hw : 1 ≤ mrtVKWeight q (2 * t) := mrt_VKWeight_ge_one hH
  have hbudget := mrt_moving_growth_budget hq hH hC
  have hrinv : r⁻¹ = 16 * H ^ (2 / 3 : ℝ) := by
    change (mrtVKRadius (2 * t) / 16)⁻¹ = _
    rw [inv_div, div_eq_mul_inv, mrtVKRadius, Real.rpow_neg hH0.le, inv_inv]
  have hprod : A * (1 / r) ≤
      Real.exp ((C + 4 + Real.log 16) * mrtVKWeight q (2 * t)) := by
    rw [one_div, hrinv]
    calc
      _ = 16 * ((q : ℝ) * ((q : ℝ) ^ 2 + H ^ C) * H ^ (2 / 3 : ℝ)) := by dsimp [A]; ring
      _ ≤ 16 * Real.exp ((C + 4) * mrtVKWeight q (2 * t)) := by
        exact mul_le_mul_of_nonneg_left hbudget (by norm_num)
      _ = Real.exp (Real.log 16 + (C + 4) * mrtVKWeight q (2 * t)) := by
        rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 16)]
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith only [mul_nonneg hl16 (sub_nonneg.mpr hw)])
  constructor
  · exact mrt_moving_LFunction_growth χ (by dsimp [A]; positivity) hraw1
      (hi r hrp (hr.trans (min_le_left _ _)) q χ v) hprod
  · exact mrt_moving_LFunction_growth (χ ^ 2) (by dsimp [A]; positivity) hraw2
      (hi r hrp (hr.trans (min_le_left _ _)) q (χ ^ 2) (2 * v)) hprod

end TwoPointCorrelations

end OAI

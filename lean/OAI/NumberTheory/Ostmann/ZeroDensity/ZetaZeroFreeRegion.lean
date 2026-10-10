import OAI.NumberTheory.Ostmann.ZeroDensity.ZetaTrigonometric
import OAI.NumberTheory.Ostmann.ZeroDensity.ZeroFreeNumerics

namespace OAI

/-! # A logarithmic zero-free region for the regularized zeta function -/

namespace Ostmann

open Complex Filter Metric
open scoped Topology

theorem regularizedZeta_small_height_gap : ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 4 ∧
    ∀ ρ : ℂ, regularizedZeta ρ = 0 → 1 - r ≤ ρ.re → r ≤ |ρ.im| := by
  have hn := (regularizedZeta_analytic 1).continuousAt.eventually_ne
    (show regularizedZeta 1 ≠ 0 by simp)
  obtain ⟨R, hR, hball⟩ := Metric.eventually_nhds_iff.mp hn
  let r := min (R / 4) (1 / 4)
  have hr : 0 < r := lt_min (by positivity) (by norm_num)
  have hrR : r ≤ R / 4 := min_le_left _ _
  refine ⟨r, hr, min_le_right _ _, ?_⟩
  intro ρ hρ hnear
  have hρ1 := regularizedZeta_zero_re_lt_one ρ hρ
  by_contra hnot
  have hi : |ρ.im| < r := lt_of_not_ge hnot
  have hdist : dist ρ 1 < R := by
    rw [dist_eq_norm]
    have hb := Complex.norm_le_abs_re_add_abs_im (ρ - 1)
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
      sub_zero, abs_of_neg (show ρ.re - 1 < 0 by linarith)] at hb
    linarith
  exact hball hdist hρ

theorem realZeroKernel_away_bound (r δ t : ℝ) (hr : 0 < r) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (ht : r ≤ |t|) : realZeroKernel δ t ≤ 1 / r ^ 2 := by
  have ht2 : r ^ 2 ≤ t ^ 2 := by nlinarith [sq_abs t]
  unfold realZeroKernel
  calc
    δ / (δ ^ 2 + t ^ 2) ≤ 1 / (δ ^ 2 + t ^ 2) :=
      div_le_div_of_nonneg_right hδ1 (by positivity)
    _ ≤ 1 / r ^ 2 := div_le_div_of_nonneg_left (by norm_num) (by positivity) (by nlinarith)

theorem regularizedZeta_zero_free_region : ∃ c : ℝ, 0 < c ∧ c ≤ 1 / 4 ∧
    ∀ ρ : ℂ, regularizedZeta ρ = 0 →
      c / (Real.log (|ρ.im| + 2) + 1) ≤ 1 - ρ.re := by
  obtain ⟨r, hr, hr4, hsmall⟩ := regularizedZeta_small_height_gap
  obtain ⟨C, hC, hbound⟩ := zeta_near_zero_trigonometric_bound
  let D := C + 5 / r ^ 2
  have hD : 0 < D := by dsimp [D]; positivity
  let c := min r (1 / (2000 * (D + 1)))
  have hc : 0 < c := lt_min hr (by positivity)
  have hcr : c ≤ r := min_le_left _ _
  have hcc : c ≤ 1 / (2000 * (D + 1)) := min_le_right _ _
  refine ⟨c, hc, hcr.trans hr4, ?_⟩
  intro ρ hρ
  let H := Real.log (|ρ.im| + 2) + 1
  have hH : 1 ≤ H := by
    have hh := Real.log_nonneg (show 1 ≤ |ρ.im| + 2 by linarith [abs_nonneg ρ.im])
    dsimp [H]
    linarith
  have hHp : 0 < H := by linarith
  let δ := 1 / (100 * (D + 1) * H)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := by
    dsimp [δ]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hbudget : δ * (D * H) ≤ 1 / 100 := by
    dsimp [δ]
    have he : (1 / (100 * (D + 1) * H)) * (D * H) = D / (100 * (D + 1)) := by
      field_simp
    rw [he]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hcut : c / H ≤ δ / 20 := by
    have hh := div_le_div_of_nonneg_right hcc hHp.le
    apply hh.trans_eq
    dsimp [δ]
    field_simp
    ring
  have hcrH : c / H ≤ r := by
    calc
      c / H ≤ c / 1 := div_le_div_of_nonneg_left hc.le (by norm_num) hH
      _ ≤ r := by simpa using hcr
  by_contra hnot
  have hnear : 1 - δ / 20 ≤ ρ.re := by
    change ¬c / H ≤ 1 - ρ.re at hnot
    linarith [lt_of_not_ge hnot]
  have hnearR : 1 - r ≤ ρ.re := by
    change ¬c / H ≤ 1 - ρ.re at hnot
    linarith [lt_of_not_ge hnot]
  have hhalf : 1 / 2 ≤ ρ.re := by linarith
  have hi := hsmall ρ hρ hnearR
  have hk1 := realZeroKernel_away_bound r δ ρ.im hr hδ hδ1 hi
  have hk2 := realZeroKernel_away_bound r δ (2 * ρ.im) hr hδ hδ1 (by
    rw [abs_mul]
    norm_num
    linarith)
  have hupper := hbound ρ hρ hhalf (1 + δ) (by linarith) (by linarith)
  simp only [add_sub_cancel_left] at hupper
  have hcost : 5 / r ^ 2 ≤ (5 / r ^ 2) * H := by
    exact le_mul_of_one_le_right (by positivity) hH
  have hup : 4 / (1 + δ - ρ.re) ≤ 3 / δ + D * H := by
    dsimp [D, H]
    dsimp [H] at hcost
    simp only [div_eq_mul_inv] at hk1 hk2 hupper hcost ⊢
    nlinarith
  have hρ1 := regularizedZeta_zero_re_lt_one ρ hρ
  have hmass := real_zero_shifted_mass δ (1 + δ - ρ.re) hδ (by linarith) (by linarith)
  have hp := mul_le_mul_of_nonneg_left hup hδ.le
  have he : δ * (3 / δ + D * H) = 3 + δ * (D * H) := by field_simp
  rw [he] at hp
  linarith

end Ostmann

end OAI

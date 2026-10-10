import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

namespace OAI

namespace InvariantProjection.PowerGaps
open Filter Topology

theorem tendsto_rpow_neg_mul_atTop {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x : ℝ => x ^ (-c * x)) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ (tendsto_rpow_neg_atTop hc)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    exact Real.rpow_nonneg hx _
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    apply Real.rpow_le_rpow_of_exponent_le hx
    nlinarith

theorem tendsto_rpow_mul_ratio {a b : ℝ} (hab : a < b) :
    Tendsto (fun x : ℝ => x ^ (a * x) / x ^ (b * x)) atTop (𝓝 0) := by
  apply (tendsto_rpow_neg_mul_atTop (sub_pos.mpr hab)).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [← Real.rpow_sub hx]
  congr 1
  ring

theorem tendsto_ratio_of_power_lower {ι : Type*} {l : Filter ι}
    {m K : ι → ℝ} {a b : ℝ} (hab : a < b)
    (hm : Tendsto m l atTop) (hK : ∀ᶠ j in l, m j ^ (b * m j) ≤ K j) :
    Tendsto (fun j => m j ^ (a * m j) / K j) l (𝓝 0) := by
  have hmpos : ∀ᶠ j in l, 0 < m j := hm.eventually (eventually_gt_atTop 0)
  apply squeeze_zero' _ _ ((tendsto_rpow_mul_ratio hab).comp hm)
  · filter_upwards [hmpos, hK] with j hj hKj
    exact div_nonneg (Real.rpow_nonneg hj.le _)
      (le_trans (Real.rpow_nonneg hj.le _) hKj)
  · filter_upwards [hmpos, hK] with j hj hKj
    exact div_le_div_of_nonneg_left (Real.rpow_nonneg hj.le _)
      (Real.rpow_pos_of_pos hj _) hKj

theorem ceil_rpow_mul_le_two {a x : ℝ} (ha : 0 ≤ a) (hx : 1 ≤ x) :
    (⌈x ^ (a * x)⌉₊ : ℝ) ≤ 2 * x ^ (a * x) := by
  have hp : 1 ≤ x ^ (a * x) :=
    Real.one_le_rpow hx (mul_nonneg ha (le_trans (by norm_num) hx))
  have hc := Nat.ceil_lt_add_one (le_trans (by norm_num : (0 : ℝ) ≤ 1) hp)
  linarith

theorem tendsto_ceil_rpow_mul_ratio {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    Tendsto (fun x : ℝ => (⌈x ^ (a * x)⌉₊ : ℝ) / x ^ (b * x)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun x : ℝ => 2 * (x ^ (a * x) / x ^ (b * x)))
      atTop (𝓝 0) := by
    simpa using (tendsto_rpow_mul_ratio hab).const_mul 2
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    exact div_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg hx _)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    calc
      (⌈x ^ (a * x)⌉₊ : ℝ) / x ^ (b * x) ≤
          (2 * x ^ (a * x)) / x ^ (b * x) :=
        div_le_div_of_nonneg_right (ceil_rpow_mul_le_two ha hx)
          (Real.rpow_nonneg (le_trans (by norm_num) hx) _)
      _ = 2 * (x ^ (a * x) / x ^ (b * x)) := by ring

theorem tendsto_cutoff_feasibility (G : ℝ) :
    Tendsto (fun x : ℝ =>
      G * (⌈x ^ ((3 / 4 : ℝ) * x)⌉₊ : ℝ) / x ^ ((4 / 5 : ℝ) * x))
      atTop (𝓝 0) := by
  have h := (tendsto_ceil_rpow_mul_ratio (a := (3 / 4 : ℝ))
    (b := (4 / 5 : ℝ)) (by norm_num) (by norm_num)).const_mul G
  simpa only [mul_zero, mul_div_assoc] using h

end InvariantProjection.PowerGaps

end OAI

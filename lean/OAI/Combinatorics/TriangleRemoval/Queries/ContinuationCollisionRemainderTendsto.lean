import Mathlib
import OAI.Combinatorics.TriangleRemoval.Tracking.PrefixDTendstoTop

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

lemma continuation_collision_remainder_tendsto :
    Tendsto (fun n : ℕ => (81920*(3 : ℝ)^49)/prefixD n+8/(n : ℝ)+
      16*(prefixD n/(n : ℝ))) atTop (𝓝 (0 : ℝ)) := by
  have h1 := prefixD_inv_tendsto.const_mul (81920*(3 : ℝ)^49)
  have h2 := tendsto_one_div_atTop_nhds_zero_nat.const_mul (8 : ℝ)
  have h3 := prefixD_div_n_tendsto.const_mul (16 : ℝ)
  simpa only [mul_one_div,add_zero,mul_zero] using (h1.add h2).add h3

theorem goodPrefix_relative_l2 (c C : ℝ) (hc : 0 < c) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      ∀ (G : Graph n), GoodPrefixGraph n c C G →
        pmfMean (finish G) (fun H =>
          ((H.card : ℝ)/((G.card : ℝ)*cavityReference (prefixD n) 1)-1)^2) < δ := by
  intro δ hδ
  let ε := min (δ/10) 1
  have hε : 0 < ε := lt_min (by positivity) zero_lt_one
  have hε1 : ε ≤ 1 := min_le_right _ _
  have hεδ : ε ≤ δ/10 := min_le_left _ _
  have hsmall : 4*ε+ε^2 ≤ δ/2 := by nlinarith [sq_nonneg ε]
  filter_upwards [goodPrefix_relative_l2_bound c C hc hε,
    continuation_collision_remainder_tendsto.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < δ/2))]
      with n hbound hrem
  intro G hG
  exact (hbound G hG).trans_lt (by linarith)

lemma normalization_sq (n : ℕ) : normalization n ^ 2 = (n : ℝ)^3 := by
  unfold normalization
  rw [← Real.rpow_mul_natCast (Nat.cast_nonneg n)]
  norm_num

lemma normalization_pos {n : ℕ} (hn : 0 < n) : 0 < normalization n := by
  exact Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _

lemma sharpConstant_pos : 0 < sharpConstant := by
  unfold sharpConstant
  positivity

lemma sharpConstant_sq : sharpConstant^2 = (1/8 : ℝ) := by
  unfold sharpConstant
  rw [div_pow,mul_pow,Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem prefix_terminal_scale_tendsto :
    Tendsto (fun n => prefixM n*cavityReference (prefixD n) 1/normalization n)
      atTop (𝓝 sharpConstant) := by
  have hinv : Tendsto (fun n => 1 / (4*(1/prefixD n+2))) atTop (𝓝 (1/8 : ℝ)) := by
    have hh := (prefixD_inv_tendsto.add_const (2 : ℝ)).const_mul (4 : ℝ)
    have hh' := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).div
      hh (by norm_num : (4*((0 : ℝ)+2)) ≠ 0)
    change Tendsto (fun n => 1/(4*(1/prefixD n+2))) atTop (𝓝 (1/(4*((0 : ℝ)+2)))) at hh'
    convert hh' using 1
    norm_num
  have hsq : ∀ᶠ n : ℕ in atTop,
      (prefixM n*cavityReference (prefixD n) 1/normalization n)^2 =
        1 / (4*(1/prefixD n+2)) := by
    filter_upwards [prefix_scales_eventually_pos,eventually_ge_atTop (1 : ℕ)] with n hp hn
    have hn0 : (0 : ℝ) < n := by
      exact_mod_cast (show 0 < n by omega)
    have hD0 : 0 < prefixD n := by linarith [hp.2]
    rw [div_pow,mul_pow,normalization_sq,cavityReference_sq hD0.le (by norm_num)]
    simp only [cavityWeight,mul_one]
    unfold prefixM prefixD
    have hp0 := hp.1
    field_simp
    ring
  have hpos : ∀ᶠ n : ℕ in atTop,
      0 ≤ prefixM n*cavityReference (prefixD n) 1/normalization n := by
    filter_upwards [prefix_scales_eventually_pos,eventually_ge_atTop (1 : ℕ)] with n hp hn
    have hn0 : 0 < n := by omega
    have hm0 : 0 < prefixM n := by unfold prefixM; have := hp.1; positivity
    have hq0 : 0 < cavityReference (prefixD n) 1 := cavityReference_pos (by linarith [hp.2]) (by norm_num)
    exact (div_pos (mul_pos hm0 hq0) (normalization_pos hn0)).le
  have hl := Real.continuous_sqrt.continuousAt.tendsto.comp hinv
  have hroot : Real.sqrt (1/8 : ℝ) = sharpConstant := by
    rw [← sharpConstant_sq,Real.sqrt_sq sharpConstant_pos.le]
  rw [hroot] at hl
  apply hl.congr'
  filter_upwards [hsq,hpos] with n he hp
  dsimp only [Function.comp_def]
  rw [← he,Real.sqrt_sq hp]

end SharpTerminalLeave

end

end OAI

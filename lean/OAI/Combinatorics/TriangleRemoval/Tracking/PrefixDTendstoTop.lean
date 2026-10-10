import Mathlib
import OAI.Combinatorics.TriangleRemoval.Tracking.GoodPrefixSurvivalMoments

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

lemma prefixD_tendsto_atTop : Tendsto prefixD atTop atTop := by
  apply tendsto_atTop_mono' atTop
    (show ∀ᶠ n : ℕ in atTop, (n : ℝ)^(1/1000 : ℝ) ≤ prefixD n from
      prefixD_eventual_envelope.mono (fun _ h => h.1))
  exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/1000)).comp
    tendsto_natCast_atTop_atTop

lemma prefixD_inv_tendsto : Tendsto (fun n => 1/prefixD n) atTop (𝓝 (0 : ℝ)) := by
  simpa only [one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp prefixD_tendsto_atTop

lemma prefixD_div_n_tendsto : Tendsto (fun n => prefixD n/(n : ℝ)) atTop (𝓝 (0 : ℝ)) := by
  have hupper : ∀ᶠ n : ℕ in atTop,
      0 ≤ prefixD n/(n : ℝ) ∧ prefixD n/(n : ℝ) ≤ 4*(n : ℝ)^(-(999/1000 : ℝ)) := by
    filter_upwards [prefixD_eventual_envelope,eventually_ge_atTop (1 : ℕ)] with n hn hp
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hp
    have hp0 : 0 ≤ prefixD n := le_trans (Real.rpow_nonneg (Nat.cast_nonneg n) _) hn.1
    refine ⟨div_nonneg hp0 hn0.le,?_⟩
    calc
      _ ≤ (4*(n : ℝ)^(1/1000 : ℝ))/(n : ℝ) := div_le_div_of_nonneg_right hn.2 hn0.le
      _ = _ := by
        have hid : (n : ℝ)^(1/1000 : ℝ)/(n : ℝ) =
            (n : ℝ)^(-(999/1000 : ℝ)) := by
          conv_lhs => rhs; rw [← Real.rpow_one (n : ℝ)]
          rw [← Real.rpow_sub hn0]
          norm_num
        rw [mul_div_assoc,hid]
  have hl := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 999/1000)).comp
    tendsto_natCast_atTop_atTop).const_mul 4
  exact squeeze_zero' (hupper.mono (fun _ h => h.1)) (hupper.mono (fun _ h => h.2))
    (by simpa using hl)

theorem goodPrefix_relative_l2_bound (c C : ℝ) (hc : 0 < c) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (G : Graph n), GoodPrefixGraph n c C G →
      pmfMean (finish G) (fun H =>
        ((H.card : ℝ)/((G.card : ℝ)*cavityReference (prefixD n) 1)-1)^2) ≤
      (81920*(3 : ℝ)^49)/prefixD n+8/(n : ℝ)+16*(prefixD n/(n : ℝ))+
        (4*ε+ε^2) := by
  filter_upwards [goodPrefix_survival_moments c C hc hε,
    prefixD_tendsto_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    prefix_scales_eventually_pos,eventually_ge_atTop (1 : ℕ)] with n hm hD hsc hn
  intro G hG
  have hD0 : 0 < prefixD n := lt_of_lt_of_le zero_lt_one hD
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm0 : 0 < (G.card : ℝ) := by
    rw [hG.2.1]
    unfold prefixM
    have := hsc.1
    positivity
  have hne : G.Nonempty := Finset.card_pos.mp (by exact_mod_cast hm0)
  obtain ⟨h1,h2⟩ := hm G hG hne
  rw [terminal_first_focus_moment] at h1
  rw [terminal_second_focus_moment] at h2
  let q := cavityReference (prefixD n) 1
  let A := (1+2*prefixD n)^48/prefixD n^50
  have hq : 0 < q := cavityReference_pos hD0 (by norm_num)
  have hq1 : q ≤ 1 := cavityReference_le_one hD0 (by norm_num)
  have hq2 : q^2 = 1/(1+2*prefixD n) := by
    dsimp only [q]
    rw [cavityReference_sq hD0.le (by norm_num)]
    simp only [cavityWeight,mul_one]
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hAbound : A ≤ (3 : ℝ)^48/prefixD n^2 := collision_power_48_bound hD
  have h1' : |pmfMean (finish G) (fun H => (H.card : ℝ))/(G.card : ℝ)-q| ≤
      8192*A+ε*q := by simpa only [A,q,mul_div_assoc] using h1
  have h2' : |pmfMean (finish G) (fun H => (H.card : ℝ)^2)/(G.card : ℝ)^2-q^2| ≤
      65536*A+8/(n : ℝ)+(2*ε+ε^2)*q^2 := by
    simpa only [A,q,mul_div_assoc] using h2
  have heq : pmfMean (finish G) (fun H =>
      ((H.card : ℝ)/((G.card : ℝ)*q)-1)^2) =
      (pmfMean (finish G) (fun H => (H.card : ℝ)^2)/(G.card : ℝ)^2-q^2)/q^2 -
      2*(pmfMean (finish G) (fun H => (H.card : ℝ))/(G.card : ℝ)-q)/q := by
    rw [pmfMean_sq_sub]
    simp_rw [div_pow,div_eq_mul_inv,pmfMean_mul_const]
    field_simp
    ring
  have hb : pmfMean (finish G) (fun H =>
      ((H.card : ℝ)/((G.card : ℝ)*q)-1)^2) ≤
      (81920*A+8/(n : ℝ))/q^2+(4*ε+ε^2) := by
    rw [heq]
    have hfirst := (abs_le.mp h1').1
    have hsecond := (abs_le.mp h2').2
    have haux : (2*(8192*A+ε*q))/q ≤ (16384*A)/q^2+2*ε := by
      calc
        _ = 16384*A/q+2*ε := by field_simp; ring
        _ ≤ _ := add_le_add
          (div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hq)
            (by nlinarith : q^2 ≤ q)) le_rfl
    have hlinear : -2*(pmfMean (finish G) (fun H => (H.card : ℝ))/(G.card : ℝ)-q)/q ≤
        (2*(8192*A+ε*q))/q :=
      div_le_div_of_nonneg_right (by linarith) hq.le
    calc
      _ ≤ (65536*A+8/(n : ℝ)+(2*ε+ε^2)*q^2)/q^2 +
          (2*(8192*A+ε*q))/q := by
        apply add_le_add
        · exact div_le_div_of_nonneg_right hsecond (sq_nonneg q)
        · simpa only [neg_mul,neg_div] using hlinear
      _ ≤ (65536*A+8/(n : ℝ)+(2*ε+ε^2)*q^2)/q^2+
          ((16384*A)/q^2+2*ε) := add_le_add le_rfl haux
      _ = _ := by field_simp; ring
  apply hb.trans
  rw [hq2]
  have hDA : (81920*A)*(1+2*prefixD n) ≤ (81920*(3 : ℝ)^49)/prefixD n := by
    calc
      _ ≤ (81920*((3 : ℝ)^48/prefixD n^2))*(3*prefixD n) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hAbound (by norm_num))
          (by linarith) (by positivity) (by positivity)
      _ = _ := by rw [show 49 = 48+1 by norm_num,pow_add,pow_one]; field_simp
  have hraw : (81920*A+8/(n : ℝ))/(1/(1+2*prefixD n)) =
      (81920*A)*(1+2*prefixD n)+8/(n : ℝ)+16*(prefixD n/(n : ℝ)) := by
    field_simp
    ring
  rw [hraw]
  linarith

end SharpTerminalLeave

end

end OAI

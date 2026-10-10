import Mathlib
import OAI.Probability.SKBarriers.Coverage.CoverageScale
import OAI.Probability.SKBarriers.Dynamics.GreedyNumerics

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open Classical MeasureTheory Filter Set
namespace SK.Analytic

 theorem greedyBlockCount_eventual {B : ℕ} (hB : 0<B) {t : ℝ} (ht : 0<t) :
    ∀ᶠ n : ℕ in atTop,0<greedyBlockCount B t n ∧
      (t/(8*B))*levelLogScale n/2≤(greedyBlockCount B t n:ℝ) := by
  have hc : 0<t/(8*B) := by positivity
  have H := stretchedLogScale_tendsto.const_mul_atTop hc
  filter_upwards [H.eventually_ge_atTop 2] with n hn
  change 2≤(t/(8*B))*levelLogScale n at hn
  constructor
  · exact Nat.floor_pos.mpr (by linarith only [hn])
  · have h := Nat.lt_floor_add_one ((t/(8*B))*levelLogScale n)
    change _≤(⌊(t/(8*B))*levelLogScale n⌋₊:ℝ)
    linarith only [h,hn]

 theorem greedyScale_eventual {B H : ℕ} (hB : 0<B) (hHB : H<B) {t b b' q : ℝ}
    (ht : 0<t) (hb : 0<b) (hpack : ⌈2/b^2⌉₊≤H) (hpack' : 3*t<b^2/2)
    (hcut : 3*t<b) (hcut' : 2*t<b') (hh : 2*t<q) :
    ∀ᶠ n : ℕ in atTop,GreedyScaleBounds n B H (B*greedyBlockCount B t n) t (levelRho n) (2/(n:ℝ)) b b' q := by
  have HF := greedySlack_tendsto t
  have HFq := HF.const_mul 2
  have HW := levelRho_tendsto.pow 8
  filter_upwards [eventually_gt_atTop (0:ℕ),greedyBlockCount_eventual hB ht,
    levelRho_tendsto.eventually_lt_const zero_lt_one,
    (greedySlack_div_tendsto t).eventually_lt_const zero_lt_one,
    HF.eventually_lt_const ht,HF.eventually_lt_const (sub_pos.mpr hcut'),
    HFq.eventually_lt_const (by simpa only [mul_zero] using sub_pos.mpr hh),
    HW.eventually_lt_const (by simpa only [zero_pow (by decide : 8≠0)] using half_pos ht)] with n hn hs hρ1 hF hFt hFb hFq hW
  apply greedyScale_of_slack hn hB hHB hs.1 hpack ht hb hpack' hcut (levelRho_pos hn) hρ1
    (levelRho_eta hn) (levelRho_inv hn) (greedyBlockCount_upper hn hB ht)
  · exact (div_lt_one (pow_pos (levelRho_pos hn) 8)).mp hF
  · exact hFt
  · linarith only [hFb]
  · linarith only [hFq]
  · exact hW

 theorem greedy_grid_mass_bound {n B : ℕ} (hn : 0<n) (hB : 0<B) {t : ℝ} (ht : 0<t) :
    (B*greedyBlockCount B t n:ℕ)*((4*(levelRho n)^8/(levelRho n)+1/(n:ℝ))/(levelRho n)^4) ≤
      (t/8)*(4*(levelRho n)^2+(levelRho n)^9995) := by
  have hp := greedyBlockCount_upper hn hB ht
  have he : (B*greedyBlockCount B t n:ℕ)*((4*(levelRho n)^8/(levelRho n)+1/(n:ℝ))/(levelRho n)^4)=
      ((B*greedyBlockCount B t n:ℕ)*levelRho n)*(4*(levelRho n)^2+(levelRho n)^9995) := by
    rw [levelRho_inv hn]
    have hρ := (levelRho_pos hn).ne'
    field_simp
  rw [he]
  exact mul_le_mul_of_nonneg_right hp (by have := (levelRho_pos hn).le; positivity)

 theorem greedy_grid_window_bound {n B : ℕ} (hn : 0<n) (hB : 0<B) {t : ℝ} (ht : 0<t) :
    2*(6*(B*greedyBlockCount B t n:ℕ)*(levelRho n)^20)/(levelRho n)+1/(n:ℝ) ≤
      (3*t/2)*(levelRho n)^18+(levelRho n)^10000 := by
  have hp := greedyBlockCount_upper hn hB ht
  rw [levelRho_inv hn]
  have he : 2*(6*(B*greedyBlockCount B t n:ℕ)*(levelRho n)^20)/(levelRho n)=
      ((B*greedyBlockCount B t n:ℕ)*levelRho n)*(12*(levelRho n)^18) := by
    have hρ := (levelRho_pos hn).ne'
    field_simp
    ring
  rw [he]
  have h := mul_le_mul_of_nonneg_right hp (show 0≤12*(levelRho n)^18 by positivity)
  nlinarith only [h]

 theorem horizon_size_bound {L : ℝ} (hL : 0≤L) : (⌈Real.exp (2*L)⌉₊:ℝ)+1≤3*Real.exp (2*L) := by
  have hc := Nat.ceil_lt_add_one (Real.exp_pos (2*L)).le
  have hh : 1≤Real.exp (2*L) := Real.one_le_exp_iff.mpr (by positivity)
  linarith only [hc,hh]

 theorem greedy_count_eventual {B : ℕ} (hB : 0<B) {t : ℝ} (ht : 0<t) :
    ∀ᶠ n : ℕ in atTop,∀m≤⌈Real.exp (2*levelLogScale n)⌉₊,
      (B*greedyBlockCount B t n:ℕ)*((4*(levelRho n)^8/(levelRho n)+1/(n:ℝ))/(levelRho n)^4)+
        (m+1)*(2*(6*(B*greedyBlockCount B t n:ℕ)*(levelRho n)^20)/(levelRho n)+1/(n:ℝ))^(greedyBlockCount B t n)<1 := by
  let c : ℝ := t/(8*B)
  have hc : 0<c := by dsimp only [c]; positivity
  have HM : Tendsto (fun n => (t/8)*(4*(levelRho n)^2+(levelRho n)^9995)) atTop (𝓝 0) := by
    convert (((levelRho_tendsto.pow 2).const_mul 4).add (levelRho_tendsto.pow 9995)).const_mul (t/8) using 1
    norm_num
  have HW : Tendsto (fun n => (3*t/2)*(levelRho n)^18+(levelRho n)^10000) atTop (𝓝 0) := by
    convert ((levelRho_tendsto.pow 18).const_mul (3*t/2)).add (levelRho_tendsto.pow 10000) using 1
    norm_num
  have HE : Tendsto (fun n => 3*Real.exp (-2*levelLogScale n)) atTop (𝓝 0) := by
    have H := (Real.tendsto_exp_atBot.comp (stretchedLogScale_tendsto.const_mul_atTop_of_neg (by norm_num : (-2:ℝ)<0))).const_mul 3
    simpa only [mul_zero,levelLogScale,Function.comp_apply] using H
  filter_upwards [eventually_gt_atTop (0:ℕ),greedyBlockCount_eventual hB ht,
    HM.eventually_lt_const (by norm_num : (0:ℝ)<1/2),
    HW.eventually_le_const (Real.exp_pos (-8/c)),HE.eventually_lt_const (by norm_num : (0:ℝ)<1/2)] with n hn hs hm hw he
  intro m hmn
  have hρ := levelRho_pos hn
  let γ : ℝ := 2*(6*(B*greedyBlockCount B t n:ℕ)*(levelRho n)^20)/(levelRho n)+1/(n:ℝ)
  have hγ : 0≤γ := by dsimp only [γ]; positivity
  have hγ' : γ≤Real.exp (-8/c) := (greedy_grid_window_bound hn hB ht).trans hw
  have hpow : γ^(greedyBlockCount B t n)≤Real.exp (-4*levelLogScale n) := by
    calc
      _ ≤ (Real.exp (-8/c))^(greedyBlockCount B t n) := pow_le_pow_left₀ hγ hγ' _
      _ = Real.exp ((greedyBlockCount B t n:ℝ)*(-8/c)) := (Real.exp_nat_mul _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by
        have hh := mul_le_mul_of_nonpos_right hs.2 (show -8/c≤0 from div_nonpos_of_nonpos_of_nonneg (by norm_num) hc.le)
        change _≤(c*levelLogScale n/2)*(-8/c) at hh
        have hz : (c*levelLogScale n/2)*(-8/c)=-4*levelLogScale n := by field_simp; ring
        rw [hz] at hh
        exact hh)
  have hM : (m:ℝ)+1≤3*Real.exp (2*levelLogScale n) := by
    have hk : (m:ℝ)≤⌈Real.exp (2*levelLogScale n)⌉₊ := by exact_mod_cast hmn
    exact (add_le_add hk (le_refl (1:ℝ))).trans (horizon_size_bound (L:=levelLogScale n) (by unfold levelLogScale; positivity))
  have hprod : ((m:ℝ)+1)*γ^(greedyBlockCount B t n)≤3*Real.exp (-2*levelLogScale n) := by
    calc
      _ ≤ (3*Real.exp (2*levelLogScale n))*Real.exp (-4*levelLogScale n) := mul_le_mul hM hpow (by positivity) (by positivity)
      _ = _ := by rw [mul_assoc,← Real.exp_add]; congr 2; ring
  have hb := greedy_grid_mass_bound hn hB ht
  linarith only [hb,hm,hprod,he]

end SK.Analytic

end
end

end OAI

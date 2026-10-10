import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Order.Filter.AtTopBot.Group
import OAI.NumberTheory.Catalan.Energy.BarrierChebyshevLogFormula
import OAI.NumberTheory.Catalan.Energy.BarrierComplexOctantRange
import OAI.NumberTheory.Catalan.Energy.BarrierGlobalMaxReduction
import OAI.NumberTheory.Catalan.Energy.BarrierPowerLogFormula
import OAI.NumberTheory.Catalan.Energy.BarrierTrialPowerHasSum
import OAI.NumberTheory.Catalan.Energy.BarrierTrialUHasSum
import OAI.NumberTheory.Catalan.Estimates.RealEnergySupDual
import OAI.NumberTheory.Catalan.SecondBarrier.BarrierCaseTwoXRootSimplicity

namespace OAI

noncomputable section

namespace InternalCatalan

section

def barrierCase2X (x : ℝ) : ℝ :=
  realEnergyField 2 x + barrierLambda2 * realEnergyCaseField x -
    4 * barrierTrialT barrierP2 x - barrierTrialS barrierV2 x

def barrierCase2Y (x : ℝ) : ℝ :=
  realEnergyColumnField x + 2 * barrierTrialT barrierV2 x

theorem barrierCase2X_eq (x : ℝ) :
    barrierCase2X x = realEnergyField 2 x -
      4 * barrierTrialT barrierP2 x - barrierTrialS barrierV2 x := by
  simp only [barrierCase2X, barrierLambda2, zero_mul, add_zero]

private theorem barrier_case2_p_tail_base_lt_one :
    ∀ zr ∈ barrierP2Tail, ‖zr.1‖ < 1 := by
  intro zr hzr
  exact lt_of_le_of_lt (barrierP2_tail_norm_bounds zr hzr).1 (by norm_num)

private theorem barrier_case2_v_tail_base_lt_one :
    ∀ zr ∈ barrierV2Tail, ‖zr.1‖ < 1 := by
  intro zr hzr
  exact lt_of_le_of_lt (barrierV2_tail_norm_bounds zr hzr).1 (by norm_num)

private theorem barrier_case2_pT_hasDerivAt {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (barrierTrialT barrierP2)
      ((barrierFiniteUDerivative barrierP2Finite).eval₂ (Rat.castHom ℝ) x +
        (barrierP2Tail.map (fun zr : ℂ × ℂ =>
          zr.2 * zr.1 / barrierTailQuadraticDen zr.1 x)).sum.re) x := by
  have hg := barrierTrialT_hasDerivAt_series barrierP2 barrier_trials_abs_summable.1
    barrier_trials_weighted_abs_summable.1 hx
  have hs := barrierTrial_U_hasSum barrierP2Finite barrierP2Tail
    barrier_case2_p_tail_base_lt_one (abs_le.mpr ⟨hx.1.le, hx.2.le⟩)
  apply hg.congr_deriv
  exact hs.tsum_eq

private theorem barrier_case2_vT_hasDerivAt {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (barrierTrialT barrierV2)
      ((barrierFiniteUDerivative barrierV2Finite).eval₂ (Rat.castHom ℝ) x +
        (barrierV2Tail.map (fun zr : ℂ × ℂ =>
          zr.2 * zr.1 / barrierTailQuadraticDen zr.1 x)).sum.re) x := by
  have hg := barrierTrialT_hasDerivAt_series barrierV2 barrier_trials_abs_summable.2.1
    barrier_trials_weighted_abs_summable.2.1 hx
  have hs := barrierTrial_U_hasSum barrierV2Finite barrierV2Tail
    barrier_case2_v_tail_base_lt_one (abs_le.mpr ⟨hx.1.le, hx.2.le⟩)
  apply hg.congr_deriv
  exact hs.tsum_eq

private theorem barrier_case2_vS_hasDerivAt {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (barrierTrialS barrierV2)
      ((barrierFinitePowerDerivative barrierV2Finite).eval₂ (Rat.castHom ℝ) x +
        (barrierV2Tail.map (fun zr : ℂ × ℂ =>
          zr.2 * zr.1 / barrierTailLinearDen zr.1 x)).sum.re) x := by
  have hg := barrierTrialS_hasDerivAt_series barrierV2 barrier_trials_abs_summable.2.1 hx
  have hs := barrierTrial_power_hasSum barrierV2Finite barrierV2Tail
    barrier_case2_v_tail_base_lt_one (abs_le.mpr ⟨hx.1.le, hx.2.le⟩)
  apply hg.congr_deriv
  exact hs.tsum_eq

private theorem barrier_realEnergyField_two_hasDerivAt {x : ℝ}
    (h0 : x ≠ 0) (h1 : x ≠ 1) :
    HasDerivAt (realEnergyField 2)
      ((19 / 48 : ℝ) / x - (1 / 12 : ℝ) / (1 - x) -
        (65 / 24 : ℝ) * x / (1 + x ^ 2)) x := by
  have ho : 1 - x ≠ 0 := sub_ne_zero.mpr h1.symm
  have hd : 1 + x ^ 2 ≠ 0 := ne_of_gt (by positivity : (0 : ℝ) < 1 + x ^ 2)
  have hl0 : HasDerivAt (fun y : ℝ => Real.log |y|) (1 / x) x := by
    simpa only [Real.log_abs, one_div] using Real.hasDerivAt_log h0
  have hl1 : HasDerivAt (fun y : ℝ => Real.log (1 - y)) (-1 / (1 - x)) x :=
    ((hasDerivAt_id x).const_sub (1 : ℝ)).log ho
  have hp : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x).const_add (1 : ℝ)
  have hh := ((hl0.const_mul (19 / 48 : ℝ)).add
    (hl1.const_mul (1 / 12 : ℝ))).sub
    ((hp.log hd).const_mul ((2 : ℝ) / 2 + 17 / 48))
  unfold realEnergyField
  apply hh.congr_deriv
  field_simp [h0, ho, hd]
  ring

private theorem barrier_case2_column_hasDerivAt {x : ℝ}
    (h0 : x ≠ 0) (h1 : x ≠ 1) :
    HasDerivAt realEnergyColumnField
      ((7 / 48 : ℝ) / x - (1 / 12 : ℝ) / (1 - x)) x := by
  have ho : 1 - x ≠ 0 := sub_ne_zero.mpr h1.symm
  have hl0 : HasDerivAt Real.log (1 / x) x := by
    simpa only [one_div] using Real.hasDerivAt_log h0
  have hl1 : HasDerivAt (fun y : ℝ => Real.log (1 - y)) (-1 / (1 - x)) x :=
    ((hasDerivAt_id x).const_sub (1 : ℝ)).log ho
  have hh := (hl0.const_mul (7 / 48 : ℝ)).add (hl1.const_mul (1 / 12 : ℝ))
  unfold realEnergyColumnField
  apply hh.congr_deriv
  field_simp [h0, ho]
  ring

theorem barrierCase2X_hasDerivAt {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) (h0 : x ≠ 0) :
    HasDerivAt barrierCase2X (barrierCase2XDerivativeFormula x) x := by
  have hh := ((barrier_realEnergyField_two_hasDerivAt h0 (ne_of_lt hx.2)).sub
    ((barrier_case2_pT_hasDerivAt hx).const_mul (4 : ℝ))).sub
    (barrier_case2_vS_hasDerivAt hx)
  have hfun : barrierCase2X = (fun y : ℝ => realEnergyField 2 y -
      4 * barrierTrialT barrierP2 y - barrierTrialS barrierV2 y) :=
    funext barrierCase2X_eq
  rw [hfun]
  apply hh.congr_deriv
  unfold barrierCase2XDerivativeFormula
  rfl

theorem barrierCase2Y_hasDerivAt {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt barrierCase2Y (barrierCase2YDerivativeFormula x) x := by
  have hx' : x ∈ Set.Ioo (-1 : ℝ) 1 := ⟨lt_trans (by norm_num) hx.1, hx.2⟩
  have hh := (barrier_case2_column_hasDerivAt (ne_of_gt hx.1) (ne_of_lt hx.2)).add
    ((barrier_case2_vT_hasDerivAt hx').const_mul (2 : ℝ))
  unfold barrierCase2Y
  apply hh.congr_deriv
  unfold barrierCase2YDerivativeFormula
  rfl

end

section

open Set Filter
open scoped Topology

private theorem barrier2_atBot_add_finite {l : Filter ℝ} {f g : ℝ → ℝ} {c : ℝ}
    (hf : Tendsto f l atBot) (hg : Tendsto g l (𝓝 c)) :
    Tendsto (fun x => f x + g x) l atBot := by
  have hb : ∀ᶠ x in l, g x ≤ c + 1 :=
    ((tendsto_order.mp hg).2 (c + 1) (by linarith)).mono (fun _ hx => hx.le)
  exact tendsto_atBot_add_right_of_ge' l (c + 1) hf hb

private theorem barrier2_log_one_sub_tendsto :
    Tendsto (fun x : ℝ => Real.log (1 - x)) (𝓝[<] 1) atBot := by
  have hc : Continuous (fun x : ℝ => 1 - x) := continuous_const.sub continuous_id
  have ht : Tendsto (fun x : ℝ => 1 - x) (𝓝[<] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using (hc.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      change x < 1 at hx
      change 0 < 1 - x
      exact sub_pos.mpr hx
  exact Real.tendsto_log_nhdsGT_zero.comp ht

private theorem barrier2_continuousOn_tendsto_one_left {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) :
    Tendsto f (𝓝[<] 1) (𝓝 (f 1)) := by
  have ht : Tendsto (fun x : ℝ => x) (𝓝[<] 1) (𝓝[Icc (-1) 1] 1) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨nhdsWithin_le_nhds, ?_⟩
    have ha : ∀ᶠ x : ℝ in 𝓝[<] 1, -1 < x :=
      (eventually_gt_nhds (by norm_num : (-1 : ℝ) < 1)).filter_mono
        nhdsWithin_le_nhds
    filter_upwards [ha, self_mem_nhdsWithin] with x hx hx1
    exact ⟨hx.le, le_of_lt hx1⟩
  exact (hf 1 (by norm_num)).tendsto.comp ht

private theorem barrier2_continuousOn_continuousAt_zero {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (-1 : ℝ) 1)) : ContinuousAt f 0 :=
  (hf 0 (by norm_num)).continuousAt (Icc_mem_nhds (by norm_num) (by norm_num))

private def barrierCase2XRegular (x : ℝ) : ℝ :=
  -(65 / 48 : ℝ) * Real.log (1 + x ^ 2) -
    4 * barrierTrialT barrierP2 x - barrierTrialS barrierV2 x

private theorem barrierCase2XRegular_continuousOn :
    ContinuousOn barrierCase2XRegular (Icc (-1 : ℝ) 1) := by
  have hl : Continuous (fun x : ℝ => Real.log (1 + x ^ 2)) := by
    apply Continuous.log (continuous_const.add (continuous_id.pow 2))
    intro x
    change 1 + x ^ 2 ≠ 0
    exact ne_of_gt (by positivity : (0 : ℝ) < 1 + x ^ 2)
  have ht := barrierTrialT_continuousOn barrierP2 barrier_trials_abs_summable.1
  have hs := barrierTrialS_continuousOn barrierV2 barrier_trials_abs_summable.2.1
  exact ((hl.continuousOn.const_mul (-(65 / 48 : ℝ))).sub (ht.const_mul 4)).sub hs

private theorem barrierCase2V2T_continuousOn :
    ContinuousOn (barrierTrialT barrierV2) (Icc (-1 : ℝ) 1) :=
  barrierTrialT_continuousOn barrierV2 barrier_trials_abs_summable.2.1

private theorem barrierCase2X_split (x : ℝ) :
    barrierCase2X x = (19 / 48 : ℝ) * Real.log |x| +
      (1 / 12 : ℝ) * Real.log (1 - x) + barrierCase2XRegular x := by
  rw [barrierCase2X_eq]
  unfold realEnergyField barrierCase2XRegular
  ring

private theorem barrierCase2X_zero_remainder :
    ContinuousAt (fun x : ℝ => (1 / 12 : ℝ) * Real.log (1 - x) +
      barrierCase2XRegular x) 0 := by
  have hl : ContinuousAt (fun x : ℝ => Real.log (1 - x)) 0 :=
    (continuousAt_const.sub continuousAt_id).log (by norm_num)
  exact (hl.const_mul (1 / 12 : ℝ)).add
    (barrier2_continuousOn_continuousAt_zero barrierCase2XRegular_continuousOn)

theorem barrierCase2X_tendsto_zero_left :
    Tendsto barrierCase2X (𝓝[<] 0) atBot := by
  have hl : Tendsto (fun x : ℝ => (19 / 48 : ℝ) * Real.log |x|)
      (𝓝[<] 0) atBot := by
    simpa only [Real.log_abs] using
      (Tendsto.const_mul_atBot (by norm_num : (0 : ℝ) < 19 / 48)
        Real.tendsto_log_nhdsLT_zero)
  have hh := barrier2_atBot_add_finite hl
    (barrierCase2X_zero_remainder.tendsto.mono_left nhdsWithin_le_nhds)
  convert hh using 1
  funext x
  rw [barrierCase2X_split]
  ring

theorem barrierCase2X_tendsto_zero_right :
    Tendsto barrierCase2X (𝓝[>] 0) atBot := by
  have hl : Tendsto (fun x : ℝ => (19 / 48 : ℝ) * Real.log |x|)
      (𝓝[>] 0) atBot := by
    simpa only [Real.log_abs] using
      (Tendsto.const_mul_atBot (by norm_num : (0 : ℝ) < 19 / 48)
        Real.tendsto_log_nhdsGT_zero)
  have hh := barrier2_atBot_add_finite hl
    (barrierCase2X_zero_remainder.tendsto.mono_left nhdsWithin_le_nhds)
  convert hh using 1
  funext x
  rw [barrierCase2X_split]
  ring

theorem barrierCase2X_tendsto_one_left :
    Tendsto barrierCase2X (𝓝[<] 1) atBot := by
  have hl := Tendsto.const_mul_atBot (by norm_num : (0 : ℝ) < 1 / 12)
    barrier2_log_one_sub_tendsto
  have hc : ContinuousAt (fun x : ℝ => Real.log |x|) 1 := by
    simpa only [Real.log_abs] using (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0))
  have hr := ((hc.tendsto.mono_left nhdsWithin_le_nhds).const_mul (19 / 48 : ℝ)).add
    (barrier2_continuousOn_tendsto_one_left barrierCase2XRegular_continuousOn)
  have hh := barrier2_atBot_add_finite hl hr
  convert hh using 1
  funext x
  rw [barrierCase2X_split]
  ring

theorem barrierCase2Y_tendsto_zero_right :
    Tendsto barrierCase2Y (𝓝[>] 0) atBot := by
  have hl := Tendsto.const_mul_atBot (by norm_num : (0 : ℝ) < 7 / 48)
    Real.tendsto_log_nhdsGT_zero
  have hr : ContinuousAt (fun x : ℝ => (1 / 12 : ℝ) * Real.log (1 - x) +
      2 * barrierTrialT barrierV2 x) 0 := by
    have hlog : ContinuousAt (fun x : ℝ => Real.log (1 - x)) 0 :=
      (continuousAt_const.sub continuousAt_id).log (by norm_num)
    exact (hlog.const_mul (1 / 12 : ℝ)).add
      ((barrier2_continuousOn_continuousAt_zero barrierCase2V2T_continuousOn).const_mul 2)
  have hh := barrier2_atBot_add_finite hl (hr.tendsto.mono_left nhdsWithin_le_nhds)
  convert hh using 1
  funext x
  unfold barrierCase2Y realEnergyColumnField
  ring

theorem barrierCase2Y_tendsto_one_left :
    Tendsto barrierCase2Y (𝓝[<] 1) atBot := by
  have hl := Tendsto.const_mul_atBot (by norm_num : (0 : ℝ) < 1 / 12)
    barrier2_log_one_sub_tendsto
  have hlog := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[<] (1 : ℝ) ≤ 𝓝 1)
  have hr := (hlog.const_mul (7 / 48 : ℝ)).add
    ((barrier2_continuousOn_tendsto_one_left barrierCase2V2T_continuousOn).const_mul 2)
  have hh := barrier2_atBot_add_finite hl hr
  convert hh using 1
  funext x
  unfold barrierCase2Y realEnergyColumnField
  ring

private theorem barrierCase2X_continuousWithinAt {x : ℝ}
    (hx : x ∈ Icc (-1 : ℝ) 1) (h0 : x ≠ 0) (h1 : x ≠ 1) :
    ContinuousWithinAt barrierCase2X (Icc (-1 : ℝ) 1) x := by
  have hlog : ContinuousAt (fun y : ℝ => Real.log |y|) x := by
    simpa only [Real.log_abs] using Real.continuousAt_log h0
  have hlog1 : ContinuousAt (fun y : ℝ => Real.log (1 - y)) x :=
    (continuousAt_const.sub continuousAt_id).log (sub_ne_zero.mpr (Ne.symm h1))
  have hh := ((hlog.continuousWithinAt.const_mul (19 / 48 : ℝ)).add
    (hlog1.continuousWithinAt.const_mul (1 / 12 : ℝ))).add
    (barrierCase2XRegular_continuousOn x hx)
  convert hh using 1
  funext y
  exact barrierCase2X_split y

theorem barrierCase2X_continuousOn_negative :
    ContinuousOn barrierCase2X (Ico (-1 : ℝ) 0) := by
  intro x hx
  apply (barrierCase2X_continuousWithinAt
    ⟨hx.1, by linarith [hx.2]⟩ (ne_of_lt hx.2) (by linarith [hx.2])).mono
  intro y hy
  exact ⟨hy.1, by linarith [hy.2]⟩

theorem barrierCase2X_continuousOn_positive :
    ContinuousOn barrierCase2X (Ioo (0 : ℝ) 1) := by
  intro x hx
  apply (barrierCase2X_continuousWithinAt
    ⟨by linarith [hx.1], hx.2.le⟩ (ne_of_gt hx.1) (ne_of_lt hx.2)).mono
  intro y hy
  exact ⟨by linarith [hy.1], hy.2.le⟩

theorem barrierCase2Y_continuousOn :
    ContinuousOn barrierCase2Y (Ioo (0 : ℝ) 1) := by
  intro x hx
  have hlog : ContinuousWithinAt Real.log (Ioo (0 : ℝ) 1) x :=
    (Real.continuousAt_log (ne_of_gt hx.1)).continuousWithinAt
  have hlog1 : ContinuousWithinAt (fun y : ℝ => Real.log (1 - y)) (Ioo 0 1) x :=
    ((continuousAt_const.sub continuousAt_id).log
      (sub_ne_zero.mpr (Ne.symm (ne_of_lt hx.2)))).continuousWithinAt
  have ht : ContinuousWithinAt (barrierTrialT barrierV2) (Ioo (0 : ℝ) 1) x := by
    apply (barrierCase2V2T_continuousOn x ⟨by linarith [hx.1], hx.2.le⟩).mono
    intro y hy
    exact ⟨by linarith [hy.1], hy.2.le⟩
  exact ((hlog.const_mul (7 / 48 : ℝ)).add (hlog1.const_mul (1 / 12 : ℝ))).add
    (ht.const_mul 2)

end

section
open scoped BigOperators

def barrierCase2XPLogTerm (x : ℝ) (zr : ℂ × ℂ) : ℝ :=
  (2 * zr.2 * Complex.log (1 - 2 * (x : ℂ) * zr.1 + zr.1 ^ 2)).re

def barrierCase2XVLogTerm (x : ℝ) (zr : ℂ × ℂ) : ℝ :=
  (zr.2 * Complex.log (1 - (x : ℂ) * zr.1)).re

def barrierCase2YVLogTerm (x : ℝ) (zr : ℂ × ℂ) : ℝ :=
  ((-1 : ℂ) * zr.2 * Complex.log (1 - 2 * (x : ℂ) * zr.1 + zr.1 ^ 2)).re

def barrierCase2XRat (x : ℚ) : ℚ :=
  -4 * barrierFiniteTRat barrierP2Finite x - barrierFiniteSRat barrierV2Finite x

def barrierCase2YRat (x : ℚ) : ℚ :=
  2 * barrierFiniteTRat barrierV2Finite x

private theorem barrierFiniteT_sum_cast (cs : List ℤ) (x : ℚ) :
    (∑ k ∈ Finset.range cs.length, ((cs.getD k 0 : ℝ) / 100000000) *
      (Polynomial.Chebyshev.T ℝ ((k + 1 : ℕ) : ℤ)).eval (x : ℝ) /
        ((k + 1 : ℕ) : ℝ)) = ((barrierFiniteTRat cs x : ℚ) : ℝ) := by
  rw [← barrierTrialT_nil_eq_sum cs (x : ℝ), barrierTrialT_nil_eval_rat]

private theorem barrierFiniteS_sum_cast (cs : List ℤ) (x : ℚ) :
    (∑ k ∈ Finset.range cs.length, ((cs.getD k 0 : ℝ) / 100000000) *
      (x : ℝ) ^ (k + 1) / ((k + 1 : ℕ) : ℝ)) =
      ((barrierFiniteSRat cs x : ℚ) : ℝ) := by
  rw [← barrierTrialS_nil_eq_sum cs (x : ℝ), barrierTrialS_nil_eval_rat]

private theorem barrierList_scaled_re_sum {α : Type*} (l : List α)
    (f : α → ℂ) (a : ℝ) :
    a * (l.map f).sum.re = (l.map (fun z => ((a : ℂ) * f z).re)).sum := by
  induction l with
  | nil => simp
  | cons z l ih =>
      simp only [List.map_cons, List.sum_cons, Complex.add_re]
      rw [← ih]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      ring

theorem barrierCase2X_eval_rat (x : ℚ) (hx : |(x : ℝ)| ≤ 1) :
    barrierCase2X (x : ℝ) =
      (19 / 48 : ℝ) * Real.log |(x : ℝ)| +
        (1 / 12 : ℝ) * Real.log (1 - (x : ℝ)) -
        (65 / 48 : ℝ) * Real.log (1 + (x : ℝ) ^ 2) +
        ((barrierCase2XRat x : ℚ) : ℝ) +
        (barrierP2Tail.map (barrierCase2XPLogTerm (x : ℝ))).sum +
        (barrierV2Tail.map (barrierCase2XVLogTerm (x : ℝ))).sum := by
  have hp : 2 * (barrierP2Tail.map (fun zr : ℂ × ℂ =>
      zr.2 * Complex.log (1 - 2 * (x : ℂ) * zr.1 + zr.1 ^ 2))).sum.re =
      (barrierP2Tail.map (barrierCase2XPLogTerm (x : ℝ))).sum := by
    unfold barrierCase2XPLogTerm
    simpa [barrierCase2XPLogTerm, mul_assoc] using barrierList_scaled_re_sum
      barrierP2Tail (fun zr : ℂ × ℂ =>
        zr.2 * Complex.log (1 - 2 * (x : ℂ) * zr.1 + zr.1 ^ 2)) 2
  have hv : (barrierV2Tail.map (fun zr : ℂ × ℂ =>
      zr.2 * Complex.log (1 - (x : ℂ) * zr.1))).sum.re =
      (barrierV2Tail.map (barrierCase2XVLogTerm (x : ℝ))).sum := by
    unfold barrierCase2XVLogTerm
    simpa [barrierCase2XVLogTerm] using barrierList_scaled_re_sum
      barrierV2Tail (fun zr : ℂ × ℂ => zr.2 * Complex.log (1 - (x : ℂ) * zr.1)) 1
  unfold barrierCase2X
  rw [barrierP2_T_eq_finite_log hx, barrierV2_S_eq_finite_log hx,
    barrierFiniteT_sum_cast, barrierFiniteS_sum_cast, ← hp, ← hv]
  unfold realEnergyField barrierLambda2 barrierCase2XRat
  push_cast
  ring

theorem barrierCase2Y_eval_rat (x : ℚ) (hx : |(x : ℝ)| ≤ 1) :
    barrierCase2Y (x : ℝ) =
      (7 / 48 : ℝ) * Real.log (x : ℝ) +
        (1 / 12 : ℝ) * Real.log (1 - (x : ℝ)) +
        ((barrierCase2YRat x : ℚ) : ℝ) +
        (barrierV2Tail.map (barrierCase2YVLogTerm (x : ℝ))).sum := by
  have hv : (-1 : ℝ) * (barrierV2Tail.map (fun zr : ℂ × ℂ =>
      zr.2 * Complex.log (1 - 2 * (x : ℂ) * zr.1 + zr.1 ^ 2))).sum.re =
      (barrierV2Tail.map (barrierCase2YVLogTerm (x : ℝ))).sum := by
    unfold barrierCase2YVLogTerm
    simpa [barrierCase2YVLogTerm, mul_assoc] using barrierList_scaled_re_sum
      barrierV2Tail (fun zr : ℂ × ℂ =>
        zr.2 * Complex.log (1 - 2 * (x : ℂ) * zr.1 + zr.1 ^ 2)) (-1)
  unfold barrierCase2Y
  rw [barrierV2_T_eq_finite_log hx, barrierFiniteT_sum_cast, ← hv]
  unfold realEnergyColumnField barrierCase2YRat
  push_cast
  ring

end
section

theorem barrierCase2X_deriv_eq_zero_iff {x : ℝ}
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) (h0 : x ≠ 0) :
    deriv barrierCase2X x = 0 ↔ (barrierCase2AX.map (Rat.castHom ℝ)).eval x = 0 := by
  have ha : |x| ≤ 1 := abs_le.mpr ⟨hx.1.le, hx.2.le⟩
  have h1 : x ≠ 1 := ne_of_lt hx.2
  rw [(barrierCase2X_hasDerivAt hx h0).deriv, Polynomial.eval_map,
    barrierCase2AX_clears_denominator ha h0 h1]
  simp [barrierCase2QX_eval_ne_zero ha h0 h1]

theorem barrierCase2Y_deriv_eq_zero_iff {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    deriv barrierCase2Y x = 0 ↔ (barrierCase2AY.map (Rat.castHom ℝ)).eval x = 0 := by
  have ha : |x| ≤ 1 := abs_le.mpr ⟨by linarith [hx.1], hx.2.le⟩
  have h0 : x ≠ 0 := ne_of_gt hx.1
  have h1 : x ≠ 1 := ne_of_lt hx.2
  rw [(barrierCase2Y_hasDerivAt hx).deriv, Polynomial.eval_map,
    barrierCase2AY_clears_denominator ha h0 h1]
  simp [barrierCase2QY_eval_ne_zero ha h0 h1]

end

section

open scoped ComplexConjugate

theorem barrierCase2XPLogTerm_conj (x : ℝ) (z r : ℂ)
    (hz : (1 - 2 * (x : ℂ) * z + z ^ 2).im ≠ 0 ∨
      0 < (1 - 2 * (x : ℂ) * z + z ^ 2).re) :
    barrierCase2XPLogTerm x (star z, star r) = barrierCase2XPLogTerm x (z, r) := by
  have h := barrierComplexLog_conj_weighted_re (2 * r)
    (1 - 2 * (x : ℂ) * z + z ^ 2) hz
  rw [← barrierComplexLog_quadratic_conj x z] at h
  simpa only [barrierCase2XPLogTerm, Complex.star_def, map_mul, map_ofNat] using h

theorem barrierCase2XVLogTerm_conj (x : ℝ) (z r : ℂ)
    (hz : (1 - (x : ℂ) * z).im ≠ 0 ∨ 0 < (1 - (x : ℂ) * z).re) :
    barrierCase2XVLogTerm x (star z, star r) = barrierCase2XVLogTerm x (z, r) := by
  have h := barrierComplexLog_conj_weighted_re r (1 - (x : ℂ) * z) hz
  rw [← barrierComplexLog_linear_conj x z] at h
  simpa only [barrierCase2XVLogTerm, Complex.star_def] using h

theorem barrierCase2YVLogTerm_conj (x : ℝ) (z r : ℂ)
    (hz : (1 - 2 * (x : ℂ) * z + z ^ 2).im ≠ 0 ∨
      0 < (1 - 2 * (x : ℂ) * z + z ^ 2).re) :
    barrierCase2YVLogTerm x (star z, star r) = barrierCase2YVLogTerm x (z, r) := by
  have h := barrierComplexLog_conj_weighted_re ((-1 : ℂ) * r)
    (1 - 2 * (x : ℂ) * z + z ^ 2) hz
  rw [← barrierComplexLog_quadratic_conj x z] at h
  simpa only [barrierCase2YVLogTerm, Complex.star_def, map_mul, map_neg, map_one] using h

end

open Set

theorem barrierCase2X_le_of_bracket_bounds (M : ℝ)
    (hneg : barrierCase2X (-1) ≤ M)
    (hbr : ∀ m ∈ barrierCase2XBrackets, ∀ x ∈
      Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ),
      barrierCase2X x ≤ M) :
    ∀ x ∈ Ico (-1 : ℝ) 0 ∪ Ioo (0 : ℝ) 1, barrierCase2X x ≤ M := by
  apply GlobalMaxReduction.le_on_two_components_of_stationary_cover
    (S := {x | ∃ m ∈ barrierCase2XBrackets,
      x ∈ Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ)})
  · exact barrierCase2X_continuousOn_negative
  · exact barrierCase2X_continuousOn_positive
  · exact hneg
  · exact barrierCase2X_tendsto_zero_left
  · exact barrierCase2X_tendsto_zero_right
  · exact barrierCase2X_tendsto_one_left
  · intro x hx hd
    have h0 : x ≠ 0 := by rcases hx with hx | hx <;> linarith [hx.1, hx.2]
    have hdomain : x ∈ Ioo (-1 : ℝ) 1 := by
      rcases hx with hx | hx
      · exact ⟨hx.1, by linarith [hx.2]⟩
      · exact ⟨by linarith [hx.1], hx.2⟩
    exact barrierCase2AX_roots_exhausted hx
      ((barrierCase2X_deriv_eq_zero_iff hdomain h0).1 hd)
  · rintro x ⟨m, hm, hx⟩
    exact hbr m hm x hx

theorem barrierCase2Y_le_of_bracket_bounds (M : ℝ)
    (hbr : ∀ m ∈ barrierCase2YBrackets, ∀ x ∈
      Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ),
      barrierCase2Y x ≤ M) :
    ∀ x ∈ Ioo (0 : ℝ) 1, barrierCase2Y x ≤ M := by
  apply GlobalMaxReduction.le_on_Ioo_of_stationary_cover
    (S := {x | ∃ m ∈ barrierCase2YBrackets,
      x ∈ Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ)})
  · exact barrierCase2Y_continuousOn
  · exact barrierCase2Y_tendsto_zero_right
  · exact barrierCase2Y_tendsto_one_left
  · intro x hx hd
    exact barrierCase2AY_roots_exhausted hx ((barrierCase2Y_deriv_eq_zero_iff hx).1 hd)
  · rintro x ⟨m, hm, hx⟩
    exact hbr m hm x hx

end InternalCatalan

end

end OAI

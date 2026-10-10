import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Order.Filter.AtTopBot.Group
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import OAI.NumberTheory.Catalan.Energy.BarrierFinitePotentialDerivatives
import OAI.NumberTheory.Catalan.Estimates.RealEnergySupDual

namespace OAI

noncomputable section

namespace InternalCatalan

section

def barrierCase1X (x : ℝ) : ℝ :=
  realEnergyField 1 x + barrierLambda1 * realEnergyCaseField x -
    2 * barrierTrialT barrierP1 x - barrierTrialS barrierV1 x

def barrierCase1Y (x : ℝ) : ℝ :=
  realEnergyColumnField x + 2 * barrierTrialT barrierV1 x

private theorem barrier_realEnergyField_one_hasDerivAt {x : ℝ}
    (h0 : x ≠ 0) (h1 : x ≠ 1) :
    HasDerivAt (realEnergyField 1)
      ((19 / 48 : ℝ) / x - (1 / 12 : ℝ) / (1 - x) -
        (41 / 24 : ℝ) * x / (1 + x ^ 2)) x := by
  have ho : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have hd : 1 + x ^ 2 ≠ 0 := ne_of_gt (by positivity : (0 : ℝ) < 1 + x ^ 2)
  have hl0 : HasDerivAt (fun y : ℝ => Real.log |y|) (1 / x) x := by
    simpa only [Real.log_abs, one_div] using Real.hasDerivAt_log h0
  have hl1 : HasDerivAt (fun y : ℝ => Real.log (1 - y))
      (-1 / (1 - x)) x :=
    ((hasDerivAt_id x).const_sub (1 : ℝ)).log ho
  have hp : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x).const_add (1 : ℝ)
  have hl2 := hp.log hd
  have hh := ((hl0.const_mul (19 / 48 : ℝ)).add
    (hl1.const_mul (1 / 12 : ℝ))).sub
    (hl2.const_mul ((1 : ℝ) / 2 + 17 / 48))
  unfold realEnergyField
  apply hh.congr_deriv
  field_simp [h0, ho, hd]
  ring

private theorem barrier_realEnergyColumnField_hasDerivAt {x : ℝ}
    (h0 : x ≠ 0) (h1 : x ≠ 1) :
    HasDerivAt realEnergyColumnField
      ((7 / 48 : ℝ) / x - (1 / 12 : ℝ) / (1 - x)) x := by
  have ho : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have hl0 : HasDerivAt Real.log (1 / x) x := by
    simpa only [one_div] using Real.hasDerivAt_log h0
  have hl1 : HasDerivAt (fun y : ℝ => Real.log (1 - y))
      (-1 / (1 - x)) x :=
    ((hasDerivAt_id x).const_sub (1 : ℝ)).log ho
  have hh := (hl0.const_mul (7 / 48 : ℝ)).add (hl1.const_mul (1 / 12 : ℝ))
  unfold realEnergyColumnField
  apply hh.congr_deriv
  field_simp [h0, ho]
  ring

private theorem barrier_realEnergyCaseField_hasDerivAt (x : ℝ) :
    HasDerivAt realEnergyCaseField (-4 * x / (1 + x ^ 2) ^ 2) x := by
  have hd : 1 + x ^ 2 ≠ 0 := ne_of_gt (by positivity : (0 : ℝ) < 1 + x ^ 2)
  have hp : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have hq : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x :=
    hp.const_add (1 : ℝ)
  have hh := ((hp.const_mul (2 : ℝ)).fun_div hq hd).const_sub (1 / 6 : ℝ)
  unfold realEnergyCaseField
  apply hh.congr_deriv
  field_simp [hd]
  ring

theorem barrierCase1X_hasDerivAt {x : ℝ} (h0 : x ≠ 0) (h1 : x ≠ 1) :
    HasDerivAt barrierCase1X (barrierCase1XDerivativeFormula x) x := by
  have ht : HasDerivAt (barrierTrialT barrierP1)
      ((barrierFiniteUDerivative barrierP1Finite).eval₂ (Rat.castHom ℝ) x) x := by
    simpa only [barrierP1] using barrierTrialT_nil_hasDerivAt barrierP1Finite x
  have hs : HasDerivAt (barrierTrialS barrierV1)
      ((barrierFinitePowerDerivative barrierV1Finite).eval₂ (Rat.castHom ℝ) x) x := by
    simpa only [barrierV1] using barrierTrialS_nil_hasDerivAt barrierV1Finite x
  have hh := (((barrier_realEnergyField_one_hasDerivAt h0 h1).add
    ((barrier_realEnergyCaseField_hasDerivAt x).const_mul barrierLambda1)).sub
    (ht.const_mul (2 : ℝ))).sub hs
  unfold barrierCase1X
  apply hh.congr_deriv
  unfold barrierCase1XDerivativeFormula
  ring

theorem barrierCase1Y_hasDerivAt {x : ℝ} (h0 : x ≠ 0) (h1 : x ≠ 1) :
    HasDerivAt barrierCase1Y (barrierCase1YDerivativeFormula x) x := by
  have ht : HasDerivAt (barrierTrialT barrierV1)
      ((barrierFiniteUDerivative barrierV1Finite).eval₂ (Rat.castHom ℝ) x) x := by
    simpa only [barrierV1] using barrierTrialT_nil_hasDerivAt barrierV1Finite x
  have hh := (barrier_realEnergyColumnField_hasDerivAt h0 h1).add (ht.const_mul (2 : ℝ))
  unfold barrierCase1Y
  apply hh.congr_deriv
  unfold barrierCase1YDerivativeFormula
  rfl

end

namespace Case1Height
open Polynomial
open scoped BigOperators

theorem abs_U_eval_le (k : ℕ) {x : ℝ} (hx : |x| ≤ 1) :
    |(Chebyshev.U ℝ (k : ℤ)).eval x| ≤ (k : ℝ) + 1 := by
  have h := Chebyshev.abs_iterate_derivative_T_real_le ((k : ℤ) + 1) 1 hx
  simp only [Function.iterate_one] at h
  rw [Chebyshev.derivative_T_eval_one] at h
  rw [Chebyshev.T_derivative_eq_U, eval_mul, eval_intCast] at h
  have hi : (k : ℤ) + 1 - 1 = (k : ℤ) := by ring
  rw [hi, abs_mul] at h
  have hn : (((k : ℤ) + 1 : ℤ) : ℝ) = (k : ℝ) + 1 := by norm_num
  rw [hn] at h
  have hp : 0 < (k : ℝ) + 1 := by positivity
  rw [abs_of_pos hp] at h
  exact le_of_mul_le_mul_left (by simpa only [sq] using h) hp

theorem finiteU_abs_le_mass (cs : List ℤ) {x : ℝ} (hx : |x| ≤ 1) :
    |(barrierFiniteUDerivative cs).eval₂ (Rat.castHom ℝ) x| ≤
      ∑ k ∈ Finset.range cs.length,
        |(cs.getD k 0 : ℝ) / 100000000| * ((k : ℝ) + 1) := by
  have hd : (barrierFiniteUDerivative cs).eval₂ (Rat.castHom ℝ) x =
      ∑ k ∈ Finset.range cs.length,
        ((cs.getD k 0 : ℝ) / 100000000) * (Chebyshev.U ℝ (k : ℤ)).eval x := by
    simp only [barrierFiniteUDerivative, eval₂_finsetSum, eval₂_mul,
      eval₂_C, map_div₀, map_intCast, map_ofNat]
    simp only [eval₂_eq_eval_map, Chebyshev.map_U]
  rw [hd]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro k _
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (abs_U_eval_le k hx) (abs_nonneg _)

theorem finitePower_abs_le_mass (cs : List ℤ) {x : ℝ} (hx : |x| ≤ 1) :
    |(barrierFinitePowerDerivative cs).eval₂ (Rat.castHom ℝ) x| ≤
      ∑ k ∈ Finset.range cs.length, |(cs.getD k 0 : ℝ) / 100000000| := by
  have hd : (barrierFinitePowerDerivative cs).eval₂ (Rat.castHom ℝ) x =
      ∑ k ∈ Finset.range cs.length,
        ((cs.getD k 0 : ℝ) / 100000000) * x ^ k := by
    simp only [barrierFinitePowerDerivative, eval₂_finsetSum, eval₂_mul,
      eval₂_C, eval₂_X_pow, map_div₀, map_intCast, map_ofNat]
  rw [hd]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  apply Finset.sum_le_sum
  intro k _
  rw [abs_mul, abs_pow]
  exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (abs_nonneg x) hx)
    (abs_nonneg ((cs.getD k 0 : ℝ) / 100000000))).trans_eq (mul_one _)

theorem actual_finite_bounds {x : ℝ} (hx : |x| ≤ 1) :
    |(barrierFiniteUDerivative barrierP1Finite).eval₂ (Rat.castHom ℝ) x| ≤ 36 ∧
    |(barrierFiniteUDerivative barrierV1Finite).eval₂ (Rat.castHom ℝ) x| ≤ 36 ∧
    |(barrierFinitePowerDerivative barrierV1Finite).eval₂ (Rat.castHom ℝ) x| ≤ 8 := by
  refine ⟨(finiteU_abs_le_mass barrierP1Finite hx).trans ?_,
    (finiteU_abs_le_mass barrierV1Finite hx).trans ?_,
    (finitePower_abs_le_mass barrierV1Finite hx).trans ?_⟩
  all_goals norm_num [barrierP1Finite, barrierV1Finite, Finset.sum_range_succ]

private theorem abs_div_le_const {a b C : ℝ} (hb : 0 < |b|)
    (h : |a| ≤ C * |b|) : |a / b| ≤ C := by
  rw [abs_div]
  exact (div_le_iff₀ hb).2 h

private theorem abs_sub_le_pair (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  simpa only [Real.norm_eq_abs] using norm_sub_le a b

private theorem abs_five_sub_le (a b c d e g : ℝ) :
    |a - b - c - d - e - g| ≤ |a| + |b| + |c| + |d| + |e| + |g| := by
  have h1 := abs_sub_le_pair a b
  have h2 := abs_sub_le_pair (a - b) c
  have h3 := abs_sub_le_pair (a - b - c) d
  have h4 := abs_sub_le_pair (a - b - c - d) e
  have h5 := abs_sub_le_pair (a - b - c - d - e) g
  linarith

theorem actual_X_deriv_abs_le {x : ℝ} (hx : |x| ≤ 1)
    (hxmargin : (1 / 100 : ℝ) ≤ |x|)
    (hgap : (1 / 100 : ℝ) ≤ 1 - x) :
    |deriv barrierCase1X x| ≤ 100000 := by
  have hxpos : 0 < |x| := lt_of_lt_of_le (by norm_num) hxmargin
  have hgpos : 0 < 1 - x := lt_of_lt_of_le (by norm_num) hgap
  have h0 : x ≠ 0 := abs_pos.mp hxpos
  have h1 : x ≠ 1 := by intro h; subst x; norm_num at hgap
  obtain ⟨hpu, _, hvp⟩ := actual_finite_bounds hx
  have hd : 0 < 1 + x ^ 2 := by positivity
  have hd1 : 1 ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg x]
  have hd2 : 1 ≤ (1 + x ^ 2) ^ 2 := by nlinarith [sq_nonneg (x ^ 2)]
  have hA : |(19 / 48 : ℝ) / x| ≤ 40 := by
    apply abs_div_le_const hxpos
    norm_num
    linarith
  have hB : |(1 / 12 : ℝ) / (1 - x)| ≤ 9 := by
    apply abs_div_le_const (abs_pos.mpr (ne_of_gt hgpos))
    rw [abs_of_pos hgpos]
    norm_num
    linarith
  have hC : |(41 / 24 : ℝ) * x / (1 + x ^ 2)| ≤ 2 := by
    apply abs_div_le_const (abs_pos.mpr (ne_of_gt hd))
    rw [abs_mul, abs_of_pos hd]
    norm_num
    nlinarith
  have hD : |4 * barrierLambda1 * x / (1 + x ^ 2) ^ 2| ≤ 10 := by
    apply abs_div_le_const (abs_pos.mpr (ne_of_gt (sq_pos_of_pos hd)))
    rw [abs_mul, abs_of_pos (sq_pos_of_pos hd)]
    norm_num [barrierLambda1]
    nlinarith
  have hE : |2 * (barrierFiniteUDerivative barrierP1Finite).eval₂ (Rat.castHom ℝ) x| ≤ 72 := by
    rw [abs_mul]
    norm_num
    linarith
  rw [(barrierCase1X_hasDerivAt h0 h1).deriv]
  unfold barrierCase1XDerivativeFormula
  exact (abs_five_sub_le _ _ _ _ _ _).trans (by linarith)

theorem actual_Y_deriv_abs_le {x : ℝ} (hx : |x| ≤ 1)
    (hxmargin : (1 / 100 : ℝ) ≤ |x|)
    (hgap : (1 / 100 : ℝ) ≤ 1 - x) :
    |deriv barrierCase1Y x| ≤ 100000 := by
  have hxpos : 0 < |x| := lt_of_lt_of_le (by norm_num) hxmargin
  have hgpos : 0 < 1 - x := lt_of_lt_of_le (by norm_num) hgap
  have h0 : x ≠ 0 := abs_pos.mp hxpos
  have h1 : x ≠ 1 := by intro h; subst x; norm_num at hgap
  obtain ⟨_, hvu, _⟩ := actual_finite_bounds hx
  have hA : |(7 / 48 : ℝ) / x| ≤ 15 := by
    apply abs_div_le_const hxpos
    norm_num
    linarith
  have hB : |(1 / 12 : ℝ) / (1 - x)| ≤ 9 := by
    apply abs_div_le_const (abs_pos.mpr (ne_of_gt hgpos))
    rw [abs_of_pos hgpos]
    norm_num
    linarith
  have hC : |2 * (barrierFiniteUDerivative barrierV1Finite).eval₂ (Rat.castHom ℝ) x| ≤ 72 := by
    rw [abs_mul]
    norm_num
    linarith
  rw [(barrierCase1Y_hasDerivAt h0 h1).deriv]
  unfold barrierCase1YDerivativeFormula
  have hab := abs_sub_le_pair ((7 / 48 : ℝ) / x) ((1 / 12 : ℝ) / (1 - x))
  have habc := abs_add_le (((7 / 48 : ℝ) / x) - ((1 / 12 : ℝ) / (1 - x)))
    (2 * (barrierFiniteUDerivative barrierV1Finite).eval₂ (Rat.castHom ℝ) x)
  linarith

end Case1Height

section

open Set Filter
open scoped Topology

private theorem barrier_atBot_add_finite {l : Filter ℝ} {f g : ℝ → ℝ} {c : ℝ}
    (hf : Tendsto f l atBot) (hg : Tendsto g l (𝓝 c)) :
    Tendsto (fun x => f x + g x) l atBot := by
  have hb : ∀ᶠ x in l, g x ≤ c + 1 :=
    ((tendsto_order.mp hg).2 (c + 1) (by linarith)).mono (fun _ hx => hx.le)
  exact tendsto_atBot_add_right_of_ge' l (c + 1) hf hb

private theorem barrier_log_one_sub_tendsto :
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

private def barrierCase1XRegular (x : ℝ) : ℝ :=
  -(41 / 48 : ℝ) * Real.log (1 + x ^ 2) +
    barrierLambda1 * realEnergyCaseField x -
    2 * barrierTrialT barrierP1 x - barrierTrialS barrierV1 x

private theorem barrierCase1XRegular_continuousAt (x : ℝ) :
    ContinuousAt barrierCase1XRegular x := by
  have hp : ContinuousAt (fun y : ℝ => 1 + y ^ 2) x :=
    continuousAt_const.add (continuousAt_id.pow 2)
  have hd : 1 + x ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hc : ContinuousAt realEnergyCaseField x := by
    unfold realEnergyCaseField
    exact continuousAt_const.sub
      ((continuousAt_const.mul (continuousAt_id.pow 2)).div hp hd)
  have ht : ContinuousAt (barrierTrialT barrierP1) x := by
    simpa only [barrierP1] using
      (barrierTrialT_nil_hasDerivAt barrierP1Finite x).continuousAt
  have hs : ContinuousAt (barrierTrialS barrierV1) x := by
    simpa only [barrierV1] using
      (barrierTrialS_nil_hasDerivAt barrierV1Finite x).continuousAt
  exact ((((hp.log hd).const_mul (-(41 / 48 : ℝ))).add
    (hc.const_mul barrierLambda1)).sub (ht.const_mul 2)).sub hs

private theorem barrierCase1V1T_continuousAt (x : ℝ) :
    ContinuousAt (barrierTrialT barrierV1) x := by
  simpa only [barrierV1] using
    (barrierTrialT_nil_hasDerivAt barrierV1Finite x).continuousAt

private theorem barrierCase1X_split (x : ℝ) :
    barrierCase1X x = (19 / 48 : ℝ) * Real.log |x| +
      (1 / 12 : ℝ) * Real.log (1 - x) + barrierCase1XRegular x := by
  unfold barrierCase1X realEnergyField barrierCase1XRegular
  ring

private theorem barrierCase1X_zero_remainder :
    ContinuousAt (fun x : ℝ => (1 / 12 : ℝ) * Real.log (1 - x) +
      barrierCase1XRegular x) 0 := by
  have hl : ContinuousAt (fun x : ℝ => Real.log (1 - x)) 0 :=
    (continuousAt_const.sub continuousAt_id).log (by norm_num)
  exact (hl.const_mul (1 / 12 : ℝ)).add (barrierCase1XRegular_continuousAt 0)

private theorem barrierCase1X_one_remainder :
    ContinuousAt (fun x : ℝ => (19 / 48 : ℝ) * Real.log |x| +
      barrierCase1XRegular x) 1 := by
  have hl : ContinuousAt (fun x : ℝ => Real.log |x|) 1 := by
    simpa only [Real.log_abs] using (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0))
  exact (hl.const_mul (19 / 48 : ℝ)).add (barrierCase1XRegular_continuousAt 1)

theorem barrierCase1X_tendsto_zero_left :
    Tendsto barrierCase1X (𝓝[<] 0) atBot := by
  have hl : Tendsto (fun x : ℝ => (19 / 48 : ℝ) * Real.log |x|)
      (𝓝[<] 0) atBot := by
    simpa only [Real.log_abs] using
      (Tendsto.const_mul_atBot (by norm_num : (0 : ℝ) < 19 / 48)
        Real.tendsto_log_nhdsLT_zero)
  have hh := barrier_atBot_add_finite hl
    (barrierCase1X_zero_remainder.tendsto.mono_left nhdsWithin_le_nhds)
  convert hh using 1
  funext x
  rw [barrierCase1X_split]
  ring

theorem barrierCase1X_tendsto_zero_right :
    Tendsto barrierCase1X (𝓝[>] 0) atBot := by
  have hl : Tendsto (fun x : ℝ => (19 / 48 : ℝ) * Real.log |x|)
      (𝓝[>] 0) atBot := by
    simpa only [Real.log_abs] using
      (Tendsto.const_mul_atBot (by norm_num : (0 : ℝ) < 19 / 48)
        Real.tendsto_log_nhdsGT_zero)
  have hh := barrier_atBot_add_finite hl
    (barrierCase1X_zero_remainder.tendsto.mono_left nhdsWithin_le_nhds)
  convert hh using 1
  funext x
  rw [barrierCase1X_split]
  ring

theorem barrierCase1X_tendsto_one_left :
    Tendsto barrierCase1X (𝓝[<] 1) atBot := by
  have hl := Tendsto.const_mul_atBot (by norm_num : (0 : ℝ) < 1 / 12)
    barrier_log_one_sub_tendsto
  have hh := barrier_atBot_add_finite hl
    (barrierCase1X_one_remainder.tendsto.mono_left nhdsWithin_le_nhds)
  convert hh using 1
  funext x
  rw [barrierCase1X_split]
  ring

theorem barrierCase1Y_tendsto_zero_right :
    Tendsto barrierCase1Y (𝓝[>] 0) atBot := by
  have hl := Tendsto.const_mul_atBot (by norm_num : (0 : ℝ) < 7 / 48)
    Real.tendsto_log_nhdsGT_zero
  have hr : ContinuousAt (fun x : ℝ => (1 / 12 : ℝ) * Real.log (1 - x) +
      2 * barrierTrialT barrierV1 x) 0 := by
    have hlog : ContinuousAt (fun x : ℝ => Real.log (1 - x)) 0 :=
      (continuousAt_const.sub continuousAt_id).log (by norm_num)
    exact (hlog.const_mul (1 / 12 : ℝ)).add
      ((barrierCase1V1T_continuousAt 0).const_mul 2)
  have hh := barrier_atBot_add_finite hl (hr.tendsto.mono_left nhdsWithin_le_nhds)
  convert hh using 1
  funext x
  unfold barrierCase1Y realEnergyColumnField
  ring

theorem barrierCase1Y_tendsto_one_left :
    Tendsto barrierCase1Y (𝓝[<] 1) atBot := by
  have hl := Tendsto.const_mul_atBot (by norm_num : (0 : ℝ) < 1 / 12)
    barrier_log_one_sub_tendsto
  have hr : ContinuousAt (fun x : ℝ => (7 / 48 : ℝ) * Real.log x +
      2 * barrierTrialT barrierV1 x) 1 := by
    exact ((Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).const_mul
      (7 / 48 : ℝ)).add ((barrierCase1V1T_continuousAt 1).const_mul 2)
  have hh := barrier_atBot_add_finite hl (hr.tendsto.mono_left nhdsWithin_le_nhds)
  convert hh using 1
  funext x
  unfold barrierCase1Y realEnergyColumnField
  ring

theorem barrierCase1X_continuousAt_neg_one :
    ContinuousAt barrierCase1X (-1 : ℝ) :=
  (barrierCase1X_hasDerivAt (by norm_num) (by norm_num)).continuousAt

end

def barrierCase1XRat (x : ℚ) : ℚ :=
  (247405979 / 100000000 : ℚ) * (1 / 6 - 2 * x ^ 2 / (1 + x ^ 2)) -
    2 * barrierFiniteTRat barrierP1Finite x - barrierFiniteSRat barrierV1Finite x

def barrierCase1YRat (x : ℚ) : ℚ :=
  2 * barrierFiniteTRat barrierV1Finite x

theorem barrierCase1X_eval_rat (x : ℚ) :
    barrierCase1X (x : ℝ) =
      (19 / 48 : ℝ) * Real.log |(x : ℝ)| +
        (1 / 12 : ℝ) * Real.log (1 - (x : ℝ)) -
        (41 / 48 : ℝ) * Real.log (1 + (x : ℝ) ^ 2) +
        ((barrierCase1XRat x : ℚ) : ℝ) := by
  unfold barrierCase1X barrierP1 barrierV1
  rw [barrierTrialT_nil_eval_rat, barrierTrialS_nil_eval_rat]
  unfold realEnergyField realEnergyCaseField barrierCase1XRat barrierLambda1
  push_cast
  ring

theorem barrierCase1Y_eval_rat (x : ℚ) :
    barrierCase1Y (x : ℝ) =
      (7 / 48 : ℝ) * Real.log (x : ℝ) +
        (1 / 12 : ℝ) * Real.log (1 - (x : ℝ)) +
        ((barrierCase1YRat x : ℚ) : ℝ) := by
  unfold barrierCase1Y barrierV1
  rw [barrierTrialT_nil_eval_rat]
  unfold realEnergyColumnField barrierCase1YRat
  push_cast
  ring

theorem barrierCase1X_deriv_eq_zero_iff {x : ℝ} (h0 : x ≠ 0) (h1 : x ≠ 1) :
    deriv barrierCase1X x = 0 ↔ (barrierCase1AX.map (Rat.castHom ℝ)).eval x = 0 := by
  rw [(barrierCase1X_hasDerivAt h0 h1).deriv, Polynomial.eval_map,
    barrierCase1AX_clears_denominator h0 h1]
  simp [barrierCase1QX_eval_ne_zero h0 h1]

theorem barrierCase1Y_deriv_eq_zero_iff {x : ℝ} (h0 : x ≠ 0) (h1 : x ≠ 1) :
    deriv barrierCase1Y x = 0 ↔ (barrierCase1AY.map (Rat.castHom ℝ)).eval x = 0 := by
  rw [(barrierCase1Y_hasDerivAt h0 h1).deriv, Polynomial.eval_map,
    barrierCase1AY_clears_denominator h0 h1]
  simp [barrierCase1QY_eval_ne_zero h0 h1]

theorem barrierCase1X_stationary_in_each_bracket (m : ℤ)
    (hm : m ∈ barrierCase1XBrackets) :
    ∃ x : ℝ, x ∈ Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ) ∧
      deriv barrierCase1X x = 0 := by
  obtain ⟨x, hx, hp⟩ := barrierCase1AX_root_in_each_bracket m hm
  obtain ⟨_, hr, hs⟩ := barrierCase1X_bracket_domain m hm
  have hr' : (barrierBracketRight m : ℝ) < 1 := by exact_mod_cast hr
  have h1 : x ≠ 1 := ne_of_lt (hx.2.trans hr')
  have h0 : x ≠ 0 := by
    rcases hs with hs | hs
    · have hs' : (barrierBracketRight m : ℝ) < 0 := by exact_mod_cast hs
      exact ne_of_lt (hx.2.trans hs')
    · have hs' : (0 : ℝ) < (barrierBracketLeft m : ℝ) := by exact_mod_cast hs
      exact ne_of_gt (hs'.trans hx.1)
  exact ⟨x, hx, (barrierCase1X_deriv_eq_zero_iff h0 h1).2 hp⟩

theorem barrierCase1Y_stationary_in_each_bracket (m : ℤ)
    (hm : m ∈ barrierCase1YBrackets) :
    ∃ x : ℝ, x ∈ Set.Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ) ∧
      deriv barrierCase1Y x = 0 := by
  obtain ⟨x, hx, hp⟩ := barrierCase1AY_root_in_each_bracket m hm
  obtain ⟨hl, hr⟩ := barrierCase1Y_bracket_domain m hm
  have hl' : (0 : ℝ) < (barrierBracketLeft m : ℝ) := by exact_mod_cast hl
  have hr' : (barrierBracketRight m : ℝ) < 1 := by exact_mod_cast hr
  have h0 : x ≠ 0 := ne_of_gt (hl'.trans hx.1)
  have h1 : x ≠ 1 := ne_of_lt (hx.2.trans hr')
  exact ⟨x, hx, (barrierCase1Y_deriv_eq_zero_iff h0 h1).2 hp⟩

open Set

namespace Case1Height

theorem X_closed_bracket_margins (m : ℤ) (hm : m ∈ barrierCase1XBrackets)
    {x : ℝ} (hx : x ∈ Icc (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ)) :
    |x| ≤ 1 ∧ (1 / 100 : ℝ) ≤ |x| ∧ (1 / 100 : ℝ) ≤ 1 - x := by
  simp only [barrierCase1XBrackets, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl
  all_goals
    norm_num [barrierBracketLeft, barrierBracketRight, Set.mem_Icc] at hx
    refine ⟨abs_le.mpr ⟨by linarith, by linarith⟩, ?_, ?_⟩
    · rcases le_total x 0 with hn | hp
      · rw [abs_of_nonpos hn]
        linarith
      · rw [abs_of_nonneg hp]
        linarith
    · linarith

theorem Y_closed_bracket_margins (m : ℤ) (hm : m ∈ barrierCase1YBrackets)
    {x : ℝ} (hx : x ∈ Icc (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ)) :
    |x| ≤ 1 ∧ (1 / 100 : ℝ) ≤ |x| ∧ (1 / 100 : ℝ) ≤ 1 - x := by
  simp only [barrierCase1YBrackets, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl
  all_goals
    norm_num [barrierBracketLeft, barrierBracketRight, Set.mem_Icc] at hx
    refine ⟨abs_le.mpr ⟨by linarith, by linarith⟩, ?_, ?_⟩
    · rcases le_total x 0 with hn | hp
      · rw [abs_of_nonpos hn]
        linarith
      · rw [abs_of_nonneg hp]
        linarith
    · linarith

private theorem regular_of_margins {x : ℝ}
    (hx : (1 / 100 : ℝ) ≤ |x|) (hgap : (1 / 100 : ℝ) ≤ 1 - x) :
    x ≠ 0 ∧ x ≠ 1 := by
  constructor
  · exact abs_pos.mp (lt_of_lt_of_le (by norm_num) hx)
  · intro h
    subst x
    norm_num at hgap

theorem abs_sub_le_on_Icc {f : ℝ → ℝ} {a b C x : ℝ}
    (hdiff : ∀ y ∈ Icc a b, DifferentiableAt ℝ f y)
    (hbound : ∀ y ∈ Icc a b, |deriv f y| ≤ C)
    (hx : x ∈ Icc a b) : |f x - f a| ≤ C * |x - a| := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hx.1.trans hx.2⟩
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun y hy => (hdiff y hy).hasDerivAt.hasDerivWithinAt)
      (fun y hy => by simpa only [Real.norm_eq_abs] using hbound y hy)
      (convex_Icc a b) ha hx

theorem actual_bracket_width (m : ℤ) :
    (barrierBracketRight m : ℝ) - (barrierBracketLeft m : ℝ) =
      (2 / 10000000000 : ℝ) := by
  norm_num [barrierBracketLeft, barrierBracketRight]
  ring

private theorem height_of_abs_variation {f : ℝ → ℝ} {m : ℤ} {x : ℝ}
    (hx : x ∈ Icc (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ))
    (hvar : |f x - f (barrierBracketLeft m : ℝ)| ≤
      100000 * |x - (barrierBracketLeft m : ℝ)|) :
    f x ≤ f (barrierBracketLeft m : ℝ) + (2 / 100000 : ℝ) := by
  have hdist : |x - (barrierBracketLeft m : ℝ)| ≤
      (barrierBracketRight m : ℝ) - (barrierBracketLeft m : ℝ) := by
    rw [abs_of_nonneg (sub_nonneg.mpr hx.1)]
    exact sub_le_sub_right hx.2 _
  have he : |f x - f (barrierBracketLeft m : ℝ)| ≤ (2 / 100000 : ℝ) := by
    calc
      _ ≤ 100000 * |x - (barrierBracketLeft m : ℝ)| := hvar
      _ ≤ 100000 * ((barrierBracketRight m : ℝ) - (barrierBracketLeft m : ℝ)) :=
        mul_le_mul_of_nonneg_left hdist (by norm_num)
      _ = (2 / 100000 : ℝ) := by rw [actual_bracket_width]; norm_num
  have hs := (le_abs_self (f x - f (barrierBracketLeft m : ℝ))).trans he
  linarith

end Case1Height

theorem barrierCase1X_bracket_height (m : ℤ) (hm : m ∈ barrierCase1XBrackets)
    {x : ℝ} (hx : x ∈ Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ)) :
    barrierCase1X x ≤ barrierCase1X (barrierBracketLeft m : ℝ) + (2 / 100000 : ℝ) := by
  have hxcc : x ∈ Icc (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ) :=
    ⟨hx.1.le, hx.2.le⟩
  apply Case1Height.height_of_abs_variation hxcc
  apply Case1Height.abs_sub_le_on_Icc
  · intro y hy
    obtain ⟨_, hy0, hy1⟩ := Case1Height.X_closed_bracket_margins m hm hy
    obtain ⟨h0, h1⟩ := Case1Height.regular_of_margins hy0 hy1
    exact (barrierCase1X_hasDerivAt h0 h1).differentiableAt
  · intro y hy
    obtain ⟨hyabs, hy0, hy1⟩ := Case1Height.X_closed_bracket_margins m hm hy
    exact Case1Height.actual_X_deriv_abs_le hyabs hy0 hy1
  · exact hxcc

theorem barrierCase1Y_bracket_height (m : ℤ) (hm : m ∈ barrierCase1YBrackets)
    {x : ℝ} (hx : x ∈ Ioo (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ)) :
    barrierCase1Y x ≤ barrierCase1Y (barrierBracketLeft m : ℝ) + (2 / 100000 : ℝ) := by
  have hxcc : x ∈ Icc (barrierBracketLeft m : ℝ) (barrierBracketRight m : ℝ) :=
    ⟨hx.1.le, hx.2.le⟩
  apply Case1Height.height_of_abs_variation hxcc
  apply Case1Height.abs_sub_le_on_Icc
  · intro y hy
    obtain ⟨_, hy0, hy1⟩ := Case1Height.Y_closed_bracket_margins m hm hy
    obtain ⟨h0, h1⟩ := Case1Height.regular_of_margins hy0 hy1
    exact (barrierCase1Y_hasDerivAt h0 h1).differentiableAt
  · intro y hy
    obtain ⟨hyabs, hy0, hy1⟩ := Case1Height.Y_closed_bracket_margins m hm hy
    exact Case1Height.actual_Y_deriv_abs_le hyabs hy0 hy1
  · exact hxcc

end InternalCatalan

end

end OAI

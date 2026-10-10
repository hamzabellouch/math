import OAI.Analysis.KadisonKastler.HaarFunctionalCalculus
import Mathlib.Topology.MetricSpace.ThickenedIndicator
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

namespace OAI

/-! # Continuous approximation of a Haar arc

The arc is the closed metric ball about zero in the circle of length `2 * pi`.
Continuous thickened indicators decrease towards its indicator, stay between
zero and one, and converge in scalar Haar `L²`. No operator spectral projection
is assumed in this construction.
-/

namespace KadisonKastler

open MeasureTheory Filter
open scoped NNReal Topology

noncomputable section

local instance haarArcPeriodPositive : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The centered closed arc of angular radius `a`. -/
def haarArc (a : ℝ) : Set HaarCircle := Metric.closedBall 0 a

theorem isClosed_haarArc (a : ℝ) : IsClosed (haarArc a) := Metric.isClosed_closedBall

theorem measurableSet_haarArc (a : ℝ) : MeasurableSet (haarArc a) :=
  (isClosed_haarArc a).measurableSet

/-- The real indicator of the centered arc. -/
def haarArcIndicator (a : ℝ) : HaarCircle → ℝ :=
  (haarArc a).indicator (fun _ => 1)

/-- A positive sequence of radii tending to zero. -/
def haarArcRadius (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem haarArcRadius_pos (n : ℕ) : 0 < haarArcRadius n := by
  unfold haarArcRadius
  positivity

theorem tendsto_haarArcRadius : Tendsto haarArcRadius atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- Continuous real cutoffs, equal to one on the arc. -/
def haarArcCutoffReal (a : ℝ) (n : ℕ) : C(HaarCircle, ℝ) where
  toFun t := (thickenedIndicator (haarArcRadius_pos n) (haarArc a) t : ℝ)
  continuous_toFun := NNReal.continuous_coe.comp
    (thickenedIndicator (haarArcRadius_pos n) (haarArc a)).continuous

/-- The same cutoffs in the complex continuous functional calculus. -/
def haarArcCutoff (a : ℝ) (n : ℕ) : C(HaarCircle, ℂ) where
  toFun t := (haarArcCutoffReal a n t : ℂ)
  continuous_toFun := Complex.continuous_ofReal.comp (haarArcCutoffReal a n).continuous

theorem haarArcCutoffReal_nonneg (a : ℝ) (n : ℕ) (t : HaarCircle) :
    0 ≤ haarArcCutoffReal a n t := NNReal.coe_nonneg _

theorem haarArcCutoffReal_le_one (a : ℝ) (n : ℕ) (t : HaarCircle) :
    haarArcCutoffReal a n t ≤ 1 := by
  exact_mod_cast thickenedIndicator_le_one (haarArcRadius_pos n) (haarArc a) t

theorem haarArcCutoffReal_eq_one {a : ℝ} (n : ℕ) {t : HaarCircle}
    (ht : t ∈ haarArc a) : haarArcCutoffReal a n t = 1 := by
  change (thickenedIndicator (haarArcRadius_pos n) (haarArc a) t : ℝ) = 1
  rw [thickenedIndicator_one (haarArcRadius_pos n) (haarArc a) ht]
  rfl

theorem haarArcCutoffReal_mono (a : ℝ) {m n : ℕ} (hmn : m ≤ n) (t : HaarCircle) :
    haarArcCutoffReal a n t ≤ haarArcCutoffReal a m t := by
  have hr : haarArcRadius n ≤ haarArcRadius m := by
    unfold haarArcRadius
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hmn 1
  exact_mod_cast thickenedIndicator_mono (haarArcRadius_pos n) (haarArcRadius_pos m)
    hr (haarArc a) t

theorem norm_haarArcCutoff_apply_le_one (a : ℝ) (n : ℕ) (t : HaarCircle) :
    ‖haarArcCutoff a n t‖ ≤ 1 := by
  change ‖(haarArcCutoffReal a n t : ℂ)‖ ≤ 1
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (haarArcCutoffReal_nonneg a n t)]
  exact haarArcCutoffReal_le_one a n t

theorem norm_haarArcCutoff_le_one (a : ℝ) (n : ℕ) : ‖haarArcCutoff a n‖ ≤ 1 := by
  apply (ContinuousMap.norm_le (haarArcCutoff a n) (by norm_num)).2
  exact norm_haarArcCutoff_apply_le_one a n

@[simp]
theorem star_haarArcCutoff (a : ℝ) (n : ℕ) : star (haarArcCutoff a n) = haarArcCutoff a n := by
  ext t
  change star (haarArcCutoffReal a n t : ℂ) = (haarArcCutoffReal a n t : ℂ)
  simp

theorem haarArcIndicator_nonneg (a : ℝ) (t : HaarCircle) : 0 ≤ haarArcIndicator a t := by
  by_cases ht : t ∈ haarArc a <;> simp [haarArcIndicator, ht]

theorem haarArcIndicator_le_one (a : ℝ) (t : HaarCircle) : haarArcIndicator a t ≤ 1 := by
  by_cases ht : t ∈ haarArc a <;> simp [haarArcIndicator, ht]

theorem measurable_haarArcIndicator (a : ℝ) : Measurable (haarArcIndicator a) :=
  measurable_const.indicator (measurableSet_haarArc a)

/-- Convergence holds even at the two endpoints, since the arc is closed. -/
theorem tendsto_haarArcCutoffReal (a : ℝ) (t : HaarCircle) :
    Tendsto (fun n => haarArcCutoffReal a n t) atTop (𝓝 (haarArcIndicator a t)) := by
  have h := thickenedIndicator_tendsto_indicator_closure haarArcRadius_pos
    tendsto_haarArcRadius (haarArc a)
  rw [tendsto_pi_nhds] at h
  have ht := NNReal.continuous_coe.continuousAt.tendsto.comp (h t)
  change Tendsto (fun n => haarArcCutoffReal a n t) atTop
    (𝓝 (((closure (haarArc a)).indicator (fun _ => (1 : ℝ≥0)) t : ℝ≥0) : ℝ)) at ht
  convert ht using 1
  by_cases hmem : t ∈ haarArc a <;>
    simp [(isClosed_haarArc a).closure_eq, haarArcIndicator, hmem]

theorem tendsto_haarArcCutoff (a : ℝ) (t : HaarCircle) :
    Tendsto (fun n => haarArcCutoff a n t) atTop (𝓝 (haarArcIndicator a t : ℂ)) :=
  Complex.continuous_ofReal.continuousAt.tendsto.comp (tendsto_haarArcCutoffReal a t)

theorem haarArcCutoff_error_sq_le_four (a : ℝ) (n : ℕ) (t : HaarCircle) :
    ‖haarArcCutoff a n t - (haarArcIndicator a t : ℂ)‖ ^ 2 ≤ 4 := by
  have hi : ‖(haarArcIndicator a t : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (haarArcIndicator_nonneg a t)]
    exact haarArcIndicator_le_one a t
  have hs := (norm_sub_le (haarArcCutoff a n t) (haarArcIndicator a t : ℂ)).trans
    (add_le_add (norm_haarArcCutoff_apply_le_one a n t) hi)
  nlinarith [norm_nonneg (haarArcCutoff a n t - (haarArcIndicator a t : ℂ))]

theorem integrable_haarArcCutoff_error_sq (a : ℝ) (n : ℕ) :
    Integrable (fun t => ‖haarArcCutoff a n t - (haarArcIndicator a t : ℂ)‖ ^ 2)
      (AddCircle.haarAddCircle (T := 2 * Real.pi)) := by
  apply (integrable_const (4 : ℝ)).mono'
  · exact (((haarArcCutoff a n).continuous.measurable.sub
      (Complex.continuous_ofReal.measurable.comp (measurable_haarArcIndicator a))).norm.pow_const
        2).aestronglyMeasurable
  · filter_upwards [] with t
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact haarArcCutoff_error_sq_le_four a n t

/-- Scalar Haar `L²` convergence of the actual continuous cutoffs. -/
theorem tendsto_integral_haarArcCutoff_error_sq (a : ℝ) :
    Tendsto (fun n => ∫ t, ‖haarArcCutoff a n t - (haarArcIndicator a t : ℂ)‖ ^ 2
      ∂(AddCircle.haarAddCircle (T := 2 * Real.pi))) atTop (𝓝 0) := by
  have hmeas : ∀ n, AEStronglyMeasurable
      (fun t => ‖haarArcCutoff a n t - (haarArcIndicator a t : ℂ)‖ ^ 2)
      (AddCircle.haarAddCircle (T := 2 * Real.pi)) := by
    intro n
    exact (((haarArcCutoff a n).continuous.measurable.sub
      (Complex.continuous_ofReal.measurable.comp (measurable_haarArcIndicator a))).norm.pow_const
        2).aestronglyMeasurable
  have hbound : ∀ n, ∀ᵐ t ∂(AddCircle.haarAddCircle (T := 2 * Real.pi)),
      ‖‖haarArcCutoff a n t - (haarArcIndicator a t : ℂ)‖ ^ 2‖ ≤ (4 : ℝ) := by
    intro n
    filter_upwards [] with t
    have hi : ‖(haarArcIndicator a t : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (haarArcIndicator_nonneg a t)]
      exact haarArcIndicator_le_one a t
    have hs := (norm_sub_le (haarArcCutoff a n t) (haarArcIndicator a t : ℂ)).trans
      (add_le_add (norm_haarArcCutoff_apply_le_one a n t) hi)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [norm_nonneg (haarArcCutoff a n t - (haarArcIndicator a t : ℂ))]
  have hlim : ∀ᵐ t ∂(AddCircle.haarAddCircle (T := 2 * Real.pi)),
      Tendsto (fun n => ‖haarArcCutoff a n t - (haarArcIndicator a t : ℂ)‖ ^ 2)
        atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [] with t
    have hc : Tendsto (fun _ : ℕ => (haarArcIndicator a t : ℂ)) atTop
        (𝓝 (haarArcIndicator a t : ℂ)) := tendsto_const_nhds
    simpa using ((tendsto_haarArcCutoff a t).sub hc).norm.pow 2
  simpa using tendsto_integral_of_dominated_convergence (fun _ => (4 : ℝ)) hmeas
    (integrable_const 4) hbound hlim

/-- A direct scalar square-distance estimate, usable without constructing an
`L²` space. -/
theorem integral_haarArcCutoff_sub_sq_le (a : ℝ) (m n : ℕ) :
    (∫ t, ‖haarArcCutoff a m t - haarArcCutoff a n t‖ ^ 2
      ∂(AddCircle.haarAddCircle (T := 2 * Real.pi))) ≤
      2 * (∫ t, ‖haarArcCutoff a m t - (haarArcIndicator a t : ℂ)‖ ^ 2
        ∂(AddCircle.haarAddCircle (T := 2 * Real.pi))) +
      2 * (∫ t, ‖haarArcCutoff a n t - (haarArcIndicator a t : ℂ)‖ ^ 2
        ∂(AddCircle.haarAddCircle (T := 2 * Real.pi))) := by
  have hm := integrable_haarArcCutoff_error_sq a m
  have hn := integrable_haarArcCutoff_error_sq a n
  have hmn : Integrable (fun t => ‖haarArcCutoff a m t - haarArcCutoff a n t‖ ^ 2)
      (AddCircle.haarAddCircle (T := 2 * Real.pi)) := by
    apply (integrable_const (4 : ℝ)).mono'
    · exact (((haarArcCutoff a m).continuous.sub (haarArcCutoff a n).continuous).norm.pow
        2).aestronglyMeasurable
    · filter_upwards [] with t
      have h := (norm_sub_le (haarArcCutoff a m t) (haarArcCutoff a n t)).trans
        (add_le_add (norm_haarArcCutoff_apply_le_one a m t) (norm_haarArcCutoff_apply_le_one a n t))
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [norm_nonneg (haarArcCutoff a m t - haarArcCutoff a n t)]
  calc
    _ ≤ ∫ t, 2 * ‖haarArcCutoff a m t - (haarArcIndicator a t : ℂ)‖ ^ 2 +
        2 * ‖haarArcCutoff a n t - (haarArcIndicator a t : ℂ)‖ ^ 2
        ∂(AddCircle.haarAddCircle (T := 2 * Real.pi)) := by
      apply integral_mono hmn ((hm.const_mul 2).add (hn.const_mul 2))
      intro t
      change ‖haarArcCutoff a m t - haarArcCutoff a n t‖ ^ 2 ≤
        2 * ‖haarArcCutoff a m t - (haarArcIndicator a t : ℂ)‖ ^ 2 +
        2 * ‖haarArcCutoff a n t - (haarArcIndicator a t : ℂ)‖ ^ 2
      have htri : ‖haarArcCutoff a m t - haarArcCutoff a n t‖ ≤
          ‖haarArcCutoff a m t - (haarArcIndicator a t : ℂ)‖ +
          ‖haarArcCutoff a n t - (haarArcIndicator a t : ℂ)‖ := by
        calc
          _ = ‖(haarArcCutoff a m t - (haarArcIndicator a t : ℂ)) -
              (haarArcCutoff a n t - (haarArcIndicator a t : ℂ))‖ := by congr 1; ring
          _ ≤ _ := norm_sub_le _ _
      have hsquare := pow_le_pow_left₀
        (norm_nonneg (haarArcCutoff a m t - haarArcCutoff a n t)) htri 2
      nlinarith [sq_nonneg (‖haarArcCutoff a m t - (haarArcIndicator a t : ℂ)‖ -
        ‖haarArcCutoff a n t - (haarArcIndicator a t : ℂ)‖),
        norm_nonneg (haarArcCutoff a m t - haarArcCutoff a n t),
        norm_nonneg (haarArcCutoff a m t - (haarArcIndicator a t : ℂ)),
        norm_nonneg (haarArcCutoff a n t - (haarArcIndicator a t : ℂ))]
    _ = _ := by rw [integral_add (hm.const_mul 2) (hn.const_mul 2),
      integral_const_mul, integral_const_mul]

theorem haarArcCutoff_square_integral_cauchy (a : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      (∫ t, ‖haarArcCutoff a m t - haarArcCutoff a n t‖ ^ 2
        ∂(AddCircle.haarAddCircle (T := 2 * Real.pi))) < ε := by
  have hev := (tendsto_order.1 (tendsto_integral_haarArcCutoff_error_sq a)).2
    (ε / 4) (by linarith)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨N, fun m hm n hn => ?_⟩
  have hm' := hN m hm
  have hn' := hN n hn
  have h := integral_haarArcCutoff_sub_sq_le a m n
  linarith

theorem haarArcCutoff_idempotency_error_sq_le (a : ℝ) (n : ℕ) (t : HaarCircle) :
    ‖haarArcCutoff a n t * haarArcCutoff a n t - haarArcCutoff a n t‖ ^ 2 ≤
      ‖haarArcCutoff a n t - (haarArcIndicator a t : ℂ)‖ ^ 2 := by
  by_cases ht : t ∈ haarArc a
  · have hone := haarArcCutoffReal_eq_one n ht
    simp [haarArcCutoff, hone, haarArcIndicator, ht]
  · simp only [haarArcIndicator, Set.indicator_of_notMem ht, Complex.ofReal_zero, sub_zero]
    let c := haarArcCutoffReal a n t
    have hc0 : 0 ≤ c := haarArcCutoffReal_nonneg a n t
    have hc1 : c ≤ 1 := haarArcCutoffReal_le_one a n t
    have hmul : c * c ≤ c := by nlinarith [mul_nonneg hc0 (sub_nonneg.mpr hc1)]
    change ‖(c : ℂ) * (c : ℂ) - (c : ℂ)‖ ^ 2 ≤ ‖(c : ℂ)‖ ^ 2
    have heq : (c : ℂ) * (c : ℂ) - (c : ℂ) = ((c * c - c : ℝ) : ℂ) := by push_cast; rfl
    rw [heq, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonpos (by nlinarith : c * c - c ≤ 0), abs_of_nonneg hc0]
    have hsq : 0 ≤ c * c := mul_nonneg hc0 hc0
    exact pow_le_pow_left₀ (by linarith) (by linarith) 2

/-- The approximate projections become idempotent in scalar Haar `L²`. -/
theorem tendsto_integral_haarArcCutoff_idempotency_error_sq (a : ℝ) :
    Tendsto (fun n => ∫ t,
      ‖haarArcCutoff a n t * haarArcCutoff a n t - haarArcCutoff a n t‖ ^ 2
        ∂(AddCircle.haarAddCircle (T := 2 * Real.pi))) atTop (𝓝 0) := by
  apply squeeze_zero
    (fun n => integral_nonneg fun t => sq_nonneg _)
    (fun n => ?_) (tendsto_integral_haarArcCutoff_error_sq a)
  have he := integrable_haarArcCutoff_error_sq a n
  have hi : Integrable (fun t =>
      ‖haarArcCutoff a n t * haarArcCutoff a n t - haarArcCutoff a n t‖ ^ 2)
      (AddCircle.haarAddCircle (T := 2 * Real.pi)) := by
    apply he.mono'
    · exact ((((haarArcCutoff a n).continuous.mul (haarArcCutoff a n).continuous).sub
        (haarArcCutoff a n).continuous).norm.pow 2).aestronglyMeasurable
    · filter_upwards [] with t
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact haarArcCutoff_idempotency_error_sq_le a n t
  exact integral_mono hi he (haarArcCutoff_idempotency_error_sq_le a n)

/-- The mass of a centered arc under probability Haar measure. -/
theorem integral_haarArcIndicator {a : ℝ} (ha : 0 ≤ a) (hapi : a ≤ Real.pi) :
    (∫ t, haarArcIndicator a t ∂(AddCircle.haarAddCircle (T := 2 * Real.pi))) =
      a / Real.pi := by
  rw [AddCircle.integral_haarAddCircle]
  have hmass : (∫ t : HaarCircle, haarArcIndicator a t) = 2 * a := by
    change (∫ t : HaarCircle, (haarArc a).indicator (fun _ => (1 : ℝ)) t) = _
    rw [integral_indicator_const (1 : ℝ) (measurableSet_haarArc a), smul_eq_mul, mul_one]
    change (volume (Metric.closedBall (0 : HaarCircle) a)).toReal = _
    rw [AddCircle.volume_closedBall, min_eq_right (by linarith : 2 * a ≤ 2 * Real.pi),
      ENNReal.toReal_ofReal (by positivity)]
  rw [hmass, smul_eq_mul]
  field_simp

theorem haarArc_measureReal {a : ℝ} (ha : 0 ≤ a) (hapi : a ≤ Real.pi) :
    (AddCircle.haarAddCircle (T := 2 * Real.pi)).real (haarArc a) = a / Real.pi := by
  rw [← integral_indicator_one (measurableSet_haarArc a)]
  exact integral_haarArcIndicator ha hapi

/-- The cutoff integrals converge to the arc's normalized angular length. -/
theorem tendsto_integral_haarArcCutoffReal {a : ℝ} (ha : 0 ≤ a) (hapi : a ≤ Real.pi) :
    Tendsto (fun n => ∫ t, haarArcCutoffReal a n t
      ∂(AddCircle.haarAddCircle (T := 2 * Real.pi))) atTop (𝓝 (a / Real.pi)) := by
  rw [← integral_haarArcIndicator ha hapi]
  apply tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
  · intro n
    exact (haarArcCutoffReal a n).continuous.aestronglyMeasurable
  · exact integrable_const 1
  · intro n
    filter_upwards [] with t
    rw [Real.norm_eq_abs, abs_of_nonneg (haarArcCutoffReal_nonneg a n t)]
    exact haarArcCutoffReal_le_one a n t
  · exact Filter.Eventually.of_forall (tendsto_haarArcCutoffReal a)

/-- On the principal angular interval, the metric arc is the ordinary interval. -/
theorem mem_haarArc_coe_iff {a t : ℝ} (ht : |t| ≤ Real.pi) :
    (t : HaarCircle) ∈ haarArc a ↔ |t| ≤ a := by
  change dist (t : HaarCircle) 0 ≤ a ↔ _
  rw [dist_zero_right]
  rw [(AddCircle.norm_coe_eq_abs_iff (2 * Real.pi) (by positivity : 2 * Real.pi ≠ 0)).2 (by
    simpa [abs_of_pos (by positivity : 0 < 2 * Real.pi)] using ht)]

/-- Scalar integration over the arc complement is exactly the two angular tails. -/
theorem integral_haarArc_compl {a : ℝ} (ha : 0 ≤ a) (hapi : a ≤ Real.pi)
    (g : C(HaarCircle, ℝ)) :
    (∫ t, (haarArc a)ᶜ.indicator g t
      ∂(AddCircle.haarAddCircle (T := 2 * Real.pi))) =
      ((∫ t in -Real.pi..-a, g (t : HaarCircle)) +
        ∫ t in a..Real.pi, g (t : HaarCircle)) / (2 * Real.pi) := by
  let F : HaarCircle → ℝ := (haarArc a)ᶜ.indicator g
  have hg : Integrable g (volume : Measure HaarCircle) :=
    (integrable_const ‖g‖).mono' g.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall g.norm_coe_le_norm)
  have hF : Integrable F (volume : Measure HaarCircle) :=
    hg.indicator (measurableSet_haarArc a).compl
  have hFint : IntervalIntegrable (fun t : ℝ => F (t : HaarCircle)) volume
      (-Real.pi) Real.pi := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [Real.pi_pos])]
    have hm := (AddCircle.measurePreserving_mk (2 * Real.pi) (-Real.pi)).integrable_comp_of_integrable hF
    rw [show -Real.pi + 2 * Real.pi = Real.pi by ring] at hm
    exact hm
  have hL : IntervalIntegrable (fun t : ℝ => F (t : HaarCircle)) volume
      (-Real.pi) (-a) := by
    apply hFint.mono_set
    rw [Set.uIcc_of_le (by linarith : -Real.pi ≤ -a),
      Set.uIcc_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
    exact Set.Icc_subset_Icc le_rfl (by linarith)
  have hM : IntervalIntegrable (fun t : ℝ => F (t : HaarCircle)) volume (-a) a := by
    apply hFint.mono_set
    rw [Set.uIcc_of_le (by linarith : -a ≤ a),
      Set.uIcc_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
    exact Set.Icc_subset_Icc (by linarith) hapi
  have hR : IntervalIntegrable (fun t : ℝ => F (t : HaarCircle)) volume a Real.pi := by
    apply hFint.mono_set
    rw [Set.uIcc_of_le hapi,
      Set.uIcc_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
    exact Set.Icc_subset_Icc (by linarith [Real.pi_pos]) le_rfl
  have eL : (∫ t in -Real.pi..-a, F (t : HaarCircle)) =
      ∫ t in -Real.pi..-a, g (t : HaarCircle) := by
    apply intervalIntegral.integral_congr_Ioo_of_le (by linarith)
    intro t ht
    have ht0 : t < 0 := lt_of_lt_of_le ht.2 (neg_nonpos.mpr ha)
    have htpi : |t| ≤ Real.pi := by rw [abs_of_neg ht0]; linarith [ht.1]
    have hnot : (t : HaarCircle) ∉ haarArc a := by
      rw [mem_haarArc_coe_iff htpi, abs_of_neg ht0]
      linarith [ht.2]
    simp [F, hnot]
  have eM : (∫ t in -a..a, F (t : HaarCircle)) = 0 := by
    calc
      _ = ∫ t in -a..a, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le (by linarith)
        intro t ht
        have htA : |t| ≤ a := abs_le.mpr ⟨ht.1.le, ht.2.le⟩
        have hmem : (t : HaarCircle) ∈ haarArc a :=
          (mem_haarArc_coe_iff (htA.trans hapi)).2 htA
        simp [F, hmem]
      _ = 0 := by simp
  have eR : (∫ t in a..Real.pi, F (t : HaarCircle)) =
      ∫ t in a..Real.pi, g (t : HaarCircle) := by
    apply intervalIntegral.integral_congr_Ioo_of_le hapi
    intro t ht
    have ht0 : 0 < t := lt_of_le_of_lt ha ht.1
    have htpi : |t| ≤ Real.pi := by rw [abs_of_pos ht0]; exact ht.2.le
    have hnot : (t : HaarCircle) ∉ haarArc a := by
      rw [mem_haarArc_coe_iff htpi, abs_of_pos ht0]
      exact not_le.mpr ht.1
    simp [F, hnot]
  rw [AddCircle.integral_haarAddCircle,
    ← AddCircle.intervalIntegral_preimage (2 * Real.pi) (-Real.pi)]
  change (2 * Real.pi)⁻¹ • (∫ t in -Real.pi..(-Real.pi + 2 * Real.pi), F (t : HaarCircle)) = _
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring,
    ← intervalIntegral.integral_add_adjacent_intervals (hL.trans hM) hR,
    ← intervalIntegral.integral_add_adjacent_intervals hL hM, eL, eM, eR]
  simp only [add_zero, smul_eq_mul, div_eq_mul_inv]
  ring

/-- Continuous weighted traces of the complementary cutoffs converge to the
corresponding integral off the closed arc. -/
theorem tendsto_integral_haarArcCutoff_compl_mul (a : ℝ) (g : C(HaarCircle, ℝ)) :
    Tendsto (fun n => ∫ t, g t * (1 - haarArcCutoffReal a n t)
      ∂(AddCircle.haarAddCircle (T := 2 * Real.pi))) atTop
      (𝓝 (∫ t, (haarArc a)ᶜ.indicator g t
        ∂(AddCircle.haarAddCircle (T := 2 * Real.pi)))) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖g‖)
  · intro n
    exact (g.continuous.mul (continuous_const.sub (haarArcCutoffReal a n).continuous)).aestronglyMeasurable
  · exact integrable_const ‖g‖
  · intro n
    filter_upwards [] with t
    rw [norm_mul, Real.norm_of_nonneg
      (sub_nonneg.mpr (haarArcCutoffReal_le_one a n t))]
    calc
      _ ≤ ‖g t‖ * 1 := mul_le_mul_of_nonneg_left
        (by linarith [haarArcCutoffReal_nonneg a n t]) (norm_nonneg _)
      _ ≤ ‖g‖ := by simpa using g.norm_coe_le_norm t
  · filter_upwards [] with t
    have hc : Tendsto (fun n => (1 : ℝ) - haarArcCutoffReal a n t) atTop
        (𝓝 (1 - haarArcIndicator a t)) :=
      tendsto_const_nhds.sub (tendsto_haarArcCutoffReal a t)
    have h := hc.const_mul (g t)
    by_cases ht : t ∈ haarArc a <;> simpa [haarArcIndicator, ht] using h

/-- The actual normalized Fourier polynomial on the quotient circle. -/
def haarCirclePolynomial (N : ℕ) : C(HaarCircle, ℂ) :=
  (Real.sqrt (N : ℝ))⁻¹ • ∑ k ∈ Finset.range N, fourier ((k + 1 : ℕ) : ℤ)

theorem haarCirclePolynomial_coe (N : ℕ) (t : ℝ) :
    haarCirclePolynomial N (t : HaarCircle) = haarPolynomial N t := by
  unfold haarCirclePolynomial haarPolynomial
  simp only [ContinuousMap.smul_apply, ContinuousMap.sum_apply]
  congr 1
  rw [haarGeometricSum_eq_sum_exp]
  apply Finset.sum_congr rfl
  intro k hk
  rw [fourier_coe_apply]
  congr 1
  push_cast
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

/-- The scalar energy outside the actual circle arc is the tail already estimated
by the geometric-sum calculation. -/
theorem integral_haarCirclePolynomial_tail {a : ℝ} (ha : 0 ≤ a) (hapi : a ≤ Real.pi)
    (N : ℕ) :
    (∫ t, (haarArc a)ᶜ.indicator (fun t => ‖haarCirclePolynomial N t‖ ^ 2) t
      ∂(AddCircle.haarAddCircle (T := 2 * Real.pi))) = haarTailEnergy N a := by
  let g : C(HaarCircle, ℝ) := ⟨fun t => ‖haarCirclePolynomial N t‖ ^ 2, by fun_prop⟩
  have h := integral_haarArc_compl ha hapi g
  simpa only [g, ContinuousMap.coe_mk, haarCirclePolynomial_coe, haarTailEnergy,
    min_eq_left hapi, add_comm] using h

theorem tendsto_integral_haarCirclePolynomial_cutoff_compl {a : ℝ}
    (ha : 0 ≤ a) (hapi : a ≤ Real.pi) (N : ℕ) :
    Tendsto (fun n => ∫ t, ‖haarCirclePolynomial N t‖ ^ 2 * (1 - haarArcCutoffReal a n t)
      ∂(AddCircle.haarAddCircle (T := 2 * Real.pi))) atTop (𝓝 (haarTailEnergy N a)) := by
  let g : C(HaarCircle, ℝ) := ⟨fun t => ‖haarCirclePolynomial N t‖ ^ 2, by fun_prop⟩
  have h := tendsto_integral_haarArcCutoff_compl_mul a g
  simpa only [g, ContinuousMap.coe_mk, integral_haarCirclePolynomial_tail ha hapi N] using h

section FunctionalCalculus

variable {B : Type*} [CStarAlgebra B]

/-- The scalar Cauchy estimate transfers directly through the Haar functional
calculus, in the form required by bounded tracial completeness. -/
theorem haarArcCutoff_traceTwoNorm_cauchy (τ : FaithfulTracialState B) (v : unitary B)
    (hhaar : ∀ k : ℤ, k ≠ 0 → τ.toLinearMap (haarPower v k) = 0)
    (Φ : C(HaarCircle, ℂ) →⋆ₐ[ℂ] B)
    (hΦ : ∀ n : ℤ, Φ (fourier n) = haarPower v n) (a : ℝ) :
    ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      traceTwoNorm τ (Φ (haarArcCutoff a m) - Φ (haarArcCutoff a n)) < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := haarArcCutoff_square_integral_cauchy a (sq_pos_of_pos hε)
  refine ⟨N, fun m hm n hn => ?_⟩
  rw [← map_sub, traceTwoNorm_haar_functional τ v hhaar Φ hΦ]
  exact (Real.sqrt_lt' hε).2 (hN m hm n hn)

/-- The same actual functional-calculus cutoffs are asymptotically idempotent. -/
theorem tendsto_traceTwoNorm_haarArcCutoff_idempotency (τ : FaithfulTracialState B)
    (v : unitary B) (hhaar : ∀ k : ℤ, k ≠ 0 → τ.toLinearMap (haarPower v k) = 0)
    (Φ : C(HaarCircle, ℂ) →⋆ₐ[ℂ] B)
    (hΦ : ∀ n : ℤ, Φ (fourier n) = haarPower v n) (a : ℝ) :
    Tendsto (fun n => traceTwoNorm τ
      (Φ (haarArcCutoff a n) * Φ (haarArcCutoff a n) - Φ (haarArcCutoff a n)))
      atTop (𝓝 0) := by
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp
    (tendsto_integral_haarArcCutoff_idempotency_error_sq a)
  simp only [Real.sqrt_zero] at h
  convert h using 1
  funext n
  rw [← map_mul, ← map_sub, traceTwoNorm_haar_functional τ v hhaar Φ hΦ]
  rfl

end FunctionalCalculus

end

end KadisonKastler

end OAI

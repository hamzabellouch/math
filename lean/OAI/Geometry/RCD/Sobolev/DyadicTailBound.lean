import OAI.Geometry.RCD.Sobolev.DyadicSupportCoercivity
import OAI.Geometry.RCD.Sobolev.DirichletTail
import OAI.Geometry.RCD.Metric.L2LevelMeasure

namespace OAI

/-! # Dyadic distribution estimates from support-sensitive coercivity -/

open Set Metric MeasureTheory Filter
open scoped ENNReal

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

/-- An absolute-value truncation turns the dyadic support estimate into
faster-than-quadratic decay of the level-set measures. -/
theorem NoncollapsedRCD.dyadic_tail_bound {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) :
    ∃ C D : ℝ, 0 < C ∧ 2 ≤ D ∧ ∀ (p : X) (R : ℝ), 0 < R → -1 ≤ K*R^2 →
      ∀ w : SobolevSpace.dirichlet (hausdorff n X) hX.quadratic (ball p R),
      ∀ (t : ℝ), 0 < t → ∀ k : ℕ,
      2*D^(k+1)*‖SobolevSpace.toLp (hausdorff n X) hX.quadratic w.val‖^2 ≤
        (hausdorff n X).real (ball p R)*t^2 →
      t^2 * (hausdorff n X).real (ball p R ∩
        {x | 2*t < |SobolevSpace.toLp (hausdorff n X) hX.quadratic w.val x|}) ≤
        C*(R/2^k)^2 * energyForm (hausdorff n X) hX.quadratic w.val w.val := by
  obtain ⟨C, D, hC, hD, hsupport⟩ := hX.dyadic_support_coercivity hn
  refine ⟨C, D, hC, hD, ?_⟩
  intro p R hR hcurv w t ht k hsize
  let μ := hausdorff n X
  let u := SobolevSpace.toLp μ hX.quadratic w.val
  let A := ball p R ∩ {x | t < |u x|}
  have hA : MeasurableSet A := measurableSet_ball.inter
    (measurableSet_lt measurable_const (Lp.stronglyMeasurable u).measurable.abs)
  have hAfin : μ A ≠ ∞ := ne_top_of_le_ne_top
    (hX.finiteOnBounded (ball p R) isBounded_ball).ne (measure_mono inter_subset_left)
  have hlevel : ∀ᵐ x ∂μ.restrict A, t ≤ |u x| :=
    (ae_restrict_mem hA).mono (fun _ hx => hx.2.le)
  have hMarkov := lp_level_measure_le μ u hAfin ht.le hlevel
  have hAsmall : 2*D^(k+1)*μ.real A ≤ μ.real (ball p R) := by
    have hm := mul_le_mul_of_nonneg_left hMarkov
      (show 0 ≤ 2*D^(k+1) by positivity)
    change 2*D^(k+1)*‖u‖^2 ≤ μ.real (ball p R)*t^2 at hsize
    nlinarith [sq_pos_of_pos ht]
  obtain ⟨v, hv, henergy⟩ := exists_dirichlet_absolute_tail μ hX.quadratic (ball p R) w ht.le
  let z := SobolevSpace.toLp μ hX.quadratic v.val
  have hz : z =ᵐ[μ.restrict Aᶜ] 0 := by
    apply (ae_restrict_iff' hA.compl).mpr
    have hzout := SobolevSpace.dirichlet_zero_off μ hX.quadratic (ball p R) measurableSet_ball v
    filter_upwards [hv, (ae_restrict_iff' measurableSet_ball.compl).mp hzout] with x hx hxout hxA
    by_cases hxball : x ∈ ball p R
    · have hxlow : |u x| ≤ t := le_of_not_gt (fun h => hxA ⟨hxball, h⟩)
      change z x = 0
      rw [show z x = max (|u x|-t) 0 from hx]
      exact max_eq_right (sub_nonpos.mpr hxlow)
    · exact hxout hxball
  have hbound := hsupport p R hR hcurv v.val A hA inter_subset_left hz k hAsmall
  rw [dirichlet_integral_square_eq_norm_square μ hX.quadratic measurableSet_ball v] at hbound
  let B := ball p R ∩ {x | 2*t < |u x|}
  have hB : MeasurableSet B := measurableSet_ball.inter
    (measurableSet_lt measurable_const (Lp.stronglyMeasurable u).measurable.abs)
  have hBfin : μ B ≠ ∞ := ne_top_of_le_ne_top
    (hX.finiteOnBounded (ball p R) isBounded_ball).ne (measure_mono inter_subset_left)
  have hBlevel : ∀ᵐ x ∂μ.restrict B, t ≤ |z x| := by
    filter_upwards [ae_restrict_of_ae hv, ae_restrict_mem hB] with x hx hxB
    rw [show z x = max (|u x|-t) 0 from hx, abs_of_nonneg (le_max_right _ _)]
    have hh : 2*t < |u x| := hxB.2
    linarith [le_max_left (|u x|-t) 0]
  exact (lp_level_measure_le μ z hBfin ht.le hBlevel).trans
    (hbound.trans (mul_le_mul_of_nonneg_left henergy (by positivity)))

end RegularPointCoordinates

end

end OAI

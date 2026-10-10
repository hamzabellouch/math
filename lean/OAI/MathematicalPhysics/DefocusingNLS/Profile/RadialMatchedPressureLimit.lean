import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialShootingPressureLimit
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialUniformExteriorPressure
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace OAI

/-! Weak-star pressure convergence on the full fixed matching ball. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS
open ProfileCertificate

theorem radialMatched_exterior_pressure_uniform_zero (s : ℕ → ℕ) (hs : StrictMono s)
    (z : ℕ → ProfileMatchingBall) :
    TendstoUniformlyOn (fun i r => ‖radialMatchedProfile (s i) (z i) r‖^
      (2*(s i+radialInnerShootingThreshold))) (fun _ => (0 : ℝ)) atTop
      (Ioi innerBoundaryRadius) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hs.tendsto_atTop.eventually (radialMatched_exterior_pressure_small ε hε)]
    with i hi r hr
  have ha := radialShootingA_bounds (s i) (profileMatchingParameter (z i))
  let P := ‖radialMatchedProfile (s i) (z i) r‖^(2*(s i+radialInnerShootingThreshold))
  have hP : 0 ≤ P := by positivity
  have hq : 0 ≤ P/radialShootingA (s i) := div_nonneg hP ha.1.le
  have h1 : P ≤ P/radialShootingA (s i) := by
    apply (le_div_iff₀ ha.1).2
    exact mul_le_of_le_one_right hP ha.2.le
  have hr' : innerBoundaryRadius < r := hr
  have hr2 : 1 ≤ r^2 := by nlinarith [innerBoundaryRadius_bounds.1]
  have h2 := mul_le_mul_of_nonneg_right hr2 hq
  have h2' : P/radialShootingA (s i) ≤ r^2*(P/radialShootingA (s i)) := by
    simpa only [one_mul] using h2
  have h3 := hi (z i) r hr
  rw [Real.dist_eq,zero_sub,abs_neg,abs_of_nonneg hP]
  exact h1.trans_lt (h2'.trans_lt h3)

theorem radialMatched_pressure_weakstar (s : ℕ → ℕ) (hs : StrictMono s)
    (z : ℕ → ProfileMatchingBall) (z₀ : ProfileMatchingBall)
    (hz : Tendsto z atTop (𝓝 z₀))
    (hX : ∀ i, HasRadialExterior (radialShootingNu (s i+radialInnerShootingThreshold) (z i))
      (s i+radialInnerShootingThreshold) (radialShootingM (z i)) (Real.log innerBoundaryRadius))
    (hm : ∀ i, radialMatchingMap (s i) (z i)=0)
    (R : ℝ) (hR : innerBoundaryRadius ≤ R) (φ : ℝ → ℝ)
    (hφ : Integrable φ (radialPressureMeasure R)) :
    Tendsto (fun i => ∫ r, ‖radialMatchedProfile (s i) (z i) r‖^
      (2*(s i+radialInnerShootingThreshold))*φ r ∂radialPressureMeasure R) atTop
      (𝓝 (∫ r, (Iic (radialShootingR (profileMatchingParameter z₀))).indicator
        (fun _ : ℝ => radialShootingB (profileMatchingParameter z₀)) r*φ r
          ∂radialPressureMeasure R)) := by
  let P := fun i r => ‖radialMatchedProfile (s i) (z i) r‖^
    (2*(s i+radialInnerShootingThreshold))
  let μ := radialPressureMeasure R
  have hμ : μ.restrict (Iic innerBoundaryRadius)=radialPressureMeasure innerBoundaryRadius :=
    radialPressureMeasure_restrict R innerBoundaryRadius hR
  have hPmeas (i : ℕ) : AEStronglyMeasurable (P i) μ :=
    ((radialMatchedProfile_differentiable (s i) (z i) (hX i) (hm i)).continuous.norm.pow _).aestronglyMeasurable
  have hb : ∀ᶠ i in atTop, ∀ᵐ r ∂μ, ‖P i r‖ ≤ 1 := by
    filter_upwards [hs.tendsto_atTop.eventually radialMatched_global_pressure_bound] with i hi
    apply radialPressureMeasure_bound
    intro r hr
    rw [Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ P i r by positivity)]
    exact hi (z i) r hr.1
  have hI := radialShootingInner_pressure_weakstar s hs
    (fun i => profileMatchingParameter (z i)) (profileMatchingParameter z₀)
    (continuous_profileMatchingParameter.continuousAt.tendsto.comp hz) φ
    (by simpa only [← hμ] using hφ.restrict (s := Iic innerBoundaryRadius))
  have heI (i : ℕ) :
      (∫ r, P i r*φ r ∂μ.restrict (Iic innerBoundaryRadius))=
        ∫ r, (radialShootingInnerAmplitude (s i) (profileMatchingParameter (z i)) r)^
          (2*(s i+radialInnerShootingThreshold))*φ r
            ∂radialPressureMeasure innerBoundaryRadius := by
    rw [hμ]
    apply integral_congr_ae
    apply (ae_withDensity_iff (by fun_prop)).2
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr _
    rw [show P i r = _ from congrArg (fun a : ℝ => a^(2*(s i+radialInnerShootingThreshold)))
      (radialMatchedAmplitude_eq_inner (s i) (z i) r hr)]
  have hO : Tendsto (fun i => ∫ r in Ioi innerBoundaryRadius, P i r*φ r ∂μ) atTop (𝓝 0) := by
    have ht := tendsto_integral_filter_of_dominated_convergence (μ := μ.restrict (Ioi innerBoundaryRadius))
      (F := fun i r => P i r*φ r) (f := fun _ => (0 : ℝ)) (fun r => ‖φ r‖)
      (Eventually.of_forall (fun i => (hPmeas i).restrict.mul hφ.aestronglyMeasurable.restrict))
      (by
        filter_upwards [hb] with i hi
        filter_upwards [ae_restrict_of_ae hi] with r hr
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) hr)
      hφ.norm.restrict
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
        simpa only [zero_mul] using
          ((radialMatched_exterior_pressure_uniform_zero s hs z).tendsto_at hr).mul_const (φ r))
    simpa only [integral_zero] using ht
  have hgeo := radialShooting_geometry (profileMatchingParameter z₀)
  rw [radialPressureMeasure_step_integral _ _ _ (by linarith [hgeo.2.1]) hgeo.2.2.2.1] at hI
  rw [radialPressureMeasure_step_integral _ _ _ (by linarith [hgeo.2.1])
    (hgeo.2.2.2.1.trans hR)]
  have hsum := hI.add hO
  simp only [add_zero] at hsum
  apply hsum.congr'
  filter_upwards [hb] with i hi
  have hint : Integrable (fun r => P i r*φ r) μ := hφ.bdd_mul (hPmeas i) hi
  rw [← heI]
  simpa only [compl_Iic] using integral_add_compl measurableSet_Iic hint

end DefocusingNLS

end OAI

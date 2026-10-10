import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPressureMeasure

namespace OAI

/-! The angular-gradient radial measure in dimension twelve. -/

open Set MeasureTheory
namespace DefocusingNLS

noncomputable def spectralAngularMeasure (R : ℝ) : Measure ℝ :=
  (volume.restrict (Icc 0 R)).withDensity (fun r : ℝ => ENNReal.ofReal ((max r 0)^9))

instance spectralAngularMeasure_finite (R : ℝ) : IsFiniteMeasure (spectralAngularMeasure R) := by
  have hc : Continuous (fun r : ℝ => (max r 0)^9) := by fun_prop
  have hi := hc.continuousOn.integrableOn_compact (μ := volume) (K := Icc 0 R) isCompact_Icc
  apply isFiniteMeasure_withDensity
  exact (lintegral_ofReal_ne_top_iff_integrable hi.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun r => by positivity))).2 hi

theorem spectralAngularMeasure_integral (R : ℝ) (hR : 0 ≤ R) (f : ℝ → ℝ) :
    (∫ r, f r ∂spectralAngularMeasure R)=∫ r in (0 : ℝ)..R, f r*r^9 := by
  unfold spectralAngularMeasure
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)),intervalIntegral.integral_of_le hR]
  calc
    _ = ∫ r in Icc (0 : ℝ) R, f r*r^9 := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro r hr
      change (ENNReal.ofReal ((max r 0)^9)).toReal • f r=f r*r^9
      rw [ENNReal.toReal_ofReal (by positivity),max_eq_left hr.1]
      simp only [smul_eq_mul]
      ring
    _ = _ := integral_Icc_eq_integral_Ioc

end DefocusingNLS

end OAI

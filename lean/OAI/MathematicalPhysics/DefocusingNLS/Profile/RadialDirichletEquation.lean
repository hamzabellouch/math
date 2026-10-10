import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialDirichletKernel
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace OAI

/-! The radial Green kernel solves the twelve-dimensional Poisson equation. -/

open MeasureTheory Set Filter Topology intervalIntegral
namespace DefocusingNLS

theorem continuous_radialAverage (f : ℝ → ℝ) (hf : Continuous f) :
    Continuous (radialAverage f) := by
  have hc : Continuous (fun p : ℝ × ℝ => f (p.1*p.2)*p.2^11) :=
    (hf.comp (continuous_fst.mul continuous_snd)).mul (continuous_snd.pow 11)
  exact continuous_parametric_intervalIntegral_of_continuous' hc 0 1

theorem radialAverage_zero (f : ℝ → ℝ) : radialAverage f 0=f 0/12 := by
  simp only [radialAverage,zero_mul,intervalIntegral.integral_const_mul,integral_pow]
  norm_num
  ring

theorem hasDerivAt_radialDirichletKernel (R : ℝ) (f : ℝ → ℝ) (hf : Continuous f) (r : ℝ) :
    HasDerivAt (radialDirichletKernel R f) (-r*radialAverage f r) r := by
  have hc : Continuous (fun t : ℝ => t*radialAverage f t) :=
    continuous_id.mul (continuous_radialAverage f hf)
  convert! integral_hasDerivAt_left (hc.intervalIntegrable r R)
      (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt using 1
  simp only [neg_mul]

theorem radialAverage_scaling (f : ℝ → ℝ) (r : ℝ) :
    r^12*radialAverage f r = ∫ t in (0 : ℝ)..r, f t*t^11 := by
  have h := mul_integral_comp_mul_right (a := (0 : ℝ)) (b := 1)
    (f := fun t => f t*t^11) r
  simp only [zero_mul,one_mul] at h
  rw [← h]
  unfold radialAverage
  have he : (fun t : ℝ => f (t*r)*(t*r)^11) =
      fun t => r^11*(f (r*t)*t^11) := by
    funext t
    rw [mul_comm t r]
    ring
  rw [he,intervalIntegral.integral_const_mul]
  ring

theorem hasDerivAt_radialAverage (f : ℝ → ℝ) (hf : Continuous f) (r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (radialAverage f) (f r/r-12*radialAverage f r/r) r := by
  have hc : Continuous (fun t : ℝ => f t*t^11) := hf.mul (continuous_id.pow 11)
  have hi := (hc.integral_hasStrictDerivAt 0 r).hasDerivAt
  have hp := (hasDerivAt_id r).pow 12
  have he : radialAverage f =ᶠ[𝓝 r]
      (fun t => (∫ s in (0 : ℝ)..t, f s*s^11)/t^12) := by
    filter_upwards [eventually_ne_nhds hr] with t ht
    exact (eq_div_iff (pow_ne_zero 12 ht)).2 (by
      simpa only [mul_comm] using radialAverage_scaling f t)
  convert! (hi.div hp (pow_ne_zero 12 hr)).congr_of_eventuallyEq he using 1
  rw [← radialAverage_scaling f r]
  simp only [Pi.pow_apply,id_eq]
  field_simp [hr]
  ring

theorem radialDirichletKernel_poisson (R : ℝ) (f : ℝ → ℝ) (hf : Continuous f)
    (r : ℝ) (hr : r ≠ 0) :
    -deriv (deriv (radialDirichletKernel R f)) r-
      11/r*deriv (radialDirichletKernel R f) r=f r := by
  have he : deriv (radialDirichletKernel R f) = fun t => -t*radialAverage f t := by
    funext t
    exact (hasDerivAt_radialDirichletKernel R f hf t).deriv
  have hd := ((hasDerivAt_id r).neg.mul (hasDerivAt_radialAverage f hf r hr)).deriv
  change deriv (fun t : ℝ => -t*radialAverage f t) r = _ at hd
  simp only [Pi.neg_apply,id_eq] at hd
  rw [he,hd]
  dsimp only
  field_simp [hr]
  ring

end DefocusingNLS

end OAI

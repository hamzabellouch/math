import OAI.GroupTheory.PolycyclicRecognition.Algebra.AlgebraOneParameter
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SmoothAutonomousCurve
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Normed.Ring.Units

namespace OAI

/-! # Continuous one-parameter subgroups are differentiable

An integral of the curve over a sufficiently short interval is invertible.
The subgroup identity then expresses the curve using a differentiable
primitive and multiplication by that fixed inverse.
-/

noncomputable section
namespace PolycyclicRecognition

open MeasureTheory Set Filter
open scoped Topology ContDiff

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

theorem exists_isUnit_intervalIntegral {f : ℝ → A}
    (hf : Continuous f) (hf0 : f 0 = 1) :
    ∃ a : ℝ, a ≠ 0 ∧ IsUnit (∫ s in 0..a, f s) := by
  let J : ℝ → A := fun a => ∫ s in 0..a, f s
  have hd : HasDerivAt J 1 0 := by
    simpa only [hf0] using intervalIntegral.integral_hasDerivAt_right
      (hf.intervalIntegrable 0 0) hf.aestronglyMeasurable.stronglyMeasurableAtFilter
      hf.continuousAt
  have ht : Tendsto (fun a => a⁻¹ • J a) (𝓝[≠] 0) (𝓝 (1 : A)) := by
    simpa only [zero_add, J, intervalIntegral.integral_same, sub_zero] using hd.tendsto_slope_zero
  have hu : ∀ᶠ a in 𝓝[≠] 0, IsUnit (a⁻¹ • J a) :=
    ht.eventually (Units.isOpen.mem_nhds isUnit_one)
  obtain ⟨a, hua, ha⟩ := (hu.and self_mem_nhdsWithin).exists
  have ha0 : a ≠ 0 := ha
  have hscalar : IsUnit (algebraMap ℝ A a) :=
    (isUnit_iff_ne_zero.mpr ha0).map (algebraMap ℝ A)
  refine ⟨a, ha0, ?_⟩
  simpa only [← Algebra.smul_def, smul_smul, mul_inv_cancel₀ ha0, one_smul] using
    hscalar.mul hua

theorem continuous_oneParameter_hasDerivAt_zero {f : ℝ → A}
    (hf : Continuous f) (hf0 : f 0 = 1)
    (hadd : ∀ s t, f (s + t) = f s * f t) :
    ∃ v : A, HasDerivAt f v 0 := by
  obtain ⟨a, _, u, hu⟩ := exists_isUnit_intervalIntegral hf hf0
  let J : ℝ → A := fun t => ∫ s in 0..t, f s
  have hJ (t : ℝ) : HasDerivAt J (f t) t :=
    intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 t)
      hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  have hid (t : ℝ) : J (t + a) - J t = f t * (u : A) := by
    rw [hu]
    dsimp [J]
    rw [intervalIntegral.integral_interval_sub_left
      (hf.intervalIntegrable 0 (t + a)) (hf.intervalIntegrable 0 t)]
    have htrans := intervalIntegral.integral_comp_add_left (f := f) (a := 0) (b := a) t
    rw [add_zero] at htrans
    rw [← htrans]
    simpa only [hadd, ContinuousLinearMap.mul_apply'] using
      (ContinuousLinearMap.mul ℝ A (f t)).intervalIntegral_comp_comm (hf.intervalIntegrable 0 a)
  have heq : (fun t => (J (t + a) - J t) * (↑u⁻¹ : A)) = f := by
    funext t
    rw [hid, mul_assoc, u.mul_inv, mul_one]
  have hshift : HasDerivAt (fun t : ℝ => J (t + a)) (f a) 0 := by
    have hJa : HasDerivAt J (f a) (0 + a) := by simpa only [zero_add] using hJ a
    simpa only [one_smul, Function.comp_def] using hJa.scomp (h := fun t : ℝ => t + a) 0
      ((hasDerivAt_id 0).add_const a)
  have hd := (hshift.sub (hJ 0)).mul_const (↑u⁻¹ : A)
  change HasDerivAt (fun t => (J (t + a) - J t) * (↑u⁻¹ : A)) _ 0 at hd
  rw [heq] at hd
  exact ⟨_, hd⟩

theorem continuous_oneParameter_eq_exp {f : ℝ → A}
    (hf : Continuous f) (hf0 : f 0 = 1)
    (hadd : ∀ s t, f (s + t) = f s * f t) :
    ∃ v : A, ∀ t : ℝ, f t = NormedSpace.exp (t • v) := by
  obtain ⟨v, hv⟩ := continuous_oneParameter_hasDerivAt_zero hf hf0 hadd
  exact ⟨v, oneParameter_eq_exp hf0 hadd hv⟩

theorem contDiff_continuous_oneParameter {f : ℝ → A}
    (hf : Continuous f) (hf0 : f 0 = 1)
    (hadd : ∀ s t, f (s + t) = f s * f t) :
    ContDiff ℝ ∞ f := by
  obtain ⟨v, hv⟩ := continuous_oneParameter_hasDerivAt_zero hf hf0 hadd
  exact contDiff_of_autonomous_curve (ContinuousLinearMap.mul ℝ A v).contDiff
    (oneParameter_hasDerivAt hadd hv)

end PolycyclicRecognition

end

end OAI

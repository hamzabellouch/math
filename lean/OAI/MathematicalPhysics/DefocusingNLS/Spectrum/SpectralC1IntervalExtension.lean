import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace OAI

/-! A C1 extension of classical radial data from the closed integration interval. -/

open Set
open scoped ContDiff
namespace DefocusingNLS

theorem spectralC1IntervalExtension (f : ℝ → ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hf : ∀ r ∈ Icc 0 R, DifferentiableAt ℝ f r)
    (hd : ContinuousOn (deriv f) (Icc 0 R)) :
    ∃ F : ℝ → ℂ, ContDiff ℝ 1 F ∧ EqOn F f (Icc 0 R) := by
  let c := fun r : ℝ => max 0 (min R r)
  have hc (r : ℝ) : c r ∈ Icc 0 R := by
    exact ⟨le_max_left _ _,max_le hR (min_le_left _ _)⟩
  have hce (r : ℝ) (hr : r ∈ Icc 0 R) : c r=r := by
    simp only [c,min_eq_right hr.2,max_eq_right hr.1]
  let d := fun r => deriv f (c r)
  have hdc : Continuous d := hd.comp_continuous
    (continuous_const.max (continuous_const.min continuous_id)) hc
  let F := fun r => f 0+∫ x in (0 : ℝ)..r, d x
  have hF (r : ℝ) : HasDerivAt F (d r) r :=
    (intervalIntegral.integral_hasDerivAt_right (hdc.intervalIntegrable 0 r)
      hdc.aestronglyMeasurable.stronglyMeasurableAtFilter hdc.continuousAt).const_add (f 0)
  have hFd : deriv F=d := funext (fun r => (hF r).deriv)
  refine ⟨F,contDiff_one_iff_deriv.mpr
    ⟨fun r => (hF r).differentiableAt,by simpa only [hFd] using hdc⟩,fun r hr => ?_⟩
  have hi : (∫ x in (0 : ℝ)..r, d x)=∫ x in (0 : ℝ)..r, deriv f x := by
    apply intervalIntegral.integral_congr_Ioo_of_le hr.1
    intro x hx
    exact congrArg (deriv f) (hce x ⟨hx.1.le,hx.2.le.trans hr.2⟩)
  have hj : (∫ x in (0 : ℝ)..r, deriv f x)=f r-f 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro x hx
      rw [uIcc_of_le hr.1] at hx
      exact (hf x ⟨hx.1,hx.2.trans hr.2⟩).hasDerivAt
    · exact (hd.mono (Icc_subset_Icc_right hr.2)).intervalIntegrable_of_Icc hr.1
  change f 0+(∫ x in (0 : ℝ)..r, d x)=f r
  rw [hi,hj]
  abel

end DefocusingNLS

end OAI

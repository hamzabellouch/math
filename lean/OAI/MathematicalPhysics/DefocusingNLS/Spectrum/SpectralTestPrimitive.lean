import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace OAI

/-! Compactly supported primitives for the radial weak-flux equation. -/

open Set MeasureTheory
open scoped ContDiff
namespace DefocusingNLS

theorem spectralTestPrimitive (a b : ℝ) (ψ : ℝ → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hs : Function.support ψ ⊆ Ioo a b)
    (hz : ∫ x, ψ x = 0) :
    ∃ Φ : ℝ → ℝ, ContDiff ℝ ∞ Φ ∧ HasCompactSupport Φ ∧
      tsupport Φ ⊆ Icc a b ∧ ∀ x, deriv Φ x = ψ x := by
  let Φ := fun t => ∫ x in a..t, ψ x
  have hd (t : ℝ) : HasDerivAt Φ (ψ t) t :=
    intervalIntegral.integral_hasDerivAt_right (hψ.continuous.intervalIntegrable a t)
      hψ.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter hψ.continuous.continuousAt
  have he : deriv Φ=ψ := funext (fun t => (hd t).deriv)
  have hc : ContDiff ℝ ∞ Φ := contDiff_infty_iff_deriv.mpr
    ⟨fun t => (hd t).differentiableAt,by simpa only [he] using hψ⟩
  have hzero (t : ℝ) (ht : t ∉ Icc a b) : Φ t=0 := by
    rcases not_and_or.mp ht with ht | ht
    · have hta : t < a := lt_of_not_ge ht
      change (∫ x in a..t, ψ x)=0
      rw [intervalIntegral.integral_symm]
      have hi : (∫ x in t..a, ψ x)=0 := by
        calc
          (∫ x in t..a, ψ x) = ∫ _ in t..a, (0 : ℝ) := by
            apply intervalIntegral.integral_congr_Ioo_of_le hta.le
            intro x hx
            apply Function.notMem_support.mp
            intro hxs
            exact (not_lt_of_ge (hs hxs).1.le) hx.2
          _ = 0 := intervalIntegral.integral_zero
      rw [hi,neg_zero]
    · have hbt : b < t := lt_of_not_ge ht
      change (∫ x in a..t, ψ x)=0
      rw [intervalIntegral.integral_eq_integral_of_support_subset
        (fun x hx => ⟨(hs hx).1,(hs hx).2.le.trans hbt.le⟩),hz]
  have hsup : Function.support Φ ⊆ Icc a b := by
    intro t ht
    by_contra h
    exact ht (hzero t h)
  exact ⟨Φ,hc,HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsup,
    closure_minimal hsup isClosed_Icc,fun t => (hd t).deriv⟩

end DefocusingNLS

end OAI

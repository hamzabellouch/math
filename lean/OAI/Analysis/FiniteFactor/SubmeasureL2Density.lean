import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Function.L2Space

namespace OAI

namespace FiniteFactor
open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- A finite submeasure of an L2 density has an actual nonnegative L2
Radon--Nikodym density, with no increase in its squared integral. -/
theorem submeasure_L2_density {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [SigmaFinite μ] [IsFiniteMeasure ν] (f : Ω → ℝ)
    (hf : MemLp f 2 μ) (hν : ν ≤ μ.withDensity (fun x => ENNReal.ofReal (f x))) :
    ∃ g : Ω → ℝ, Measurable g ∧ (∀ x, 0 ≤ g x) ∧
      ν = μ.withDensity (fun x => ENNReal.ofReal (g x)) ∧
      (∀ᵐ x ∂μ, g x ≤ |f x|) ∧ MemLp g 2 μ ∧
      (∫ x, g x ^ 2 ∂μ) ≤ ∫ x, f x ^ 2 ∂μ := by
  let g := fun x => (ν.rnDeriv μ x).toReal
  have hg : Measurable g := (Measure.measurable_rnDeriv ν μ).ennreal_toReal
  have hac : ν ≪ μ := (Measure.absolutelyContinuous_of_le hν).trans (withDensity_absolutelyContinuous _ _)
  have hderiv : ν.rnDeriv μ ≤ᵐ[μ] (fun x => ENNReal.ofReal (f x)) := by
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite (Measure.measurable_rnDeriv ν μ)
    intro A hA _
    calc
      _ ≤ ν A := Measure.setLIntegral_rnDeriv_le A
      _ ≤ (μ.withDensity (fun x => ENNReal.ofReal (f x))) A := hν A
      _ = _ := withDensity_apply _ hA
  have hle : ∀ᵐ x ∂μ, g x ≤ |f x| := by
    filter_upwards [hderiv] with x hx
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (hx.trans (ENNReal.ofReal_le_ofReal (le_abs_self (f x))))
    simpa only [ENNReal.toReal_ofReal (abs_nonneg (f x))] using hh
  have hlp : MemLp g 2 μ := hf.mono hg.aestronglyMeasurable (by
    filter_upwards [hle] with x hx
    change |g x| ≤ |f x|
    rw [abs_of_nonneg (show 0 ≤ g x from ENNReal.toReal_nonneg)]
    exact hx)
  refine ⟨g,hg,fun x => ENNReal.toReal_nonneg,?_,hle,hlp,?_⟩
  · rw [← Measure.withDensity_rnDeriv_eq ν μ hac]
    apply withDensity_congr_ae
    filter_upwards [Measure.rnDeriv_ne_top ν μ] with x hx
    exact (ENNReal.ofReal_toReal hx).symm
  · apply integral_mono_ae hlp.integrable_sq hf.integrable_sq
    filter_upwards [hle] with x hx
    have hg0 : 0 ≤ g x := ENNReal.toReal_nonneg
    nlinarith [sq_abs (f x)]

end
end FiniteFactor

end OAI

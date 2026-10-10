import Mathlib

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped ENNReal

namespace Invariant233.SubmeasureDensity

theorem rnDeriv_le_of_le_withDensity
    {X : Type*} [MeasurableSpace X] {μ ν : Measure X} [SigmaFinite μ]
    {f : X → ℝ≥0∞} (hν : ν ≤ μ.withDensity f) :
    ν.rnDeriv μ ≤ᵐ[μ] f := by
  apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite (ν.measurable_rnDeriv μ)
  intro s hs _
  calc
    (∫⁻ x in s, ν.rnDeriv μ x ∂μ) ≤ ν s := Measure.setLIntegral_rnDeriv_le s
    _ ≤ μ.withDensity f s := hν s
    _ = ∫⁻ x in s, f x ∂μ := withDensity_apply f hs

theorem exists_lp_density_of_le_withDensity
    {X : Type*} [MeasurableSpace X] {μ ν : Measure X} [SigmaFinite μ]
    [IsFiniteMeasure ν] {p : ℝ≥0∞} (f : Lp ℝ p μ)
    (hf : 0 ≤ᵐ[μ] f)
    (hν : ν ≤ μ.withDensity (fun x => ENNReal.ofReal (f x))) :
    ∃ g : Lp ℝ p μ, (0 ≤ᵐ[μ] g) ∧ (g ≤ᵐ[μ] f) ∧
      ν = μ.withDensity (fun x => ENNReal.ofReal (g x)) ∧ ‖g‖ ≤ ‖f‖ := by
  let r : X → ℝ := fun x => (ν.rnDeriv μ x).toReal
  have hrmeas : Measurable r := (ν.measurable_rnDeriv μ).ennreal_toReal
  have hrnonneg : ∀ x, 0 ≤ r x := fun _ => ENNReal.toReal_nonneg
  have hrle : r ≤ᵐ[μ] f := by
    filter_upwards [rnDeriv_le_of_le_withDensity hν, hf] with x hx hfx
    calc
      r x ≤ (ENNReal.ofReal (f x)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hx
      _ = f x := ENNReal.toReal_ofReal hfx
  have hrnorm : ∀ᵐ x ∂μ, ‖r x‖ ≤ ‖f x‖ := by
    filter_upwards [hrle, hf] with x hx hfx
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hrnonneg x), abs_of_nonneg hfx] using hx
  have hrLp : MemLp r p μ := (Lp.memLp f).mono hrmeas.aestronglyMeasurable hrnorm
  have hrac : ν ≪ μ :=
    (Measure.absolutelyContinuous_of_le hν).trans (withDensity_absolutelyContinuous _ _)
  refine ⟨hrLp.toLp r, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hrLp.coeFn_toLp] with x hx
    rw [hx]
    exact hrnonneg x
  · filter_upwards [hrLp.coeFn_toLp, hrle] with x hx hrx
    simpa only [hx] using hrx
  · calc
      ν = μ.withDensity (ν.rnDeriv μ) := (ν.withDensity_rnDeriv_eq μ hrac).symm
      _ = μ.withDensity (fun x => ENNReal.ofReal ((hrLp.toLp r) x)) := by
        apply withDensity_congr_ae
        filter_upwards [ν.rnDeriv_ne_top μ, hrLp.coeFn_toLp] with x hfinite hx
        rw [hx]
        exact (ENNReal.ofReal_toReal hfinite).symm
  · rw [Lp.norm_toLp, Lp.norm_def]
    exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
      (eLpNorm_mono_ae hrmeas.aestronglyMeasurable hrnorm)

end Invariant233.SubmeasureDensity

end

end OAI

import OAI.Geometry.RCD.Metric.FiniteDensityMeasure
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

namespace OAI

/-! # The bounded real density of a dominated finite energy limit -/

open Set Filter MeasureTheory
open scoped ENNReal
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MeasurableSpace X]

theorem bounded_finite_density (μ : Measure X) [IsFiniteMeasure μ]
    (ν : FiniteMeasure X) {M : ℝ} (hM : 0≤M)
    (hν : (ν : Measure X)≤ENNReal.ofReal M • μ) :
    ∃ f : X → ℝ, Measurable f ∧ Integrable f μ ∧
      (∀ᵐ x ∂μ, 0≤f x ∧ f x≤M) ∧
      (ν : Measure X)=μ.withDensity (fun x => ENNReal.ofReal (f x)) := by
  let f := fun x => ((ν : Measure X).rnDeriv μ x).toReal
  have hb : (ν : Measure X).rnDeriv μ≤ᵐ[μ] fun _ => ENNReal.ofReal M := by
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite ((ν : Measure X).measurable_rnDeriv μ)
    intro A _ _
    have hh := (Measure.setLIntegral_rnDeriv_le (μ := (ν : Measure X)) (ν := μ) A).trans (hν A)
    simpa only [lintegral_const,Measure.restrict_apply_univ,Measure.smul_apply,smul_eq_mul] using hh
  have hf : Measurable f := ((ν : Measure X).measurable_rnDeriv μ).ennreal_toReal
  have hbf : ∀ᵐ x ∂μ, 0≤f x ∧ f x≤M := by
    filter_upwards [hb] with x hx
    refine ⟨ENNReal.toReal_nonneg,?_⟩
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hx).trans_eq (ENNReal.toReal_ofReal hM)
  have hi : Integrable f μ := Integrable.of_bound hf.aestronglyMeasurable M
    (hbf.mono fun _ hx => by simpa only [Real.norm_eq_abs,abs_of_nonneg hx.1] using hx.2)
  refine ⟨f,hf,hi,hbf,?_⟩
  rw [← Measure.withDensity_rnDeriv_eq (ν : Measure X) μ (Measure.absolutelyContinuous_of_le_smul hν)]
  apply withDensity_congr_ae
  filter_upwards [Measure.rnDeriv_ne_top (ν : Measure X) μ] with x hx
  exact (ENNReal.ofReal_toReal hx).symm

end RegularPointCoordinates

end

end OAI

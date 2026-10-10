import OAI.Analysis.KadisonKastler.ProductIntegralUniqueness
import OAI.Analysis.KadisonKastler.ShiftInvariantSigma
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Unique

namespace OAI

/-! # Invariant sections and rectangle tests

For a function invariant under a shift in its first coordinate, integrating
over a set in the second coordinate gives a function on the invariant sigma
algebra. Consequently invariant rectangles already determine such a function.
-/

namespace KadisonKastler

noncomputable section

open MeasureTheory Set

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
  {S : X → X} {f : X × Y → ℂ}

omit [IsFiniteMeasure μ] in
theorem integrable_section_setIntegral (hf : Integrable f (μ.prod ν))
    (B : Set Y) : Integrable (fun x => ∫ y in B, f (x, y) ∂ν) μ := by
  have h : Integrable f (μ.prod (ν.restrict B)) :=
    hf.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  exact h.integral_prod_left

omit [IsFiniteMeasure μ] in
theorem invariant_section_setIntegral
    (hf : ∀ᵐ z ∂μ.prod ν, f (S z.1, z.2) = f z) (B : Set Y) :
    ∀ᵐ x ∂μ, (∫ y in B, f (S x, y) ∂ν) = ∫ y in B, f (x, y) ∂ν := by
  filter_upwards [Measure.ae_ae_of_ae_prod hf] with x hx
  exact integral_congr_ae (ae_restrict_of_ae hx)

omit [IsFiniteMeasure μ] in
theorem invariant_section_measurable (hfm : StronglyMeasurable f)
    (hf : ∀ᵐ z ∂μ.prod ν, f (S z.1, z.2) = f z) (B : Set Y) :
    Measurable[shiftInvariantSigma μ S] (fun x => ∫ y in B, f (x, y) ∂ν) := by
  apply measurable_shiftInvariantSigma_of_fixed μ S
    ((hfm.integral_prod_right' (ν := ν.restrict B)).measurable)
  exact invariant_section_setIntegral hf B

theorem invariant_integrable_zero_of_rectangle_tests (hfm : StronglyMeasurable f)
    (hfi : Integrable f (μ.prod ν))
    (hfix : ∀ᵐ z ∂μ.prod ν, f (S z.1, z.2) = f z)
    (htest : ∀ A B, MeasurableSet[shiftInvariantSigma μ S] A → MeasurableSet B →
      ∫ z in A ×ˢ B, f z ∂μ.prod ν = 0) : f =ᵐ[μ.prod ν] 0 := by
  have hB (B : Set Y) (hBm : MeasurableSet B) :
      (fun x => ∫ y in B, f (x, y) ∂ν) =ᵐ[μ] 0 := by
    have hi := integrable_section_setIntegral hfi B
    apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite' (shiftInvariantSigma_le μ S)
      (fun _ _ _ => hi.integrableOn) (fun _ _ _ => (integrable_zero _ _ _).integrableOn)
    · intro A hA _
      rw [← setIntegral_prod f hfi.integrableOn, htest A B hA hBm]
      simp
    · exact (invariant_section_measurable hfm hfix B).stronglyMeasurable.aestronglyMeasurable
    · exact aestronglyMeasurable_zero
  apply integrable_eq_zero_of_rectangle_integrals hfi
  intro A B _ hBmeas
  rw [setIntegral_prod f hfi.integrableOn]
  calc
    (∫ x in A, ∫ y in B, f (x, y) ∂ν ∂μ) = ∫ x in A, (0 : ℂ) ∂μ :=
      integral_congr_ae (ae_restrict_of_ae (hB B hBmeas))
    _ = 0 := by simp

end

end KadisonKastler

end OAI

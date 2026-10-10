import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.FactorsThrough

namespace OAI

open MeasureTheory

namespace Invariant233.ConditionalEndpointTransport

variable {Ω X Y E : Type*} [mΩ : MeasurableSpace Ω]
  [mX : MeasurableSpace X] [mY : MeasurableSpace Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem condExp_comap_encode_ae_eq
    (μ : Measure Ω) [IsFiniteMeasure μ] (x : Ω → X) (hx : Measurable x)
    (encode : X → Y) (hencode : Measurable encode)
    (decode : Y → X) (hdecode : Measurable decode)
    (hinverse : ∀ᵐ ω ∂μ, decode (encode (x ω)) = x ω) (f : Ω → E) :
    μ[f | mY.comap (encode ∘ x)] =ᵐ[μ] μ[f | mX.comap x] := by
  have hxy : mY.comap (encode ∘ x) ≤ mX.comap x :=
    (hencode.comp (Measurable.of_comap_le le_rfl)).comap_le
  have hy : Measurable (encode ∘ x) := hencode.comp hx
  obtain ⟨g, hg, hfactor⟩ :=
    (stronglyMeasurable_condExp (μ := μ) (f := f) (m := mX.comap x)).exists_eq_measurable_comp
  have hgm : AEStronglyMeasurable[mY.comap (encode ∘ x)]
      (μ[f | mX.comap x]) μ := by
    have hmeas : StronglyMeasurable[mY.comap (encode ∘ x)]
        (fun ω => g (decode (encode (x ω)))) :=
      hg.comp_measurable (hdecode.comp (Measurable.of_comap_le le_rfl))
    apply hmeas.aestronglyMeasurable.congr
    filter_upwards [hinverse] with ω hω
    rw [hω, hfactor]
    rfl
  exact (condExp_condExp_of_le hxy hx.comap_le).symm.trans
    (condExp_of_aestronglyMeasurable' hy.comap_le hgm integrable_condExp)

end Invariant233.ConditionalEndpointTransport

end OAI

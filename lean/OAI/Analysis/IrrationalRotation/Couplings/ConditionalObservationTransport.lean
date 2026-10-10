import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.Probability.Independence.Conditional

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped MeasureTheory

namespace Invariant233.ConditionalObservationTransport

variable {Ω D Y E : Type*} [mΩ : MeasurableSpace Ω]
  [mD : MeasurableSpace D] [mY : MeasurableSpace Y]
  {μ : Measure Ω} [IsFiniteMeasure μ]

omit [IsFiniteMeasure μ] in

theorem aestronglyMeasurable_encoding
    [NormedAddCommGroup E] [CompleteSpace E]
    {X : Ω → D} {encode : D → Y} {decode : Y → D}
    (hdecode : Measurable decode)
    (hrecover : ∀ᵐ ω ∂μ, decode (encode (X ω)) = X ω)
    {g : Ω → E} (hg : StronglyMeasurable[mD.comap X] g) :
    AEStronglyMeasurable[mY.comap (encode ∘ X)] g μ := by
  obtain ⟨k, hk, hkg⟩ := hg.exists_eq_measurable_comp
  have hobs : Measurable[mY.comap (encode ∘ X)] (encode ∘ X) :=
    measurable_iff_comap_le.mpr le_rfl
  refine ⟨k ∘ decode ∘ (encode ∘ X),
    hk.comp_measurable (hdecode.comp hobs), ?_⟩
  filter_upwards [hrecover] with ω hω
  simp only [hkg, Function.comp_apply, hω]

theorem condExp_encoding
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {X : Ω → D} {encode : D → Y} {decode : Y → D}
    (hX : Measurable X) (hencode : Measurable encode) (hdecode : Measurable decode)
    (hrecover : ∀ᵐ ω ∂μ, decode (encode (X ω)) = X ω) (f : Ω → E) :
    μ[f | mY.comap (encode ∘ X)] =ᵐ[μ] μ[f | mD.comap X] := by
  have hle : mY.comap (encode ∘ X) ≤ mD.comap X := by
    rw [← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono hencode.comap_le
  have hsmall : mY.comap (encode ∘ X) ≤ mΩ := (hencode.comp hX).comap_le
  have hg : AEStronglyMeasurable[mY.comap (encode ∘ X)] (μ[f | mD.comap X]) μ :=
    aestronglyMeasurable_encoding hdecode hrecover stronglyMeasurable_condExp
  exact (condExp_condExp_of_le hle hX.comap_le).symm.trans
    (condExp_of_aestronglyMeasurable' hsmall hg integrable_condExp)

theorem condExp_encoding_formula
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {X : Ω → D} {encode : D → Y} {decode : Y → D}
    (hX : Measurable X) (hencode : Measurable encode) (hdecode : Measurable decode)
    (hrecover : ∀ᵐ ω ∂μ, decode (encode (X ω)) = X ω)
    (f : Ω → E) (posterior : D → E)
    (hposterior : μ[f | mD.comap X] =ᵐ[μ] posterior ∘ X) :
    μ[f | mY.comap (encode ∘ X)] =ᵐ[μ] posterior ∘ decode ∘ (encode ∘ X) := by
  refine (condExp_encoding hX hencode hdecode hrecover f).trans (hposterior.trans ?_)
  filter_upwards [hrecover] with ω hω
  simp only [Function.comp_apply, hω]

theorem iCondIndepFun_encoding_iff
    [StandardBorelSpace Ω] {ι : Type*} {β : ι → Type*}
    [mβ : ∀ i, MeasurableSpace (β i)]
    {X : Ω → D} {encode : D → Y} {decode : Y → D}
    (hX : Measurable X) (hencode : Measurable encode) (hdecode : Measurable decode)
    (hrecover : ∀ᵐ ω ∂μ, decode (encode (X ω)) = X ω)
    (L : ∀ i, Ω → β i) (hL : ∀ i, Measurable (L i)) :
    iCondIndepFun (mY.comap (encode ∘ X)) (hencode.comp hX).comap_le L μ ↔
      iCondIndepFun (mD.comap X) hX.comap_le L μ := by
  classical
  rw [iCondIndepFun_iff_condExp_inter_preimage_eq_mul mβ L hL,
    iCondIndepFun_iff_condExp_inter_preimage_eq_mul mβ L hL]
  have hce (s : Set Ω) :
      μ⟦s | mY.comap (encode ∘ X)⟧ =ᵐ[μ] μ⟦s | mD.comap X⟧ :=
    condExp_encoding hX hencode hdecode hrecover (s.indicator (fun _ => (1 : ℝ)))
  constructor
  · intro h S sets hsets
    have hp : (∏ i ∈ S, μ⟦L i ⁻¹' sets i | mY.comap (encode ∘ X)⟧) =ᵐ[μ]
        ∏ i ∈ S, μ⟦L i ⁻¹' sets i | mD.comap X⟧ :=
      eventuallyEq_prod (fun i _ => hce (L i ⁻¹' sets i))
    exact (hce _).symm.trans ((h S hsets).trans hp)
  · intro h S sets hsets
    have hp : (∏ i ∈ S, μ⟦L i ⁻¹' sets i | mY.comap (encode ∘ X)⟧) =ᵐ[μ]
        ∏ i ∈ S, μ⟦L i ⁻¹' sets i | mD.comap X⟧ :=
      eventuallyEq_prod (fun i _ => hce (L i ⁻¹' sets i))
    exact (hce _).trans ((h S hsets).trans hp.symm)

end Invariant233.ConditionalObservationTransport

end

end OAI

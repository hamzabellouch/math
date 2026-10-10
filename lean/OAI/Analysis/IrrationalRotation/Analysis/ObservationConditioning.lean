import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Independence.Conditional

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Invariant233.ObservationConditioning

variable {Ω A B : Type*} [MeasurableSpace Ω]
    {mA : MeasurableSpace A} {mB : MeasurableSpace B}

theorem condExp_comap_congr_ae (μ : Measure Ω) [IsFiniteMeasure μ]
    {X X' : Ω → A} (hX : Measurable X) (hX' : Measurable X')
    (hXX' : X =ᵐ[μ] X') (f : Ω → ℝ) :
    μ[f | mA.comap X] =ᵐ[μ] μ[f | mA.comap X'] := by
  by_cases hf : Integrable f μ
  · have hkernel : condDistrib f X μ = condDistrib f X' μ :=
      condDistrib_congr_right hXX'
    filter_upwards [condExp_ae_eq_integral_condDistrib' hX hf,
      condExp_ae_eq_integral_condDistrib' hX' hf, hXX'] with ω h₁ h₂ hω
    rw [h₁, h₂, hkernel, hω]
  · simp only [condExp_of_not_integrable hf]
    rfl

theorem comap_eq_of_measurable_leftInverse {r : B → A} {q : A → B}
    (hr : Measurable r) (hq : Measurable q) (hqr : Function.LeftInverse q r) :
    mA.comap r = mB := by
  apply le_antisymm hr.comap_le
  intro s hs
  refine ⟨q ⁻¹' s, hq hs, ?_⟩
  ext b
  change q (r b) ∈ s ↔ b ∈ s
  rw [hqr b]

theorem condExp_comap_of_ae_section (μ : Measure Ω) [IsFiniteMeasure μ]
    {X : Ω → A} {Y : Ω → B} (hX : Measurable X) (hY : Measurable Y)
    {r : B → A} {q : A → B} (hr : Measurable r) (hq : Measurable q)
    (hqr : Function.LeftInverse q r) (hrep : (r ∘ Y) =ᵐ[μ] X)
    (f : Ω → ℝ) :
    μ[f | mA.comap X] =ᵐ[μ] μ[f | mB.comap Y] := by
  have h := condExp_comap_congr_ae μ hX (hr.comp hY) hrep.symm f
  have heq : mA.comap (r ∘ Y) = mB.comap Y := by
    rw [← MeasurableSpace.comap_comp,
      comap_eq_of_measurable_leftInverse hr hq hqr]
  simpa only [heq] using h

theorem iCondIndepSet_comap_iff_of_ae_section {ι : Type*} [Countable ι]
    [StandardBorelSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {X : Ω → A} {Y : Ω → B} (hX : Measurable X) (hY : Measurable Y)
    {r : B → A} {q : A → B} (hr : Measurable r) (hq : Measurable q)
    (hqr : Function.LeftInverse q r) (hrep : (r ∘ Y) =ᵐ[μ] X)
    (events : ι → Set Ω) (hmeas : ∀ i, MeasurableSet (events i)) :
    iCondIndepSet (mA.comap X) hX.comap_le events μ ↔
      iCondIndepSet (mB.comap Y) hY.comap_le events μ := by
  have hsingle : ∀ᵐ ω ∂μ, ∀ i,
      (μ[(events i).indicator (fun _ => (1 : ℝ)) | mA.comap X]) ω =
      (μ[(events i).indicator (fun _ => (1 : ℝ)) | mB.comap Y]) ω :=
    ae_all_iff.mpr (fun i => condExp_comap_of_ae_section μ hX hY hr hq hqr hrep _)
  rw [iCondIndepSet_iff _ _ events hmeas μ,
    iCondIndepSet_iff _ _ events hmeas μ]
  constructor
  · intro h S
    filter_upwards [h S, hsingle,
      condExp_comap_of_ae_section μ hX hY hr hq hqr hrep
        ((⋂ i ∈ S, events i).indicator (fun _ => (1 : ℝ)))] with ω hω hs hi
    rw [← hi, hω]
    simp only [Finset.prod_apply]
    exact Finset.prod_congr rfl (fun i _ => hs i)
  · intro h S
    filter_upwards [h S, hsingle,
      condExp_comap_of_ae_section μ hX hY hr hq hqr hrep
        ((⋂ i ∈ S, events i).indicator (fun _ => (1 : ℝ)))] with ω hω hs hi
    rw [hi, hω]
    simp only [Finset.prod_apply]
    exact Finset.prod_congr rfl (fun i _ => (hs i).symm)

omit [MeasurableSpace Ω] in

theorem iCondIndepSet_iff_of_events_ae_eq {ι : Type*} [Countable ι]
    (m : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    (hm : m ≤ mΩ) (μ : Measure Ω) [IsFiniteMeasure μ]
    (events events' : ι → Set Ω)
    (hmeas : ∀ i, MeasurableSet (events i))
    (hmeas' : ∀ i, MeasurableSet (events' i))
    (heq : ∀ i, events i =ᵐ[μ] events' i) :
    iCondIndepSet m hm events μ ↔ iCondIndepSet m hm events' μ := by
  have hsingle : ∀ᵐ ω ∂μ, ∀ i,
      (μ[(events i).indicator (fun _ => (1 : ℝ)) | m]) ω =
      (μ[(events' i).indicator (fun _ => (1 : ℝ)) | m]) ω :=
    ae_all_iff.mpr (fun i => condExp_congr_ae (indicator_ae_eq_of_ae_eq_set (heq i)))
  have hinter (S : Finset ι) : (⋂ i ∈ S, events i) =ᵐ[μ] (⋂ i ∈ S, events' i) := by
    filter_upwards [ae_all_iff.mpr heq] with ω hω
    change (ω ∈ ⋂ i ∈ S, events i) = (ω ∈ ⋂ i ∈ S, events' i)
    apply propext
    simp only [Set.mem_iInter]
    constructor <;> intro h i hi
    · exact (hω i).mp (h i hi)
    · exact (hω i).mpr (h i hi)
  rw [iCondIndepSet_iff _ _ events hmeas μ,
    iCondIndepSet_iff _ _ events' hmeas' μ]
  constructor
  · intro h S
    filter_upwards [h S, hsingle,
      condExp_congr_ae (m := m)
        (indicator_ae_eq_of_ae_eq_set (f := fun _ => (1 : ℝ)) (hinter S))]
      with ω hω hs hi
    rw [← hi, hω]
    simp only [Finset.prod_apply]
    exact Finset.prod_congr rfl (fun i _ => hs i)
  · intro h S
    filter_upwards [h S, hsingle,
      condExp_congr_ae (m := m)
        (indicator_ae_eq_of_ae_eq_set (f := fun _ => (1 : ℝ)) (hinter S))]
      with ω hω hs hi
    rw [hi, hω]
    simp only [Finset.prod_apply]
    exact Finset.prod_congr rfl (fun i _ => (hs i).symm)

end Invariant233.ObservationConditioning

end OAI

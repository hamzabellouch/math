import OAI.Analysis.CircleDomains.Modulus.LevelIncidence
import OAI.Analysis.CircleDomains.Rigidity.ComponentTrace
import Mathlib.MeasureTheory.Constructions.Pi

namespace OAI

/-!
# Completed-measure compatibility for finite level tuples

Lusin's universal-measurability theorem applies to the finite-dimensional
tori used for level choices:
A. S. Kechris, *Classical Descriptive Set Theory*, GTM 156 (1995),
Theorem 21.10, p. 155. Every analytic subset of a standard Borel space is
measurable for the completion of each sigma-finite Borel measure.
Publisher: https://doi.org/10.1007/978-1-4612-4190-4

The compatibility statement uses analyticity of compact incidence sets
and nullity of the free trace image on each nondegenerate component.
-/

open Set MeasureTheory

namespace CircleDomainRigidity

/-- The specialization of Kechris, Theorem 21.10, actually needed for
finite tuples of circle-valued levels. -/
def FiniteTorusAnalyticMeasurability : Prop :=
  ∀ (d : ℕ) (E : Set (UnitAddCircle × (Fin d → UnitAddCircle))),
    AnalyticSet E →
      NullMeasurableSet E (volume.prod (Measure.pi (fun _ : Fin d => volume)))

/-- The ambient version of the nondegenerate-component locus agrees
with the image of the corresponding locus in the level subtype. -/
theorem nontrivialComponentInLocus_eq_image
    {X : Type*} [TopologicalSpace X] (A : Set X) :
    {x | (connectedComponentIn A x).Nontrivial} =
      Subtype.val '' nontrivialComponentLocus A := by
  ext x
  constructor
  · intro hx
    change (connectedComponentIn A x).Nontrivial at hx
    have hxA : x ∈ A := by
      by_contra hn
      exact Set.not_nontrivial_empty (connectedComponentIn_eq_empty hn ▸ hx)
    rw [connectedComponentIn_eq_image hxA] at hx
    exact ⟨⟨x, hxA⟩, nontrivial_of_image _ _ hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    change (connectedComponentIn A x.val).Nontrivial
    rw [connectedComponentIn_eq_image x.property]
    exact hx.image Subtype.val_injective

/-- Null component traces give a null trace image on the ambient
nondegenerate-component locus of a compact level union. -/
theorem volume_trace_nontrivialComponentInLocus_eq_zero
    {X : Type*} [MetricSpace X] (A : Set X) [CompactSpace A]
    (hbound : HasFiniteLargeContinuumBound A) (F : Set X)
    (w : X → UnitAddCircle)
    (hnull : ∀ C : Set A, (∃ x, C = connectedComponent x) → C.Nontrivial →
      volume ((fun x : A => w x) '' ((Subtype.val ⁻¹' F) ∩ C)) = 0) :
    volume (w '' (F ∩ {x | (connectedComponentIn A x).Nontrivial})) = 0 := by
  have hn := volume_trace_nontrivialComponentLocus_eq_zero hbound
    (Subtype.val ⁻¹' F) (fun x : A => w x) hnull
  have heq : w '' (F ∩ {x | (connectedComponentIn A x).Nontrivial}) =
      (fun x : A => w x) '' ((Subtype.val ⁻¹' F) ∩ nontrivialComponentLocus A) := by
    rw [nontrivialComponentInLocus_eq_image]
    ext t
    constructor
    · rintro ⟨x, ⟨hxF, y, hy, rfl⟩, ht⟩
      exact ⟨y, ⟨hxF, hy⟩, ht⟩
    · rintro ⟨x, ⟨hxF, hxC⟩, ht⟩
      exact ⟨x, ⟨hxF, x, hxC, rfl⟩, ht⟩
  rwa [heq]

/-- Fubini's null-section implication with the other order of factors.
The event need only be measurable in the completed product measure. -/
theorem product_null_of_nullMeasurable_swapped_sections
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} [SFinite μ] [SFinite ν]
    {E : Set (A × B)} (hE : NullMeasurableSet E (μ.prod ν))
    (hsections : ∀ᵐ y ∂ν, μ ((fun x => (x, y)) ⁻¹' E) = 0) :
    (μ.prod ν) E = 0 := by
  have hswap := (Measure.measurePreserving_swap (μ := ν) (ν := μ))
  have hpre : NullMeasurableSet (Prod.swap ⁻¹' E) (ν.prod μ) :=
    hE.preimage hswap.quasiMeasurePreserving
  have hzero : (ν.prod μ) (Prod.swap ⁻¹' E) = 0 :=
    product_null_of_nullMeasurable_sections hpre hsections
  rw [hswap.measure_preimage hE] at hzero
  exact hzero

/-- An analytic compatibility failure is measurable for the completed
product law, using analytic measurability on finite tori. -/
theorem nullMeasurableSet_freeComponentFailure
    {X Λ : Type*} [MetricSpace X] [CompactSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (hLusin : FiniteTorusAnalyticMeasurability) (d : ℕ)
    {F : Set X} (hF : MeasurableSet F)
    {Rnew : Set (X × UnitAddCircle)} (hnew : IsClosed Rnew)
    {R : Λ → Set (X × UnitAddCircle)} (hR : ∀ l, IsClosed (R l))
    (labels : Fin d → Λ) :
    NullMeasurableSet (freeComponentFailure F Rnew R labels)
      (volume.prod (Measure.pi (fun _ : Fin d => volume))) :=
  hLusin d _ (analyticSet_freeComponentFailure hF hnew hR labels)

/-- For one fixed prior tuple, null component traces exclude all new
levels except a Haar-null set. No measurability of the trace is needed. -/
theorem measure_new_level_failure_eq_zero
    {X Λ : Type*} [MetricSpace X] [CompactSpace X]
    (F : Set X) (Rnew : Set (X × UnitAddCircle))
    (R : Λ → Set (X × UnitAddCircle)) (d : ℕ) (labels : Fin d → Λ)
    (θ : Fin d → UnitAddCircle) (w : X → UnitAddCircle)
    (hlevel : ∀ x ∈ F, ∀ t, (x, t) ∈ Rnew ↔ w x = t)
    (hA : IsClosed {x | (x, θ) ∈ finiteLevelUnionGraph R labels})
    (hbound : HasFiniteLargeContinuumBound
      {x | (x, θ) ∈ finiteLevelUnionGraph R labels})
    (hnull : ∀ C : Set {x | (x, θ) ∈ finiteLevelUnionGraph R labels},
      (∃ x, C = connectedComponent x) → C.Nontrivial →
      volume ((fun x : {x | (x, θ) ∈ finiteLevelUnionGraph R labels} => w x) ''
        ((Subtype.val ⁻¹' F) ∩ C)) = 0) :
    volume ((fun t => (t, θ)) ⁻¹' freeComponentFailure F Rnew R labels) = 0 := by
  let A := {x | (x, θ) ∈ finiteLevelUnionGraph R labels}
  let : CompactSpace A := isCompact_iff_compactSpace.mp hA.isCompact
  have htrace := volume_trace_nontrivialComponentInLocus_eq_zero A hbound F w hnull
  apply measure_mono_null (t := w '' (F ∩ {x | (connectedComponentIn A x).Nontrivial})) _ htrace
  intro t ht
  obtain ⟨⟨x, t', θ'⟩, hx, heq⟩ := ht
  cases heq
  exact ⟨x, ⟨hx.1, hx.2.2⟩, (hlevel x hx.1 t).mp hx.2.1⟩

/-- The finite-tuple compatibility conclusion, conditional on the
analytic measurability on finite tori and the null-trace
hypotheses. Repeated prior labels are allowed. -/
theorem measure_freeComponentFailure_eq_zero
    {X Λ : Type*} [MetricSpace X] [CompactSpace X] [PolishSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (hLusin : FiniteTorusAnalyticMeasurability) (d : ℕ)
    {F : Set X} (hF : MeasurableSet F)
    {Rnew : Set (X × UnitAddCircle)} (hnew : IsClosed Rnew)
    {R : Λ → Set (X × UnitAddCircle)} (hR : ∀ l, IsClosed (R l))
    (labels : Fin d → Λ) (w : X → UnitAddCircle)
    (hlevel : ∀ x ∈ F, ∀ t, (x, t) ∈ Rnew ↔ w x = t)
    (hgood : ∀ᵐ θ ∂Measure.pi (fun _ : Fin d => (volume : Measure UnitAddCircle)),
      HasFiniteLargeContinuumBound {x | (x, θ) ∈ finiteLevelUnionGraph R labels} ∧
      ∀ C : Set {x | (x, θ) ∈ finiteLevelUnionGraph R labels},
        (∃ x, C = connectedComponent x) → C.Nontrivial →
        volume ((fun x : {x | (x, θ) ∈ finiteLevelUnionGraph R labels} => w x) ''
          ((Subtype.val ⁻¹' F) ∩ C)) = 0) :
    (volume.prod (Measure.pi (fun _ : Fin d => volume)))
      (freeComponentFailure F Rnew R labels) = 0 := by
  apply product_null_of_nullMeasurable_swapped_sections
    (nullMeasurableSet_freeComponentFailure hLusin d hF hnew hR labels)
  filter_upwards [hgood] with θ hθ
  have hA : IsClosed {x | (x, θ) ∈ finiteLevelUnionGraph R labels} :=
    (isClosed_finiteLevelUnionGraph hR labels).preimage
      (continuous_id.prodMk continuous_const)
  exact measure_new_level_failure_eq_zero F Rnew R d labels θ w hlevel hA hθ.1 hθ.2

end CircleDomainRigidity

end OAI

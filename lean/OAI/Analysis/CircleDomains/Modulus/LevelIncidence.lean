import OAI.Analysis.CircleDomains.Modulus.HyperspaceIncidence
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.Prod

namespace OAI

/-!
# Finite level unions and analytic compatibility failures

Repeated labels are allowed in a finite tuple of levels. Closed level
graphs give a closed union graph; its nondegenerate-component relation
is Borel by the compact hyperspace argument. After restriction to a
Borel set of free points, projection over the point is analytic.
-/

open Set MeasureTheory

namespace CircleDomainRigidity

def finiteLevelUnionGraph {X T J Λ : Type*} (R : Λ → Set (X × T))
    (labels : J → Λ) : Set (X × (J → T)) :=
  ⋃ j, (fun p : X × (J → T) => (p.1, p.2 j)) ⁻¹' R (labels j)

theorem isClosed_finiteLevelUnionGraph
    {X T J Λ : Type*} [TopologicalSpace X] [TopologicalSpace T] [Fintype J]
    {R : Λ → Set (X × T)} (hR : ∀ l, IsClosed (R l)) (labels : J → Λ) :
    IsClosed (finiteLevelUnionGraph R labels) := by
  apply isClosed_iUnion_of_finite
  intro j
  exact (hR (labels j)).preimage
    (continuous_fst.prodMk ((continuous_apply j).comp continuous_snd))

theorem measurableSet_finiteLevel_nontrivial_components
    {X T J Λ : Type*} [MetricSpace X] [CompactSpace X] [TopologicalSpace T]
    [Fintype J] [MeasurableSpace X] [MeasurableSpace T]
    [BorelSpace X] [BorelSpace T] [SecondCountableTopology T]
    {R : Λ → Set (X × T)} (hR : ∀ l, IsClosed (R l)) (labels : J → Λ) :
    MeasurableSet (nontrivialFiberComponentRelation (finiteLevelUnionGraph R labels)) :=
  measurableSet_nontrivialFiberComponentRelation (isClosed_finiteLevelUnionGraph hR labels)

def freeComponentFailure {X T J Λ : Type*} [TopologicalSpace X]
    (F : Set X) (Rnew : Set (X × T)) (R : Λ → Set (X × T)) (labels : J → Λ) :
    Set (T × (J → T)) :=
  Prod.snd '' {p : X × (T × (J → T)) |
    p.1 ∈ F ∧ (p.1, p.2.1) ∈ Rnew ∧
      (p.1, p.2.2) ∈ nontrivialFiberComponentRelation (finiteLevelUnionGraph R labels)}

/-- The failure event in (P) is an analytic subset of its finite level
parameter space. Its universal measurability is the separate classical
descriptive-set-theoretic input when completed measures are used. -/
theorem analyticSet_freeComponentFailure
    {X T J Λ : Type*} [MetricSpace X] [CompactSpace X] [PolishSpace X]
    [TopologicalSpace T] [PolishSpace T] [Fintype J]
    [MeasurableSpace X] [MeasurableSpace T] [BorelSpace X] [BorelSpace T]
    {F : Set X} (hF : MeasurableSet F) {Rnew : Set (X × T)} (hnew : IsClosed Rnew)
    {R : Λ → Set (X × T)} (hR : ∀ l, IsClosed (R l)) (labels : J → Λ) :
    AnalyticSet (freeComponentFailure F Rnew R labels) := by
  have hcomponents := measurableSet_finiteLevel_nontrivial_components hR labels
  have hbad : MeasurableSet {p : X × (T × (J → T)) |
      p.1 ∈ F ∧ (p.1, p.2.1) ∈ Rnew ∧
        (p.1, p.2.2) ∈ nontrivialFiberComponentRelation (finiteLevelUnionGraph R labels)} :=
    (hF.preimage measurable_fst).inter
      ((hnew.measurableSet.preimage (continuous_fst.prodMk continuous_snd.fst).measurable).inter
        (hcomponents.preimage (continuous_fst.prodMk continuous_snd.snd).measurable))
  exact hbad.analyticSet.image_of_continuous continuous_snd

/-- Fubini's null-section implication for a completed-measurable event.
This version does not require the event itself to be Borel. -/
theorem product_null_of_nullMeasurable_sections
    {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} [SFinite μ] [SFinite ν]
    {E : Set (A × B)} (hE : NullMeasurableSet E (μ.prod ν))
    (hsections : ∀ᵐ x ∂μ, ν (Prod.mk x ⁻¹' E) = 0) :
    (μ.prod ν) E = 0 := by
  rw [Measure.prod_apply₀ hE, lintegral_congr_ae hsections]
  exact lintegral_zero

end CircleDomainRigidity

end OAI

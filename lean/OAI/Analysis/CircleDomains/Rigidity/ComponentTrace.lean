import OAI.Analysis.CircleDomains.Selection.FinitelySuslinian
import OAI.Analysis.CircleDomains.Probability.CircleNullImage
import Mathlib.MeasureTheory.Measure.Prod

namespace OAI

/-!
# Null traces on the nondegenerate components of a level union

Generic level unions have only countably many nondegenerate components.
Consequently a trace that is null on each such component is null on their
union. At free points the new coordinate has one trace value, so the
levels meeting this union form a Haar-null set. This is the fixed-prior-
tuple step in the manuscript's compatibility argument.
-/

open Set MeasureTheory

namespace CircleDomainRigidity

def nontrivialComponentLocus (X : Type*) [TopologicalSpace X] : Set X :=
  {x | (connectedComponent x).Nontrivial}

theorem volume_trace_nontrivialComponentLocus_eq_zero
    {X : Type*} [MetricSpace X] [CompactSpace X]
    (hbound : HasFiniteLargeContinuumBound X) (F : Set X)
    (w : X → AddCircle (1 : ℝ))
    (hnull : ∀ C : Set X, (∃ x, C = connectedComponent x) → C.Nontrivial →
      volume (w '' (F ∩ C)) = 0) :
    volume (w '' (F ∩ nontrivialComponentLocus X)) = 0 := by
  let S : Set (Set X) := {C | (∃ x, C = connectedComponent x) ∧ C.Nontrivial}
  have hS : S.Countable := countable_nontrivial_connectedComponents hbound
  have hcover : w '' (F ∩ nontrivialComponentLocus X) ⊆
      ⋃ C ∈ S, w '' (F ∩ C) := by
    rintro t ⟨x, hx, rfl⟩
    exact mem_iUnion.mpr ⟨connectedComponent x,
      mem_iUnion.mpr ⟨⟨⟨x, rfl⟩, hx.2⟩, x, ⟨hx.1, mem_connectedComponent⟩, rfl⟩⟩
  apply measure_mono_null hcover
  exact (measure_biUnion_null_iff hS).mpr (fun C hC => hnull C hC.1 hC.2)

/-- At free points, membership in the new level is membership of the
unique trace value. Null component traces therefore exclude almost every
new level from every nondegenerate old component. -/
theorem ae_new_level_avoids_nontrivial_components
    {X : Type*} [MetricSpace X] [CompactSpace X]
    (hbound : HasFiniteLargeContinuumBound X) (F : Set X)
    (w : X → AddCircle (1 : ℝ)) (H : AddCircle (1 : ℝ) → Set X)
    (hlevel : ∀ x ∈ F, ∀ t, x ∈ H t ↔ w x = t)
    (hnull : ∀ C : Set X, (∃ x, C = connectedComponent x) → C.Nontrivial →
      volume (w '' (F ∩ C)) = 0) :
    ∀ᵐ t ∂volume, ∀ x ∈ F ∩ H t, x ∉ nontrivialComponentLocus X := by
  have hn := volume_trace_nontrivialComponentLocus_eq_zero hbound F w hnull
  have hae : ∀ᵐ t ∂volume, t ∉ w '' (F ∩ nontrivialComponentLocus X) :=
    (ae_iff.mpr (by simpa only [not_not, ofPred_mem_eq] using hn))
  filter_upwards [hae] with t ht
  intro x hx hnontrivial
  exact ht ⟨x, ⟨hx.1, hnontrivial⟩, (hlevel x hx.1 t).mp hx.2⟩

/-- Passing from almost every prior tuple and almost every new level to
the product assertion requires measurability of the incidence relation.
The manuscript obtains this from compact hyperspace projection. -/
theorem ae_product_compatibility_of_ae_sections
    {T : Type*} [MeasurableSpace T] (ν : Measure T) [SFinite ν]
    (P : AddCircle (1 : ℝ) → T → Prop)
    (hP : MeasurableSet {z : AddCircle (1 : ℝ) × T | P z.1 z.2})
    (hsections : ∀ᵐ s ∂ν, ∀ᵐ t ∂volume, P t s) :
    ∀ᵐ z ∂(volume.prod ν), P z.1 z.2 := by
  apply (Measure.ae_prod_iff_ae_ae hP).mpr
  exact (Measure.ae_ae_comm hP).mpr hsections

end CircleDomainRigidity

end OAI

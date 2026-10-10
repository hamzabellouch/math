import OAI.Geometry.SurfaceImmersion.Geometry.ScalarFlatCriticalValues
import Mathlib.Topology.Compactness.Lindelof

namespace OAI

/-! Local null-image statements glue over a second countable domain. -/
noncomputable section
open Set MeasureTheory
open scoped Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing

theorem null_image_of_locally_null {X Y : Type*} [TopologicalSpace X]
    [SecondCountableTopology X] [MeasurableSpace Y] (μ : Measure Y)
    (f : X → Y) (s : Set X)
    (h : ∀ x ∈ s, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ μ (f '' (s ∩ U)) = 0) :
    μ (f '' s) = 0 := by
  choose U ho hm hn using fun x : s => h x x.property
  have hcover : s ⊆ ⋃ x : s, U x := fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩,hm ⟨x,hx⟩⟩
  obtain ⟨A,hAc,hA⟩ := (HereditarilyLindelofSpace.isLindelof s).elim_countable_subcover U ho hcover
  have hsub : f '' s ⊆ ⋃ x ∈ A, f '' (s ∩ U x) := by
    rintro y ⟨x,hx,rfl⟩
    obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp (hA hx)
    exact mem_iUnion₂.mpr ⟨i,hi,⟨x,⟨hx,hxi⟩,rfl⟩⟩
  exact measure_mono_null hsub ((measure_biUnion_null_iff hAc).mpr fun x _ => hn x)

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI

import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Maps.Basic

namespace OAI

/-! # Compact lifts under an open quotient

A compact target set has lifts in one compact source set for an open
surjection from a locally compact space. This is the precise bounded-step
lifting consequence needed by the Cartan multiplication map.
-/

noncomputable section

namespace PolycyclicRecognition

open Set Topology

/-- Compact lifts need no global section, properness, or injectivity of the
quotient map. Finite local compact neighborhoods suffice. -/
theorem exists_compact_lifts_of_open_surjection
    {X Y : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [TopologicalSpace Y]
    (f : X → Y) (hopen : IsOpenMap f) (hsurj : Function.Surjective f)
    {K : Set Y} (hK : IsCompact K) :
    ∃ C : Set X, IsCompact C ∧ K ⊆ f '' C := by
  choose C hC hn using (fun x : X => exists_compact_mem_nhds x)
  have hxi (x : X) : x ∈ interior (C x) := mem_interior_iff_mem_nhds.mpr (hn x)
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x => f '' interior (C x))
    (fun _ => hopen _ isOpen_interior) (by
      intro y _
      obtain ⟨x, rfl⟩ := hsurj y
      exact mem_iUnion.mpr ⟨x, ⟨x, hxi x, rfl⟩⟩)
  refine ⟨⋃ x ∈ t, C x, t.isCompact_biUnion (fun x _ => hC x), ?_⟩
  intro y hy
  obtain ⟨x, hx, z, hz, hzy⟩ := mem_iUnion₂.mp (ht hy)
  exact ⟨z, mem_iUnion₂.mpr ⟨x, hx, interior_subset hz⟩, hzy⟩

end PolycyclicRecognition

end

end OAI

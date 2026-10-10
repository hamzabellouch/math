import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Separation.Hausdorff

namespace OAI

/-! # Continuity of a descended map from compact lifts

The Cartan multiplication map already has compact lifts of compact sets.
This gives the quotient-continuity statement needed for a representation
defined by its two factors.
-/

namespace PolycyclicRecognition

open Set Filter Topology

theorem continuous_of_compact_lifts
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    [T2Space Y] [LocallyCompactSpace Y]
    (p : X → Y) (F : X → Z) (f : Y → Z) (hp : Continuous p) (hF : Continuous F)
    (hcomp : ∀ x, f (p x) = F x)
    (hlift : ∀ K : Set Y, IsCompact K → ∃ C : Set X, IsCompact C ∧ K ⊆ p '' C) :
    Continuous f := by
  rw [continuous_def]
  intro U hU
  apply isOpen_iff_mem_nhds.mpr
  intro y hy
  obtain ⟨K, hK, hKy⟩ := exists_compact_mem_nhds y
  obtain ⟨C, hC, hKC⟩ := hlift K hK
  let B := C ∩ F ⁻¹' Uᶜ
  have hB : IsCompact B := hC.inter_right (hU.isClosed_compl.preimage hF)
  have hclosed : IsClosed (p '' B) := (hB.image hp).isClosed
  have hyB : y ∉ p '' B := by
    rintro ⟨x, hx, rfl⟩
    exact hx.2 (hcomp x ▸ hy)
  have hneigh : (p '' B)ᶜ ∈ 𝓝 y := hclosed.isOpen_compl.mem_nhds hyB
  apply Filter.mem_of_superset (inter_mem hKy hneigh)
  rintro z ⟨hzK, hzB⟩
  obtain ⟨x, hxC, rfl⟩ := hKC hzK
  by_contra hz
  apply hzB
  refine ⟨x, ⟨hxC, ?_⟩, rfl⟩
  change F x ∉ U
  change f (p x) ∉ U at hz
  rwa [hcomp x] at hz

end PolycyclicRecognition

end OAI

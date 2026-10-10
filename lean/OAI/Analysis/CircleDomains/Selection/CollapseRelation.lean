import OAI.Analysis.CircleDomains.Topology.ComponentTopology
import Mathlib.Topology.Separation.Regular

namespace OAI

/-!
# Closedness of the component-collapse relation

The connected-component space of a closed set in a compact Hausdorff space
is compact Hausdorff. Collapsing its components gives a closed relation,
as required by Moore's sphere decomposition theorem.
-/

open Set Topology

namespace CircleDomainRigidity

/-- Collapsing the connected components of a closed set in a compact Hausdorff
space, and leaving the remaining points fixed, gives a closed relation. -/
theorem isClosed_componentCollapseRelation
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {F : Set X} (hF : IsClosed F) :
    IsClosed {p : X × X | p.1 = p.2 ∨
      (p.1 ∈ F ∧ p.2 ∈ connectedComponentIn F p.1)} := by
  let : CompactSpace F := isCompact_iff_compactSpace.mp hF.isCompact
  let K : Set (F × F) := {p |
    ConnectedComponents.mk p.2 = ConnectedComponents.mk p.1}
  have hK : IsClosed K :=
    isClosed_eq (ConnectedComponents.continuous_coe.comp continuous_snd)
      (ConnectedComponents.continuous_coe.comp continuous_fst)
  let valPair : F × F → X × X := fun p => (p.1.val, p.2.val)
  have hval : Continuous valPair :=
    (continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)
  have himage : IsClosed (valPair '' K) := (hK.isCompact.image hval).isClosed
  have hdiag : IsClosed {p : X × X | p.1 = p.2} :=
    isClosed_eq continuous_fst continuous_snd
  convert hdiag.union himage using 1
  ext p
  constructor
  · rintro (heq | ⟨hx, hy⟩)
    · exact Or.inl heq
    · right
      rw [connectedComponentIn_eq_image hx] at hy
      obtain ⟨y, hy, hvaly⟩ := hy
      refine ⟨(⟨p.1, hx⟩, y), ?_, ?_⟩
      · exact ConnectedComponents.coe_eq_coe'.mpr hy
      · exact Prod.ext rfl hvaly
  · rintro (heq | ⟨⟨x, y⟩, hxy, hpair⟩)
    · exact Or.inl heq
    · have hx : x.val = p.1 := congrArg Prod.fst hpair
      have hy : y.val = p.2 := congrArg Prod.snd hpair
      right
      refine ⟨hx ▸ x.property, ?_⟩
      have hmem : y ∈ connectedComponent x := ConnectedComponents.coe_eq_coe'.mp hxy
      have hin : y.val ∈ connectedComponentIn F x.val := by
        rw [connectedComponentIn_eq_image x.property]
        exact ⟨y, hmem, rfl⟩
      simpa only [hx, hy] using hin

end CircleDomainRigidity

end OAI

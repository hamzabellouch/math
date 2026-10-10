import OAI.Geometry.Relativity.CKS.CutSurface
import OAI.Geometry.Relativity.CKS.EmbeddingOpenInterior

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped ContDiff Topology
namespace CKSSchwarzschild
open CKSBoundarySurface

theorem full_cut_radial_projection_surjective (D : CKSGeometricCuts.OuterDomain Exterior) :
    Function.Surjective (fun z : CKSFullCutArea.Surface D => (CKSFullCutArea.cutInclusion D z).2) := by
  intro n
  by_contra hnone
  have hnone' : ∀ x ∈ I3.boundary D.Carrier, (D.inclusion x).2 ≠ n := by
    intro x hx he
    exact hnone ⟨⟨x,hx⟩,he⟩
  have hinner : ∀ t : Radial, (t,n) ∈ range D.inclusion ↔
      (t,n) ∈ D.inclusion '' I3.interior D.Carrier := by
    intro t
    constructor
    · rintro ⟨x,hx⟩
      refine ⟨x,?_,hx⟩
      by_contra hxi
      have hxb : x ∈ I3.boundary D.Carrier :=
        (I3.isBoundaryPoint_iff_not_isInteriorPoint x).mpr hxi
      exact hnone' x hxb (congrArg Prod.snd hx)
    · rintro ⟨x,_,hx⟩
      exact ⟨x,hx⟩
  let s : Set Radial := (fun t => (t,n)) ⁻¹' range D.inclusion
  have hseq : s = (fun t : Radial => (t,n)) ⁻¹' (D.inclusion '' I3.interior D.Carrier) := by
    ext t; exact hinner t
  have hsc : IsClosed s := D.closed.preimage (continuous_id.prodMk continuous_const)
  have hso : IsOpen s := by
    rw [hseq]
    exact (CKSEmbeddingDerivative.image_interior_isOpen D.embedding).preimage
      (continuous_id.prodMk continuous_const)
  have hsne : s.Nonempty := by
    obtain ⟨K,hK,hfar⟩ := D.contains_distant_end
    have hc : Continuous (fun p : Exterior => p.1.val) := continuous_subtype_val.comp continuous_fst
    obtain ⟨B,hB⟩ := (hK.image hc).bddAbove
    let t : Radial := ⟨max 0 B + 1,by positivity⟩
    refine ⟨t,hfar ?_⟩
    intro hmem
    have hb := hB (mem_image_of_mem (fun p : Exterior => p.1.val) hmem)
    have hm := le_max_right (0 : ℝ) B
    change max 0 B + 1 ≤ B at hb
    linarith
  let : ConnectedSpace Radial := isConnected_iff_connectedSpace.mp isConnected_Ici
  have hsall : s = univ := (IsClopen.eq_univ ⟨hsc,hso⟩ hsne)
  have hz : ((⟨0,le_rfl⟩ : Radial),n) ∈ D.inclusion '' I3.interior D.Carrier :=
    (hinner _).mp (by change (⟨0,le_rfl⟩ : Radial) ∈ s; rw [hsall]; trivial)
  have hout := D.interior_into hz
  have hpos := (interior_iff ((⟨0,le_rfl⟩ : Radial),n)).mp hout
  exact (lt_irrefl (0 : ℝ)) hpos

end CKSSchwarzschild

end

end OAI

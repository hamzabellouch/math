import Mathlib
import OAI.Geometry.Cannon.PlaneTopology.RegionEdges
import OAI.Geometry.Cannon.PlaneTopology.VertexLines

namespace OAI

section
section
section
noncomputable section
open Set unitInterval Topology

noncomputable section
noncomputable section
noncomputable section
open Set Topology unitInterval

noncomputable section
open Set Metric Topology unitInterval

noncomputable section
open Set Metric Topology

noncomputable section
noncomputable section
open Set unitInterval

noncomputable section
noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Metric Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology

noncomputable section
open Set Topology unitInterval

noncomputable section
noncomputable section
noncomputable section
noncomputable section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Topology unitInterval CannonFaceIncidence CannonPolygonal

variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem retained_faces_surplus (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j => Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃q∈Q,segment ℝ q.1 q.2)
    (S : Finset ι) (hS : S.Nonempty) (hproper : S≠Finset.univ) :
    Nat.card {d : Faces F | regionEdges F ConnectedComponents.mk d⊆(S:Set ι)}+1≤
      Nat.card (Faces (fun i : S=> F i.val)) := by
  classical
  let K := ⋃ i,range (F i)
  let H : S → Arc ℂ := fun i=>F i.val
  let L := ⋃ i,range (H i)
  have hLK : L⊆K := by
    intro z hz
    obtain ⟨i,hi⟩ := mem_iUnion.mp hz
    exact mem_iUnion.mpr ⟨i.val,hi⟩
  have hLproper : (K\L).Nonempty := by
    have hn : ∃ i,i∉S := by
      by_contra hh
      push Not at hh
      exact hproper (Finset.eq_univ_of_forall hh)
    obtain ⟨i,hi⟩ := hn
    let t : I := ⟨1/2,by constructor <;> norm_num⟩
    have ht : t≠0 ∧ t≠1 := by constructor <;> intro h <;> have he := congrArg Subtype.val h <;> norm_num [t] at he
    refine ⟨F i t,mem_iUnion.mpr ⟨i,mem_range_self t⟩,?_⟩
    intro hh
    obtain ⟨j,s,hs⟩ := mem_iUnion.mp hh
    have hij : i≠j.val := fun he=>hi (he ▸ j.property)
    exact ((hF hij).1 t s hs.symm).1.elim ht.1 ht.2
  let _ : Nonempty S := hS.to_subtype
  let _ : Finite (Faces H) := faces_finite H
    (fun i j hij=>hF (fun he=>hij (Subtype.ext he))) Q (fun i=>hQ i.val)
  let B := {d : Faces F | regionEdges F ConnectedComponents.mk d⊆(S:Set ι)}
  let _ : Finite (Faces F) := faces_finite F hF Q hQ
  have hcl (d : B) : IsClopen ((Subtype.val : (Lᶜ : Set ℂ) → ℂ) ⁻¹' face F d.val) := by
    constructor
    · have he : (Subtype.val : (Lᶜ : Set ℂ) → ℂ) ⁻¹' face F d.val=
          (Subtype.val : (Lᶜ : Set ℂ) → ℂ) ⁻¹' closure (face F d.val) := by
        ext z
        constructor
        · intro hz
          exact subset_closure hz
        · intro hz
          have _ : LocallyConnectedSpace (Kᶜ : Set ℂ) :=
            (isClosed_iUnion_of_finite fun i=>(F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
          have hh := tame_region_closure F hF Q hQ ConnectedComponents.continuous_coe d.val
          change z.val∈closure (region Kᶜ ConnectedComponents.mk d.val) at hz
          rw [hh] at hz
          rcases hz with hz|hz
          · exact hz
          · obtain ⟨i,hi,hzi⟩ := mem_iUnion₂.mp hz
            exact False.elim (z.property (mem_iUnion.mpr ⟨⟨i,d.property hi⟩,hzi⟩))
      rw [he]
      exact isClosed_closure.preimage continuous_subtype_val
    · exact (face_open F d.val).preimage continuous_subtype_val
  choose a ha using fun d : B=>face_nonempty F d.val
  let p (d : B) : (Lᶜ : Set ℂ) := ⟨a d,fun hL=>(ha d).1 (hLK hL)⟩
  obtain ⟨x,hxK,hxL⟩ := hLproper
  let f : Option B → Faces H := fun o=> match o with
    | none => ConnectedComponents.mk ⟨x,hxL⟩
    | some d => ConnectedComponents.mk (p d)
  have hkey (d : B) (y : (Lᶜ : Set ℂ)) (he : ConnectedComponents.mk y=ConnectedComponents.mk (p d)) : y.val∈face F d.val := by
    exact (hcl d).connectedComponent_subset (ha d) (ConnectedComponents.coe_eq_coe'.mp he)
  have hinj : Function.Injective f := by
    intro u v he
    rcases u with _|d <;> rcases v with _|e
    · rfl
    · have hh := hkey e ⟨x,hxL⟩ he
      exact False.elim (hh.1 hxK)
    · have hh := hkey d ⟨x,hxL⟩ he.symm
      exact False.elim (hh.1 hxK)
    · have hh := hkey e (p d) he
      have hde : d=e := Subtype.ext ((ha d).2.symm.trans hh.2)
      exact congrArg some hde
  let _ := Fintype.ofFinite B
  let _ := Fintype.ofFinite (Faces H)
  have hb := Nat.card_le_card_of_injective f hinj
  change Nat.card B + 1 ≤ Nat.card (Faces H)
  simpa only [Nat.card_eq_fintype_card,Fintype.card_option] using hb

end CannonEmbeddedArc.Arc

end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI

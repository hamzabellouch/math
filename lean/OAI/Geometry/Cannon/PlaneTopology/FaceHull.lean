import Mathlib
import OAI.Geometry.Cannon.PlaneTopology.PairComponentClosure
import OAI.Geometry.Cannon.PlaneTopology.FacialStar
import OAI.Geometry.Cannon.PlaneTopology.GraphEdgeValueCompatible
import OAI.Geometry.Cannon.Topology.Retraction

namespace OAI

section
section
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Topology Metric unitInterval CannonFaceIncidence

variable {ι : Type*} [Fintype ι]

def faceHull (F : ι → Arc ℂ) (z : ℂ → ℂ) (d : Faces F) : Set ℂ :=
  convexHull ℝ (z '' (faceVertices F d : Set ℂ))

lemma graph_extension_hull [DecidableEq ι] [Nonempty ι] (F : ι → Arc ℂ)
    (hF : Pairwise fun i j=>Compatible (F i) (F j))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃p∈Q,segment ℝ p.1 p.2)
    (z : ℂ → ℂ) (g : C(ℂ,ℂ))
    (hg : ∀ i t,g (F i t)=Path.segment (z (F i 0)) (z (F i 1)) t)
    (d : Faces F) {x : ℂ} (hx : x∈closure (face F d)) (hgraph : x∈⋃i,range (F i)) :
    g x∈faceHull F z d := by
  let _ : LocallyConnectedSpace ((⋃ i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i=>(F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  let _ : DiscreteTopology (ConnectedComponents ((⋃ i,range (F i))ᶜ : Set ℂ)) := inferInstance
  have hcl := tame_region_closure F hF Q hQ ConnectedComponents.continuous_coe d
  change closure (face F d)=face F d∪_ at hcl
  rw [hcl] at hx
  have hxE : x∈⋃i∈regionEdges F ConnectedComponents.mk d,range (F i) := by
    rcases hx with hx|hx
    · exact (hx.1 hgraph).elim
    · exact hx
  obtain ⟨i,hi,t,rfl⟩ := mem_iUnion₂.mp hxE
  have ends : F i 0∈faceVertices F d ∧ F i 1∈faceVertices F d := by
    exact ⟨(mem_faceVertices F _ _).mpr ⟨⟨i,Or.inl rfl⟩,
      region_edge_in_closure F hF Q hQ ConnectedComponents.continuous_coe hi ⟨0,rfl⟩⟩,
      (mem_faceVertices F _ _).mpr ⟨⟨i,Or.inr rfl⟩,
      region_edge_in_closure F hF Q hQ ConnectedComponents.continuous_coe hi ⟨1,rfl⟩⟩⟩
  rw [hg]
  have h0 : z (F i 0)∈faceHull F z d :=
    subset_convexHull ℝ (z '' (faceVertices F d : Set ℂ)) ⟨F i 0,ends.1,rfl⟩
  have h1 : z (F i 1)∈faceHull F z d :=
    subset_convexHull ℝ (z '' (faceVertices F d : Set ℂ)) ⟨F i 1,ends.2,rfl⟩
  exact (convex_convexHull ℝ (z '' (faceVertices F d : Set ℂ))).segment_subset h0 h1
    (by rw [←Path.range_segment]; exact mem_range_self t)

theorem exists_facewise_convex_realization [DecidableEq ι] [Nonempty ι] (F : ι → Arc ℂ)
    (hF : Pairwise fun i j=>Compatible (F i) (F j))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃p∈Q,segment ℝ p.1 p.2)
    (hcorner : ∀ d : Faces F,(faceVertices F d).Nonempty) (z : ℂ → ℂ) :
    ∃ g : C(ℂ,ℂ),
      (∀ i t,g (F i t)=Path.segment (z (F i 0)) (z (F i 1)) t) ∧
      ∀ d : Faces F,MapsTo g (closure (face F d)) (faceHull F z d) := by
  classical
  let _ : Finite (Faces F) := faces_finite F hF Q hQ
  obtain ⟨g,hg⟩:=extend_graph F hF z
  have hnon (d : Faces F) : (faceHull F z d).Nonempty :=
    ((hcorner d).to_set.image z).mono (subset_convexHull ℝ _)
  have hclosed (d : Faces F) : IsClosed (faceHull F z d) :=
    (((faceVertices F d).finite_toSet.image z).isCompact_convexHull ℝ).isClosed
  have hproj (d : Faces F) := CannonConvexRetraction.exists_retraction
    (faceHull F z d) (hnon d) (hclosed d) (convex_convexHull ℝ _)
  choose P hLip hP hfix using hproj
  let f (d : Faces F) : C(ℂ,ℂ) := ⟨fun x=>P d (g x),(hLip d).continuous.comp g.continuous⟩
  have hf (d : Faces F) (x : ℂ) (hx : x∈closure (face F d)) (hxK : x∈⋃i,range (F i)) :
      f d x=g x := hfix d (g x) (graph_extension_hull F hF Q hQ z g hg d hx hxK)
  obtain ⟨f₀,hf₀⟩:=CannonFiniteClosedGluing.exists_gluing
    (fun d : Faces F=>closure (face F d)) (fun _=>isClosed_closure)
    (facial_closures_cover F hF Q hQ) f (by
      intro d e x hxd hxe
      by_cases hde : d=e
      · rw [hde]
      have hxK : x∈⋃i,range (F i) := by
        by_contra hxK
        let c : Faces F := ConnectedComponents.mk ⟨x,hxK⟩
        have hc : x∈face F c := ⟨hxK,rfl⟩
        exact hde ((same_face_of_mem_closure F hc hxd).symm.trans (same_face_of_mem_closure F hc hxe))
      exact (hf d x hxd hxK).trans (hf e x hxe hxK).symm)
  refine ⟨f₀,?_,?_⟩
  · intro i t
    obtain ⟨d,hd⟩ := facial_closures_cover F hF Q hQ (F i t)
    exact (hf₀ d _ hd).trans ((hf d _ hd (mem_iUnion.mpr ⟨i,mem_range_self t⟩)).trans (hg i t))
  · intro d x hx
    rw [hf₀ d x hx]
    exact hP d (g x)
end CannonEmbeddedArc.Arc

end
end
end
end

end OAI

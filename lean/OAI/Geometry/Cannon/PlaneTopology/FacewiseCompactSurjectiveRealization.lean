import Mathlib
import OAI.Geometry.Cannon.PlaneTopology.FaceHull
import OAI.Geometry.Cannon.Uniformization.LocalCompactSurjection

namespace OAI

section
section
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Topology Metric unitInterval CannonFaceIncidence

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem exists_facewise_compact_surjective_realization (F : ι → Arc ℂ)
    (hF : Pairwise fun i j=>Compatible (F i) (F j))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃p∈Q,segment ℝ p.1 p.2)
    (hcorner : ∀ d : Faces F,(faceVertices F d).Nonempty) (z : ℂ → ℂ) :
    ∃ g : C(ℂ,ℂ),
      (∀ i t,g (F i t)=Path.segment (z (F i 0)) (z (F i 1)) t) ∧
      ∀ d : Faces F,MapsTo g (closure (face F d)) (faceHull F z d) ∧
        ∃ W : Set ℂ,IsCompact W ∧ W⊆face F d ∧ faceHull F z d⊆g '' W := by
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
  have hlocal (d : Faces F) := CannonLocalRealization.exists_local_compact_surjection
    (faceHull F z d) (face F d) (((faceVertices F d).finite_toSet.image z).isCompact_convexHull ℝ)
    (face_open F d) (face_nonempty F d) g
  choose gd hgd W hW hWU honto using hlocal
  let f (d : Faces F) : C(ℂ,ℂ) := ⟨fun x=>P d (gd d x),(hLip d).continuous.comp (gd d).continuous⟩
  have hf (d : Faces F) (x : ℂ) (hx : x∈closure (face F d)) (hxK : x∈⋃i,range (F i)) :
      f d x=g x := by
    have hnot : x∈(face F d)ᶜ := fun H=>H.1 hxK
    change P d (gd d x)=g x
    rw [hgd d hnot]
    exact hfix d (g x) (graph_extension_hull F hF Q hQ z g hg d hx hxK)
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
  · intro d
    constructor
    · intro x hx
      rw [hf₀ d x hx]
      exact hP d (gd d x)
    · refine ⟨W d,hW d,hWU d,?_⟩
      intro y hy
      obtain ⟨x,hx,hxy⟩:=honto d hy
      refine ⟨x,hx,?_⟩
      rw [hf₀ d x (subset_closure (hWU d hx))]
      change P d (gd d x)=y
      rw [hxy]
      exact hfix d y hy
end CannonEmbeddedArc.Arc

end
end
end
end

end OAI

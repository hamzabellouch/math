import Mathlib
import OAI.Geometry.Cannon.PlaneTopology.FacewiseCompactSurjectiveRealization
import OAI.Geometry.Cannon.Topology.ExteriorConnected

namespace OAI

section
section
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Topology Metric unitInterval CannonFaceIncidence CannonPlanarEuler

variable {ι : Type*} [Fintype ι] [Nonempty ι]

omit [Nonempty ι] in
theorem outer_face_compact_others (F : ι → Arc ℂ) :
    ∃ out : Faces F,∀ d : Faces F,d≠out → IsCompact (closure (face F d)) := by
  have hK : IsCompact (⋃ i,range (F i)) := isCompact_iUnion fun i=>(F i).compact_range
  obtain ⟨R,hR,hKR⟩ := hK.isBounded.subset_ball_lt 0 (0:ℂ)
  let E := {z : ℂ | R<‖z‖}
  have hE := CannonPlaneExterior.exterior_connected hR.le
  have hEK : E⊆(⋃ i,range (F i))ᶜ := by
    intro z hz hKz
    have hb := hKR hKz
    rw [mem_ball,dist_zero_right] at hb
    exact (lt_asymm hz hb)
  obtain ⟨x,hx⟩ := hE.nonempty
  let out : Faces F := ConnectedComponents.mk ⟨x,hEK hx⟩
  have hEf : E⊆face F out := by
    change E⊆region _ ConnectedComponents.mk _
    rw [component_region_eq]
    exact hE.isPreconnected.subset_connectedComponentIn hx hEK
  refine ⟨out,?_⟩
  intro d hd
  have hsub : face F d⊆closedBall (0:ℂ) R := by
    intro z hz
    rw [mem_closedBall,dist_zero_right]
    by_contra hh
    have ho := hEf (lt_of_not_ge hh)
    exact hd (hz.2.symm.trans ho.2)
  exact (isCompact_closedBall (0:ℂ) R).of_isClosed_subset isClosed_closure
    (closure_minimal hsub isClosed_closedBall)

variable {X : Type*} [TopologicalSpace X] [T2Space X]

def compactifiedFace (F : ι → Arc ℂ) (e : ℂ → X) (d : Faces F) : Set X :=
  closure (e '' face F d)

theorem compactified_face_interiors_cover [DecidableEq ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j=>Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃q∈Q,segment ℝ q.1 q.2)
    (hcorner : ∀ d : Faces F,(faceVertices F d).Nonempty)
    (e : ℂ → X) (he : IsOpenEmbedding e) (p : X) (heR : range e={p}ᶜ)
    (hdense : DenseRange e) :
    (∀ x : X,∃ d : Faces F,x∈compactifiedFace F e d) ∧
    ∀ x : X,∃ v∈vertices F Finset.univ,
      x∈interior (⋃ d : Faces F,⋃ (_ : v∈faceVertices F d),compactifiedFace F e d) := by
  classical
  let _ : Finite (Faces F) := faces_finite F hF Q hQ
  have hcover : ∀ x : X,∃ d : Faces F,x∈compactifiedFace F e d := by
    have hclosed : IsClosed (⋃ d : Faces F,compactifiedFace F e d) :=
      isClosed_iUnion_of_finite fun _=>isClosed_closure
    have hsub : range e⊆⋃d : Faces F,compactifiedFace F e d := by
      rintro _ ⟨z,rfl⟩
      obtain ⟨d,hd⟩ := facial_closures_cover F hF Q hQ z
      exact mem_iUnion.mpr ⟨d,image_closure_subset_closure_image he.continuous ⟨z,hd,rfl⟩⟩
    intro x
    exact mem_iUnion.mp ((closure_minimal hsub hclosed) (hdense x))
  refine ⟨hcover,?_⟩
  obtain ⟨out,hout⟩ := outer_face_compact_others F
  have hp (d : Faces F) (hd : p∈compactifiedFace F e d) : d=out := by
    by_contra hn
    have hsub : compactifiedFace F e d⊆e '' closure (face F d) :=
      closure_minimal (image_mono subset_closure) (((hout d hn).image he.continuous).isClosed)
    have hpr : p∈range e := image_subset_range e _ (hsub hd)
    rw [heR] at hpr
    exact hpr (mem_singleton p)
  intro x
  by_cases hxp : x=p
  · subst x
    obtain ⟨v,hv⟩ := hcorner out
    have hvV := ((mem_faceVertices F out v).mp hv).1
    obtain ⟨i,hi⟩ := hvV
    refine ⟨v,(mem_vertices F Finset.univ v).mpr ⟨i,Finset.mem_univ _,hi⟩,?_⟩
    apply CannonFacialStars.interior_union_at _ (fun _=>isClosed_closure) hcover
    intro d hd
    exact (hp d hd).symm ▸ hv
  · have hxr : x∈range e := by rw [heR]; exact hxp
    obtain ⟨z,rfl⟩ := hxr
    obtain ⟨v,hv,hvd⟩ := common_vertex_at F hF Q hQ hcorner z
    refine ⟨v,hv,?_⟩
    apply CannonFacialStars.interior_union_at _ (fun _=>isClosed_closure) hcover
    intro d hd
    apply hvd d
    rw [he.isEmbedding.closure_eq_preimage_closure_image]
    exact hd
end CannonEmbeddedArc.Arc

end
end
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Topology Metric unitInterval CannonFaceIncidence

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem exists_eventually_constant_facewise_realization (F : ι → Arc ℂ)
    (hF : Pairwise fun i j=>Compatible (F i) (F j))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃p∈Q,segment ℝ p.1 p.2)
    (hcorner : ∀ d : Faces F,(faceVertices F d).Nonempty) (z : ℂ → ℂ)
    (out : Faces F) (hout : ∀ d : Faces F,d≠out → IsCompact (closure (face F d)))
    (q : ℂ) (hq : q∈faceHull F z out) :
    ∃ g : C(ℂ,ℂ),∃ K : Set ℂ,IsCompact K ∧
      (∀ x,x∉K → g x=q) ∧
      (∀ i t,g (F i t)=Path.segment (z (F i 0)) (z (F i 1)) t) ∧
      ∀ d : Faces F,MapsTo g (closure (face F d)) (faceHull F z d) ∧ faceHull F z d⊆g '' face F d := by
  classical
  let _ : Finite (Faces F) := faces_finite F hF Q hQ
  obtain ⟨g,hg,hgD⟩:=exists_facewise_compact_surjective_realization F hF Q hQ hcorner z
  choose W hW hWU honto using fun d=>(hgD d).2
  let A : Set ℂ := (⋃ i,range (F i)) ∪ (⋃ d : Faces F,W d) ∪
    (⋃ d : {d : Faces F // d≠out},closure (face F d.val))
  have hA : IsCompact A := ((isCompact_iUnion fun i=>(F i).compact_range).union
    (isCompact_iUnion hW)).union (isCompact_iUnion fun d=>hout d.val d.property)
  obtain ⟨ψ,hψ,hψK,_,hψV⟩:=exists_continuousMap_one_of_isCompact_subset_isOpen hA isOpen_univ (subset_univ _)
  let f : C(ℂ,ℂ) := ⟨fun x=>(ψ x) • g x+(1-ψ x) • q,
    (ψ.continuous.smul g.continuous).add ((continuous_const.sub ψ.continuous).smul continuous_const)⟩
  have hfA {x : ℂ} (hx : x∈A) : f x=g x := by
    change (ψ x) • g x+(1-ψ x) • q=g x
    simp [hψ hx]
  refine ⟨f,tsupport ψ,hψK,?_,?_,?_⟩
  · intro x hx
    have hz : ψ x=0 := by
      by_contra hn
      exact hx (subset_closure hn)
    change (ψ x) • g x+(1-ψ x) • q=q
    simp [hz]
  · intro i t
    exact (hfA (Or.inl (Or.inl (mem_iUnion.mpr ⟨i,mem_range_self t⟩)))).trans (hg i t)
  · intro d
    constructor
    · intro x hx
      by_cases hd : d=out
      · subst d
        exact (convex_convexHull ℝ _) ((hgD out).1 hx) hq (hψV x).1
          (sub_nonneg.mpr (hψV x).2) (by ring)
      · rw [hfA (Or.inr (mem_iUnion.mpr ⟨⟨d,hd⟩,hx⟩))]
        exact (hgD d).1 hx
    · intro y hy
      obtain ⟨x,hx,hxy⟩:=honto d hy
      exact ⟨x,hWU d hx,(hfA (Or.inl (Or.inr (mem_iUnion.mpr ⟨d,hx⟩)))).trans hxy⟩
end CannonEmbeddedArc.Arc

end
end
end
end

end OAI

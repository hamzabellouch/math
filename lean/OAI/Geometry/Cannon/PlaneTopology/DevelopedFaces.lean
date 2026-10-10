import Mathlib
import OAI.Geometry.Cannon.PlaneTopology.NoSingleFaceDiscordance
import OAI.Geometry.Cannon.PlaneTopology.IntrinsicCircleData
import OAI.Geometry.Cannon.CirclePacking.TrianglePoint

namespace OAI

section
section
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonFaceIncidence CannonPackingGeometry CannonPlanarEuler

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] [Nonempty ι] in
theorem intrinsic_metric_angles (F : ι → Arc ℂ) [Fintype (Faces F)]
    (out : Faces F) (hdata : HasIntrinsicCircleData F out) :
    ∃ r : ℂ → ℝ,∃ α : Faces F → ℂ → ℝ,
      (∀ q,0<r q) ∧
      (∀ d,d≠out → ∀ q∈faceVertices F d,α d q∈Ioo (0:ℝ) Real.pi) ∧
      (∀ q,Vertex F q → (∑ d,α d q)=if q∈faceVertices F out then Real.pi/3 else 2*Real.pi) ∧
      (∀ d q,q∉faceVertices F d → α d q=0) ∧ (∀ q,α out q=0) ∧
      (∀ d,d≠out → ∀ u∈faceVertices F d,∀ v∈faceVertices F d,∀ w∈faceVertices F d,
        u≠v → u≠w → v≠w →
        2*(r u+r v)*(r u+r w)*Real.cos (α d u)=(r u+r v)^2+(r u+r w)^2-(r v+r w)^2) := by
  classical
  obtain ⟨vertex,hinj,hR,θ,r,q,hθ,hθf,hθv,hr,hq,htan⟩ := hdata
  let V := vertices F Finset.univ
  let A := {d : Faces F // d≠out}
  let vtx : A × Fin 3 → ℂ := fun i=>(vertex i).val
  have hvinj (f:A) : Function.Injective (fun k=>vtx (f,k)) := Subtype.val_injective.comp (hinj f)
  have hm (f:A) (v:ℂ) : (∃ k,vtx (f,k)=v) ↔ v∈faceVertices F f.val := by
    change v∈range (fun k=>(vertex (f,k)).val) ↔ _
    rw [hR f]
    rfl
  let rad : ℂ → ℝ := fun v=>if h:v∈V then r ⟨v,h⟩ else 1
  have hrad (v:V) : rad v.val=r v := by simp [rad,v.property]
  let α : Faces F → ℂ → ℝ := fun d v=>if h:d≠out then cornerAngle vtx θ ⟨d,h⟩ v else 0
  have hα (f:A) (v:ℂ) : α f.val v=cornerAngle vtx θ f v := by simp [α,f.property]
  have hαat (f:A) (k:Fin 3) : α f.val (vtx (f,k))=θ (f,k) := by
    rw [hα,cornerAngle_at vtx θ hvinj]
  refine ⟨rad,α,?_,?_,?_,?_,?_,?_⟩
  · intro v
    dsimp [rad]
    split_ifs
    · exact hr _
    · norm_num
  · intro d hd v hv
    obtain ⟨k,hk⟩ := (hm ⟨d,hd⟩ v).mpr hv
    rw [←hk,hαat ⟨d,hd⟩ k]
    exact hθ _
  · intro v hv
    have hvV : v∈V := by
      obtain ⟨i,hi⟩ := hv
      exact (mem_vertices F Finset.univ v).mpr ⟨i,Finset.mem_univ _,hi⟩
    have he : (∑ d,α d v)=∑ f:A,cornerAngle vtx θ f v := by
      have hh := Fintype.sum_subtype_add_sum_subtype (fun d : Faces F=>d≠out) (fun d=>α d v)
      have hz : (∑ d : {d : Faces F // ¬d≠out},α d.val v)=0 := by
        apply Finset.sum_eq_zero
        intro d hd
        have he : d.val=out := not_ne_iff.mp d.property
        simp [he,α]
      rw [hz,add_zero] at hh
      rw [←hh]
      exact Finset.sum_congr rfl (fun f hf=>hα f v)
    rw [he,sum_cornerAngle]
    have hh := hθv ⟨v,hvV⟩
    convert hh using 1
    apply Finset.sum_congr rfl
    intro i hi
    have he : (vertex i).val=v ↔ vertex i=⟨v,hvV⟩ := ⟨fun h=>Subtype.ext h,fun h=>congrArg Subtype.val h⟩
    simp only [vtx,he]
  · intro d v hv
    by_cases hd : d≠out
    · rw [hα ⟨d,hd⟩]
      exact cornerAngle_zero vtx θ ⟨d,hd⟩ v (fun h=>hv ((hm ⟨d,hd⟩ v).mp h))
    · simp [α,hd]
  · intro v; simp [α]
  · intro d hd u hu v hv w hw huv huw hvw
    let f:A := ⟨d,hd⟩
    obtain ⟨i,hi⟩ := (hm f u).mpr hu
    obtain ⟨j,hj⟩ := (hm f v).mpr hv
    obtain ⟨k,hk⟩ := (hm f w).mpr hw
    have hij:i≠j := fun h=>huv (hi.symm.trans (h ▸ hj))
    have hik:i≠k := fun h=>huw (hi.symm.trans (h ▸ hk))
    have hjk:j≠k := fun h=>hvw (hj.symm.trans (h ▸ hk))
    rw [←hi,←hj,←hk,hαat f i]
    simp only [vtx,hrad]
    exact intrinsic_cosine_law_fin3 (fun k=>θ (f,k)) (fun k=>r (vertex (f,k))) (q f)
      (fun k=>hθ (f,k)) (hθf f) (fun k=>hr _) (hq f) (fun k=>htan (f,k)) hij hik hjk
end CannonEmbeddedArc.Arc

end
end
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonFaceIncidence CannonPackingGeometry

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

structure DevelopedFaces (F : ι → Arc ℂ) [Fintype (Faces F)] (out : Faces F) where
  radius : ℂ → ℝ
  radius_pos : ∀ q,0<radius q
  chart : Faces F → ℂ → ℂ
  lengths : ∀ d,∀ u∈faceVertices F d,∀ v∈faceVertices F d,u≠v →
    dist (chart d u) (chart d v)=radius u+radius v
  angle : Faces F → ℂ → ℝ
  angle_pos : ∀ d,d≠out → ∀ q∈faceVertices F d,angle d q∈Ioo (0:ℝ) Real.pi
  angle_sum : ∀ q,Vertex F q → (∑ d,angle d q)=if q∈faceVertices F out then Real.pi/3 else 2*Real.pi
  angle_zero : ∀ d q,q∉faceVertices F d → angle d q=0
  angle_out : ∀ q,angle out q=0
  cosine : ∀ d,d≠out → ∀ u∈faceVertices F d,∀ v∈faceVertices F d,∀ w∈faceVertices F d,
    u≠v → u≠w → v≠w →
    2*(radius u+radius v)*(radius u+radius w)*Real.cos (angle d u)=
      (radius u+radius v)^2+(radius u+radius w)^2-(radius v+radius w)^2
  edge_agree : ∀ i d e,d≠out → e≠out →
    i∈regionEdges F ConnectedComponents.mk d → i∈regionEdges F ConnectedComponents.mk e →
    chart d (F i 0)=chart e (F i 0) ∧ chart d (F i 1)=chart e (F i 1)
  opposite : ∀ i d e,d≠e → d≠out → e≠out →
    i∈regionEdges F ConnectedComponents.mk d → i∈regionEdges F ConnectedComponents.mk e →
    ∀ u∈faceVertices F d,u≠F i 0 → u≠F i 1 →
    ∀ v∈faceVertices F e,v≠F i 0 → v≠F i 1 →
    orientedArea (chart e (F i 0)) (chart e (F i 1)) (chart d u)*
      orientedArea (chart e (F i 0)) (chart e (F i 1)) (chart e v)<0

theorem intrinsic_developed_faces (F : ι → Arc ℂ)
    (hF : Pairwise fun i j=>Compatible (F i) (F j))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q}))
    [Fintype (Faces F)] (out : Faces F) (hthree : ∀ d,(faceVertices F d).card=3)
    (hdata : HasIntrinsicCircleData F out) : Nonempty (DevelopedFaces F out) := by
  classical
  let _ : LocallyConnectedSpace ((⋃ i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i=>(F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  let _ : DiscreteTopology (ConnectedComponents ((⋃ i,range (F i))ᶜ : Set ℂ)) := inferInstance
  obtain ⟨r,α,hr,hα,hαsum,hαzero,hαout,hcos⟩ := intrinsic_metric_angles F out hdata
  have exchart (d : Faces F) := triangle_chart (faceVertices F d) (hthree d) r hr
  choose c hc using exchart
  have exedge (i : ι) := noncut_edge_two_faces F hF Q hQ hK i
  choose a b hab ha hb using exedge
  have ends (i : ι) (d : Faces F) (hi : i∈regionEdges F ConnectedComponents.mk d) :
      F i 0∈faceVertices F d ∧ F i 1∈faceVertices F d := by
    exact ⟨(mem_faceVertices F _ _).mpr ⟨⟨i,Or.inl rfl⟩,
      region_edge_in_closure F hF Q hQ ConnectedComponents.continuous_coe hi ⟨0,rfl⟩⟩,
      (mem_faceVertices F _ _).mpr ⟨⟨i,Or.inr rfl⟩,
      region_edge_in_closure F hF Q hQ ConnectedComponents.continuous_coe hi ⟨1,rfl⟩⟩⟩
  have exfold (i : ι) := (exists_fold (hthree (a i)) (hthree (b i)) hr (hc (a i)) (hc (b i))
    (ends i _ (ha i)).1 (ends i _ (ha i)).2 (ends i _ (hb i)).1 (ends i _ (hb i)).2 (F i).endpoints_ne).exists
  choose K hfold using exfold
  have hflat (q : ℂ) (hq : Vertex F q) (hqo : q∉faceVertices F out) :
      ∃ t : Faces F → (ℂ ≃ᵢ ℂ),∀ j,q∈range (F j) → K j*t (a j)=t (b j) := by
    have hinner (d : IncidentFaces F q) : d.val≠out := by
      intro hd
      exact hqo ((mem_faceVertices F _ _).mpr ⟨hq,hd ▸ d.property⟩)
    have hmem (d : IncidentFaces F q) : q∈faceVertices F d.val := (mem_faceVertices F _ _).mpr ⟨hq,d.property⟩
    have hsum : (∑ d : IncidentFaces F q,α d.val q)=2*Real.pi := by
      have hh := Fintype.sum_subtype_add_sum_subtype (fun d : Faces F=>q∈closure (face F d)) (fun d=>α d q)
      have hz : (∑ d : {d : Faces F // ¬q∈closure (face F d)},α d.val q)=0 := by
        apply Finset.sum_eq_zero
        intro d hd
        exact hαzero _ _ (fun h=>d.property ((mem_faceVertices F _ _).mp h).2)
      rw [hz,add_zero,hαsum q hq,ite_eq_right hqo] at hh
      exact hh
    exact metric_star_flat F hF Q hQ hK a b hab ha hb r hr c hc K hfold hq
      (fun d=>α d.val q) (fun d=>hα d.val (hinner d) q (hmem d)) hsum
      (fun d u hu v hv hqu hqv huv=>hcos d.val (hinner d) q (hmem d) u hu v hv hqu hqv huv)
  obtain ⟨t,ht⟩ := triangular_disk_gauge_integrates F hF Q hQ hK out (hthree out) a b hab ha hb K hflat
  let z : Faces F → ℂ → ℂ := fun d u=>(t d).symm (c d u)
  have htrans (i : ι) (hai : a i≠out) (hbi : b i≠out) (u : ℂ) :
      (t (b i)).symm (K i (c (a i) u))=z (a i) u := by
    have h := congrArg (fun e : ℂ ≃ᵢ ℂ=>e ((t (a i)).symm (c (a i) u))) (ht i hai hbi)
    have h' : K i (c (a i) u)=t (b i) (z (a i) u) := by simpa [z] using h
    exact (t (b i)).symm_apply_eq.mpr h'
  have hagree (i : ι) (hai : a i≠out) (hbi : b i≠out) :
      z (a i) (F i 0)=z (b i) (F i 0) ∧ z (a i) (F i 1)=z (b i) (F i 1) := by
    constructor
    · rw [←htrans i hai hbi,(hfold i).1]
    · rw [←htrans i hai hbi,(hfold i).2.1]
  have hopp (i : ι) (hai : a i≠out) (hbi : b i≠out) :
      Folds (1 : ℂ ≃ᵢ ℂ) (z (a i)) (z (b i)) (faceVertices F (a i)) (faceVertices F (b i)) (F i 0) (F i 1) := by
    refine ⟨(hagree i hai hbi).1,(hagree i hai hbi).2,?_⟩
    intro u hu hu0 hu1 v hv hv0 hv1
    have hh := isometry_orientedArea_product (t (b i)).symm
      (c (b i) (F i 0)) (c (b i) (F i 1)) (K i (c (a i) u)) (c (b i) v)
    rw [htrans i hai hbi] at hh
    change orientedArea (z (b i) (F i 0)) (z (b i) (F i 1)) (z (a i) u)*
      orientedArea (z (b i) (F i 0)) (z (b i) (F i 1)) (z (b i) v)<0
    rw [hh]
    exact (hfold i).2.2 u hu hu0 hu1 v hv hv0 hv1
  refine ⟨{
    radius := r
    radius_pos := hr
    chart := z
    lengths := ?_
    angle := α
    angle_pos := hα
    angle_sum := hαsum
    angle_zero := hαzero
    angle_out := hαout
    cosine := hcos
    edge_agree := ?_
    opposite := ?_ }⟩
  · intro d u hu v hv huv
    simpa only [z,IsometryEquiv.dist_eq] using hc d u hu v hv huv
  · intro i d e hd he hdi hei
    rcases edge_face_unique_two F hF Q hQ i (hab i) (ha i) (hb i) hdi with rfl|rfl <;>
      rcases edge_face_unique_two F hF Q hQ i (hab i) (ha i) (hb i) hei with rfl|rfl
    · exact ⟨rfl,rfl⟩
    · exact hagree i hd he
    · exact ⟨(hagree i he hd).1.symm,(hagree i he hd).2.symm⟩
    · exact ⟨rfl,rfl⟩
  · intro i d e hde hd he hdi hei
    rcases edge_face_unique_two F hF Q hQ i (hab i) (ha i) (hb i) hdi with rfl|rfl <;>
      rcases edge_face_unique_two F hF Q hQ i (hab i) (ha i) (hb i) hei with rfl|rfl
    · exact (hde rfl).elim
    · exact (hopp i hd he).2.2
    · exact (hopp i he hd).symm.2.2
    · exact (hde rfl).elim
end CannonEmbeddedArc.Arc

end
end
end
end

end OAI

import Mathlib
import OAI.Geometry.Cannon.PlaneTopology.NoncutEdgeTwoFaces
import OAI.Geometry.Cannon.PlaneTopology.FacialStar
import OAI.Geometry.Cannon.Boundary.GraphPreconnected
import OAI.Geometry.Cannon.PlanarGraphs.FiniteClosedLocal

namespace OAI

section
section
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonFaceIncidence CannonPlanarEuler CannonVertexLinks

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
abbrev IncidentFaces (F : ι → Arc ℂ) (q : ℂ) := {d : Faces F | q∈closure (face F d)}
abbrev IncidentEdges (F : ι → Arc ℂ) (q : ℂ) := {i : ι | q∈range (F i)}
def vertexFaceGraph (F : ι → Arc ℂ) (q : ℂ) : SimpleGraph (IncidentFaces F q) where
  Adj d c := d≠c ∧ ∃ i : ι,q∈range (F i) ∧
    i∈regionEdges F ConnectedComponents.mk d.val ∧
    i∈regionEdges F ConnectedComponents.mk c.val
  symm := ⟨by rintro d c ⟨hne,i,hi,hd,hc⟩; exact ⟨hne.symm,i,hi,hc,hd⟩⟩
  loopless := ⟨fun d h=>h.1 rfl⟩

omit [DecidableEq ι] [Nonempty ι] in
theorem vertexFaceGraph_preconnected [DecidableEq ι] [Nonempty ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j=>Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    {q : ℂ} (hq : Vertex F q) : (vertexFaceGraph F q).Preconnected := by
  classical
  let _ : Finite (Faces F) := faces_finite F hF Q hQ
  let _ : LocallyConnectedSpace ((⋃ i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i=>(F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  let _ : DiscreteTopology (ConnectedComponents ((⋃ i,range (F i))ᶜ : Set ℂ)) := inferInstance
  obtain ⟨rF,hrF,hnearF⟩ := finite_closed_local (fun d : Faces F=>closure (face F d))
    (fun _=>isClosed_closure) q
  obtain ⟨rE,hrE,hnearE⟩ := finite_closed_local (fun i=>range (F i))
    (fun i=>(F i).compact_range.isClosed) q
  obtain ⟨rV,hrV,hnearV⟩ := finite_closed_local
    (fun v : (vertices F Finset.univ : Set ℂ)=>({v.val}:Set ℂ)) (fun _=>isClosed_singleton) q
  choose w hw using face_nonempty F
  have hqw (d : Faces F) : 0<dist (w d) q := by
    apply dist_pos.mpr
    intro h
    exact (hw d).1 (h.symm ▸ vertex_mem_support F hq)
  obtain ⟨rW,hrW,hfar⟩ := finite_pos_lower (fun d=>dist (w d) q) hqw
  let r := min (min rF rE) (min rV rW)/2
  have hr : 0<r := half_pos (lt_min (lt_min hrF hrE) (lt_min hrV hrW))
  have hsmall : r<rF ∧ r<rE ∧ r<rV ∧ r<rW := by
    have ht : r < min (min rF rE) (min rV rW) := half_lt_self (lt_min (lt_min hrF hrE) (lt_min hrV hrW))
    exact ⟨ht.trans_le ((min_le_left _ _).trans (min_le_left _ _)),
      ht.trans_le ((min_le_left _ _).trans (min_le_right _ _)),
      ht.trans_le ((min_le_right _ _).trans (min_le_left _ _)),
      ht.trans_le ((min_le_right _ _).trans (min_le_right _ _))⟩
  let C (d : IncidentFaces F q) : Set ℂ := sphere q r∩closure (face F d.val)
  have hcover : (⋃d,C d)=sphere q r := by
    apply Subset.antisymm
    · exact iUnion_subset fun _=>inter_subset_left
    · intro z hz
      obtain ⟨d,hd⟩ := facial_closures_cover F hF Q hQ z
      have hqd := hnearF z (show z∈ball q rF from by rw [mem_ball,(mem_sphere.mp hz)]; exact hsmall.1) d hd
      exact mem_iUnion.mpr ⟨⟨d,hqd⟩,hz,hd⟩
  have hne (d : IncidentFaces F q) : (C d).Nonempty := by
    obtain ⟨z,hz,hzdist⟩ := Metric.mem_closure_iff.mp d.property r hr
    have hc : IsPreconnected (face F d.val) := (component_region_connected _ d.val).isPreconnected
    obtain ⟨y,hy,hyd⟩ := hc.intermediate_value hz (hw d.val)
      (continuous_id.dist continuous_const).continuousOn
      (show r∈Icc (dist z q) (dist (w d.val) q) from
        ⟨by rw [dist_comm]; exact hzdist.le,(hsmall.2.2.2.trans (hfar d.val)).le⟩)
    exact ⟨y,mem_sphere.mpr hyd,subset_closure hy⟩
  refine CannonClosedCover.graph_preconnected (vertexFaceGraph F q) C
    (fun _=>isClosed_sphere.inter isClosed_closure) ?_ hne ?_
  · rw [hcover]
    exact (isConnected_sphere (E:=ℂ) (by rw [Complex.rank_real_complex]; norm_num) q hr.le).isPreconnected
  intro d c hdc ⟨z,hzd,hzc⟩
  have hzq : z≠q := by intro h; have he := mem_sphere.mp hzd.1; rw [h,dist_self] at he; linarith
  have hzV : ¬Vertex F z := by
    intro hz
    obtain ⟨i,hi⟩ := hz
    have hv : z∈vertices F Finset.univ := (mem_vertices F Finset.univ z).mpr ⟨i,Finset.mem_univ _,hi⟩
    have hqz := hnearV z (by rw [mem_ball,mem_sphere.mp hzd.1]; exact hsmall.2.2.1) ⟨z,hv⟩ rfl
    exact hzq hqz.symm
  have hzK : z∈⋃i,range (F i) := by
    by_contra hn
    have get (a : Faces F) (ha : z∈closure (face F a)) : z∈face F a := by
      change z∈closure (region ((⋃ i,range (F i))ᶜ) ConnectedComponents.mk a) at ha
      rw [tame_region_closure F hF Q hQ ConnectedComponents.continuous_coe a] at ha
      rcases ha with h|h
      · exact h
      · obtain ⟨i,-,hi⟩ := mem_iUnion₂.mp h
        exact (hn (mem_iUnion.mpr ⟨i,hi⟩)).elim
    have hd := get d.val hzd.2
    have hc := get c.val hzc.2
    exact hdc (Subtype.ext (hd.2.symm.trans hc.2))
  obtain ⟨i,t,rfl⟩ := mem_iUnion.mp hzK
  have ht₀ : 0<t := by
    apply lt_of_le_of_ne (nonneg t)
    intro he
    exact hzV ⟨i,Or.inl (congrArg (F i) (show (0:I)=t from Subtype.ext he))⟩
  have ht₁ : t<1 := by
    apply lt_of_le_of_ne (le_one t)
    intro he
    exact hzV ⟨i,Or.inr (congrArg (F i) (show (1:I)=t from Subtype.ext he.symm))⟩
  refine ⟨hdc,i,?_,⟨t,ht₀,ht₁,hzd.2⟩,⟨t,ht₀,ht₁,hzc.2⟩⟩
  exact hnearE (F i t) (by rw [mem_ball,mem_sphere.mp hzd.1]; exact hsmall.2.1) i (mem_range_self t)
end CannonEmbeddedArc.Arc

end
end
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonFaceIncidence CannonPlanarEuler

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
def vertexLink (F : ι → Arc ℂ) (q : ℂ) : SimpleGraph (IncidentEdges F q ⊕ IncidentFaces F q) where
  Adj
    | .inl i,.inr d => i.val∈regionEdges F ConnectedComponents.mk d.val
    | .inr d,.inl i => i.val∈regionEdges F ConnectedComponents.mk d.val
    | _,_ => False
  symm := ⟨by intro a b h; cases a <;> cases b <;> exact h⟩
  loopless := ⟨by intro a; cases a <;> exact id⟩

omit [DecidableEq ι] [Nonempty ι] in
lemma edge_face_unique_two [DecidableEq ι] [Nonempty ι] (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j=>Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (i : ι) {a b c : Faces F} (hab : a≠b)
    (ha : i∈regionEdges F ConnectedComponents.mk a)
    (hb : i∈regionEdges F ConnectedComponents.mk b)
    (hc : i∈regionEdges F ConnectedComponents.mk c) : c=a ∨ c=b := by
  let _ : LocallyConnectedSpace ((⋃i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i=>(F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  let _ : DiscreteTopology (ConnectedComponents ((⋃i,range (F i))ᶜ : Set ℂ)) := inferInstance
  obtain ⟨labels,hlabels⟩ := tame_edge_incident_labels F hF Q hQ ConnectedComponents.continuous_coe i
  have get (d : Faces F) (hd : i∈regionEdges F ConnectedComponents.mk d) : ∃ b,labels b=d := by
    obtain ⟨t,ht₀,ht₁,ht⟩ := hd
    have : d∈incident _ ConnectedComponents.mk (F i t) := ht
    rwa [hlabels t ht₀ ht₁] at this
  obtain ⟨u,hu⟩ := get a ha
  obtain ⟨v,hv⟩ := get b hb
  obtain ⟨w,hw⟩ := get c hc
  cases u <;> cases v <;> cases w <;> simp_all

theorem vertexLink_isCycles (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j=>Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃i,range (F i))\{q}))
    {q : ℂ} (hq : Vertex F q) : (vertexLink F q).IsCycles := by
  classical
  let _ : LocallyConnectedSpace ((⋃i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i=>(F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  let _ : DiscreteTopology (ConnectedComponents ((⋃i,range (F i))ᶜ : Set ℂ)) := inferInstance
  intro x hx
  cases x with
  | inl i =>
    obtain ⟨a,b,hab,ha,hb⟩ := noncut_edge_two_faces F hF Q hQ hK i.val
    let a' : IncidentFaces F q := ⟨a,region_edge_in_closure F hF Q hQ ConnectedComponents.continuous_coe ha i.property⟩
    let b' : IncidentFaces F q := ⟨b,region_edge_in_closure F hF Q hQ ConnectedComponents.continuous_coe hb i.property⟩
    apply Set.ncard_eq_two.mpr
    refine ⟨Sum.inr a',Sum.inr b',?_,?_⟩
    · intro h; exact hab (congrArg Subtype.val (Sum.inr.inj h))
    · ext z
      cases z with
      | inl j => simp [vertexLink]
      | inr d =>
        change (i.val∈regionEdges F ConnectedComponents.mk d.val) ↔ _
        constructor
        · intro hd
          rcases edge_face_unique_two F hF Q hQ i.val hab ha hb hd with h|h
          · exact Or.inl (congrArg Sum.inr (Subtype.ext h))
          · exact Or.inr (congrArg Sum.inr (Subtype.ext h))
        · rintro (h|h)
          · have hd : d=a' := Sum.inr.inj h
            exact hd.symm ▸ ha
          · have hd : d=b' := Sum.inr.inj h
            exact hd.symm ▸ hb
  | inr d =>
    obtain ⟨z,hz⟩ := hx
    cases z with
    | inr c => exact hz.elim
    | inl i =>
      obtain ⟨j,hji,hj,hqj⟩ := noncut_face_second_edge F hF Q hQ hK d.val hq hz i.property
      let j' : IncidentEdges F q := ⟨j,hqj⟩
      apply Set.ncard_eq_two.mpr
      refine ⟨Sum.inl i,Sum.inl j',?_,?_⟩
      · intro h; exact hji (congrArg Subtype.val (Sum.inl.inj h)).symm
      · ext z
        cases z with
        | inr c => simp [vertexLink]
        | inl k =>
          change (k.val∈regionEdges F ConnectedComponents.mk d.val) ↔ _
          constructor
          · intro hk
            rcases face_edge_eq F hF Q hQ hq (hK q) d.val hji.symm hz hj hk i.property hqj k.property with h|h
            · exact Or.inl (congrArg Sum.inl (Subtype.ext h))
            · exact Or.inr (congrArg Sum.inl (Subtype.ext h))
          · rintro (h|h)
            · have hk : k=i := Sum.inl.inj h
              exact hk.symm ▸ hz
            · have hk : k=j' := Sum.inl.inj h
              exact hk.symm ▸ hj

theorem vertexLink_preconnected (F : ι → Arc ℂ)
    (hF : Pairwise (fun i j=>Compatible (F i) (F j)))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃i,range (F i))\{q}))
    {q : ℂ} (hq : Vertex F q) : (vertexLink F q).Preconnected := by
  let _ : LocallyConnectedSpace ((⋃i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i=>(F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  let _ : DiscreteTopology (ConnectedComponents ((⋃i,range (F i))ᶜ : Set ℂ)) := inferInstance
  have hins (a b : IncidentFaces F q) : (vertexLink F q).Reachable (.inr a) (.inr b) := by
    obtain ⟨p⟩ := vertexFaceGraph_preconnected F hF Q hQ hq a b
    induction p with
    | nil => exact .rfl
    | @cons a b c h p ih =>
      obtain ⟨-,i,hi,ha,hb⟩ := h
      exact ((show (vertexLink F q).Adj (.inr a) (.inl ⟨i,hi⟩) from ha).reachable.trans
        (show (vertexLink F q).Adj (.inl ⟨i,hi⟩) (.inr b) from hb).reachable).trans ih
  have hface (x : IncidentEdges F q ⊕ IncidentFaces F q) :
      ∃ a : IncidentFaces F q,(vertexLink F q).Reachable x (.inr a) := by
    cases x with
    | inr a => exact ⟨a,.rfl⟩
    | inl i =>
      obtain ⟨a,b,hab,ha,hb⟩ := noncut_edge_two_faces F hF Q hQ hK i.val
      let a' : IncidentFaces F q := ⟨a,region_edge_in_closure F hF Q hQ ConnectedComponents.continuous_coe ha i.property⟩
      exact ⟨a',(show (vertexLink F q).Adj (.inl i) (.inr a') from ha).reachable⟩
  intro x y
  obtain ⟨a,ha⟩ := hface x
  obtain ⟨b,hb⟩ := hface y
  exact (ha.trans (hins a b)).trans hb.symm
end CannonEmbeddedArc.Arc

end
end
end
end

end OAI

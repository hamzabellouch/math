import Mathlib
import OAI.Geometry.Cannon.PlaneTopology.DevelopedFaces
import OAI.Geometry.Cannon.PlanarGraphs.Steps

namespace OAI

section
section
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonFaceIncidence CannonPackingGeometry

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem DevelopedFaces.vertex_agree (F : ι → Arc ℂ)
    (hF : Pairwise fun i j=>Compatible (F i) (F j))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q}))
    [Fintype (Faces F)] {out : Faces F} (B : DevelopedFaces F out)
    {q : ℂ} (hq : Vertex F q) {d e : Faces F} (hd : d≠out) (he : e≠out)
    (hqd : q∈faceVertices F d) (hqe : q∈faceVertices F e) : B.chart d q=B.chart e q := by
  classical
  obtain ⟨n,hn,edge,a,_hn2,hei,hen⟩ := vertexLink_order F hF Q hQ hK hq
  let nx := CannonCycleOrder.next hn
  let z : Fin n → ℂ := fun i=>B.chart (a i).val q
  have hstep (i : Fin n) (hi : (a i).val≠out) (hj : (a (nx i)).val≠out) : z i=z (nx i) := by
    have h := B.edge_agree (edge (nx i)).val _ _ hi hj (hen i) (hei (nx i))
    obtain ⟨w,hw⟩ := vertex_spans F hF hq (edge (nx i)).property
    rcases hw with ⟨h0,_h1⟩|⟨h1,_h0⟩
    · simpa only [z,h0] using h.1
    · simpa only [z,h1] using h.2
  let i : Fin n := a.symm ⟨d,((mem_faceVertices F _ _).mp hqd).2⟩
  let j : Fin n := a.symm ⟨e,((mem_faceVertices F _ _).mp hqe).2⟩
  have hi : (a i).val=d := by simp [i]
  have hj : (a j).val=e := by simp [j]
  have hzi : z i=B.chart d q := by dsimp only [z]; rw [hi]
  have hzj : z j=B.chart e q := by dsimp only [z]; rw [hj]
  rw [←hzi,←hzj]
  by_cases ho : ∃ o:Fin n,(a o).val=out
  · obtain ⟨o,ho⟩ := ho
    apply CannonCycleOrder.eq_of_steps_except hn z o
    · intro k hko hnko
      apply hstep k
      · intro hk
        exact hko (a.injective (Subtype.ext (hk.trans ho.symm)))
      · intro hk
        exact hnko (a.injective (Subtype.ext (hk.trans ho.symm)))
    · intro hh; exact hd (hi.symm.trans (hh ▸ ho))
    · intro hh; exact he (hj.symm.trans (hh ▸ ho))
  · exact CannonCycleOrder.eq_of_steps hn z (fun k=>hstep k (fun h=>ho ⟨k,h⟩) (fun h=>ho ⟨nx k,h⟩)) i j

theorem DevelopedFaces.global_centers (F : ι → Arc ℂ)
    (hF : Pairwise fun i j=>Compatible (F i) (F j))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q}))
    [Fintype (Faces F)] {out : Faces F} (B : DevelopedFaces F out) :
    ∃ z : ℂ → ℂ,∀ d,d≠out → ∀ q∈faceVertices F d,z q=B.chart d q := by
  classical
  let _ : LocallyConnectedSpace ((⋃ i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i=>(F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  let _ : DiscreteTopology (ConnectedComponents ((⋃ i,range (F i))ᶜ : Set ℂ)) := inferInstance
  have incident (v : GraphVertices F) : ∃ d:Faces F,d≠out ∧ v.val∈faceVertices F d := by
    obtain ⟨i,hi⟩ := v.property
    have hv : v.val∈range (F i) := hi.elim (fun h=>h ▸ ⟨0,rfl⟩) (fun h=>h ▸ ⟨1,rfl⟩)
    obtain ⟨a,b,hab,ha,hb⟩ := noncut_edge_two_faces F hF Q hQ hK i
    have mem (d : Faces F) (hd : i∈regionEdges F ConnectedComponents.mk d) : v.val∈faceVertices F d :=
      (mem_faceVertices F _ _).mpr ⟨v.property,region_edge_in_closure F hF Q hQ ConnectedComponents.continuous_coe hd hv⟩
    by_cases hao : a=out
    · exact ⟨b,fun h=>hab (hao.trans h.symm),mem b hb⟩
    · exact ⟨a,hao,mem a ha⟩
  choose d hd hmem using incident
  let z : ℂ → ℂ := fun q=>if h:Vertex F q then B.chart (d ⟨q,h⟩) q else 0
  refine ⟨z,fun e he q hq=>?_⟩
  have hqv := ((mem_faceVertices F _ _).mp hq).1
  dsimp only [z]
  rw [dite_eq_left hqv]
  exact B.vertex_agree F hF Q hQ hK hqv (hd _) he (hmem _) hq
end CannonEmbeddedArc.Arc

end
end
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonFaceIncidence CannonPackingGeometry

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] [Nonempty ι] in
theorem triangular_face_cycle (F : ι → Arc ℂ)
    (hF : Pairwise fun i j=>Compatible (F i) (F j))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q}))
    (d : Faces F) (hthree : (faceVertices F d).card=3) :
    ∃ x y z : ℂ, ∃ i j k : ι,
      x≠y ∧ x≠z ∧ y≠z ∧ faceVertices F d={x,y,z} ∧
      i∈regionEdges F ConnectedComponents.mk d ∧
      j∈regionEdges F ConnectedComponents.mk d ∧
      k∈regionEdges F ConnectedComponents.mk d ∧
      Spans (F i) x y ∧ Spans (F j) y z ∧ Spans (F k) z x := by
  classical
  let _ : LocallyConnectedSpace ((⋃i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i=>(F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  let _ : DiscreteTopology (ConnectedComponents ((⋃i,range (F i))ᶜ : Set ℂ)) := inferInstance
  let S : Set (GraphVertices F) := {x | x.val∈faceVertices F d}
  have hE : (regionEdges F ConnectedComponents.mk d).Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero
    have hn := noncut_facial_vertices_edges F hF Q hQ hK d
    rw [hthree] at hn
    change Nat.card (regionEdges F ConnectedComponents.mk d)≠0
    omega
  obtain ⟨i,hi⟩ := hE
  let x : GraphVertices F := ⟨F i 0,⟨i,Or.inl rfl⟩⟩
  let y : GraphVertices F := ⟨F i 1,⟨i,Or.inr rfl⟩⟩
  have hixy : Spans (F i) x.val y.val := Or.inl ⟨rfl,rfl⟩
  obtain ⟨j,hji,hj,hxj⟩ := noncut_face_second_edge F hF Q hQ hK d x.property hi hixy.mem_left
  obtain ⟨z₀,hjxz⟩ := vertex_spans F hF x.property hxj
  let z : GraphVertices F := ⟨z₀,hjxz.vertex_right⟩
  have hxy : x≠y := fun h=>hixy.ne (congrArg Subtype.val h)
  have hxz : x≠z := fun h=>hjxz.ne (congrArg Subtype.val h)
  have hyz : y≠z := by
    intro h
    exact hji (spans_edge_unique F hF (show Spans (F j) x.val y.val from
      (congrArg Subtype.val h).symm ▸ hjxz) hixy)
  have memS {a:ι} (ha:a∈regionEdges F ConnectedComponents.mk d) {v:GraphVertices F}
      (hv:v.val∈range (F a)) : v∈S :=
    (mem_faceVertices F d v.val).mpr ⟨v.property,region_edge_in_closure F hF Q hQ
      ConnectedComponents.continuous_coe ha hv⟩
  have hxS : x∈S := memS hi hixy.mem_left
  have hyS : y∈S := memS hi hixy.mem_right
  have hzS : z∈S := memS hj hjxz.mem_right
  have hfin : faceVertices F d={x.val,y.val,z.val} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro v hv
      simp only [Finset.mem_insert,Finset.mem_singleton] at hv
      rcases hv with rfl|rfl|rfl <;> assumption
    · rw [hthree]
      have hxy' : x.val≠y.val := fun h=>hxy (Subtype.ext h)
      have hxz' : x.val≠z.val := fun h=>hxz (Subtype.ext h)
      have hyz' : y.val≠z.val := fun h=>hyz (Subtype.ext h)
      simp [hxy',hxz',hyz']
  obtain ⟨k,hki,hk,hyk⟩ := noncut_face_second_edge F hF Q hQ hK d y.property hi hixy.mem_right
  obtain ⟨w,hkyw⟩ := vertex_spans F hF y.property hyk
  have hw : w∈faceVertices F d := memS hk (v:=⟨w,hkyw.vertex_right⟩) hkyw.mem_right
  have hwy : w≠y.val := hkyw.ne.symm
  have hwx : w≠x.val := by
    intro he
    subst w
    exact hki (spans_edge_unique F hF hkyw hixy.symm)
  have hwz : w=z.val := by
    rw [hfin] at hw
    simp only [Finset.mem_insert,Finset.mem_singleton] at hw
    exact hw.elim (fun h=>(hwx h).elim) (fun h=>h.elim (fun h=>(hwy h).elim) id)
  refine ⟨x.val,y.val,z.val,i,k,j,hixy.ne,hjxz.ne,?_,hfin,hi,hk,hj,hixy,?_,hjxz.symm⟩
  · exact fun he=>hyz (Subtype.ext he)
  · exact hwz ▸ hkyw

end CannonEmbeddedArc.Arc

end
end
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonFaceIncidence CannonPackingGeometry

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem DevelopedFaces.global_metric_centers (F : ι → Arc ℂ)
    (hF : Pairwise fun i j=>Compatible (F i) (F j))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q}))
    [Fintype (Faces F)] {out : Faces F} (B : DevelopedFaces F out) :
    ∃ z : ℂ → ℂ,
      (∀ d,d≠out → ∀ q∈faceVertices F d,z q=B.chart d q) ∧
      (∀ i,dist (z (F i 0)) (z (F i 1))=B.radius (F i 0)+B.radius (F i 1)) ∧
      (∀ d,d≠out → ∀ u∈faceVertices F d,∀ v∈faceVertices F d,∀ w∈faceVertices F d,
        u≠v → u≠w → v≠w → orientedArea (z u) (z v) (z w)≠0) ∧
      (∀ i d e,d≠e → d≠out → e≠out →
        i∈regionEdges F ConnectedComponents.mk d → i∈regionEdges F ConnectedComponents.mk e →
        ∀ u∈faceVertices F d,u≠F i 0 → u≠F i 1 →
        ∀ v∈faceVertices F e,v≠F i 0 → v≠F i 1 →
        orientedArea (z (F i 0)) (z (F i 1)) (z u)*
          orientedArea (z (F i 0)) (z (F i 1)) (z v)<0) := by
  classical
  let _ : LocallyConnectedSpace ((⋃ i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i=>(F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  let _ : DiscreteTopology (ConnectedComponents ((⋃ i,range (F i))ᶜ : Set ℂ)) := inferInstance
  obtain ⟨z,hz⟩ := B.global_centers F hF Q hQ hK
  have ends (i : ι) (d : Faces F) (hi : i∈regionEdges F ConnectedComponents.mk d) :
      F i 0∈faceVertices F d ∧ F i 1∈faceVertices F d := by
    exact ⟨(mem_faceVertices F _ _).mpr ⟨⟨i,Or.inl rfl⟩,
      region_edge_in_closure F hF Q hQ ConnectedComponents.continuous_coe hi ⟨0,rfl⟩⟩,
      (mem_faceVertices F _ _).mpr ⟨⟨i,Or.inr rfl⟩,
      region_edge_in_closure F hF Q hQ ConnectedComponents.continuous_coe hi ⟨1,rfl⟩⟩⟩
  have len (d : Faces F) (hd : d≠out) {u v : ℂ}
      (hu : u∈faceVertices F d) (hv : v∈faceVertices F d) (huv : u≠v) :
      dist (z u) (z v)=B.radius u+B.radius v := by
    rw [hz d hd u hu,hz d hd v hv]
    exact B.lengths d u hu v hv huv
  refine ⟨z,hz,?_,?_,?_⟩
  · intro i
    obtain ⟨d,e,hde,hd,he⟩ := noncut_edge_two_faces F hF Q hQ hK i
    by_cases hdo : d=out
    · exact len e (fun h=>hde (hdo.trans h.symm)) (ends i e he).1 (ends i e he).2 (F i).endpoints_ne
    · exact len d hdo (ends i d hd).1 (ends i d hd).2 (F i).endpoints_ne
  · intro d hd u hu v hv w hw huv huw hvw
    apply orientedArea_ne_zero_of_strict
    all_goals rw [len d hd hu hv huv,len d hd hu hw huw,len d hd hv hw hvw]
    all_goals linarith [B.radius_pos u,B.radius_pos v,B.radius_pos w]
  · intro i d e hde hd he hid hie u hu hu0 hu1 v hv hv0 hv1
    have H := B.opposite i d e hde hd he hid hie u hu hu0 hu1 v hv hv0 hv1
    rw [←hz e he _ (ends i e hie).1,←hz e he _ (ends i e hie).2,
      ←hz d hd u hu,←hz e he v hv] at H
    exact H
end CannonEmbeddedArc.Arc

end
end
section
noncomputable section
namespace CannonTriangleWinding
open Set

attribute [local instance] Classical.propDecidable

def crossing (y z A : ℝ) : ℤ :=
  if y<0 ∧ 0<z ∧ 0<A then 1 else if z<0 ∧ 0<y ∧ A<0 then -1 else 0

lemma crossing_neg (y z A : ℝ) : crossing z y (-A)= -crossing y z A := by
  unfold crossing
  simp only [neg_pos,neg_lt_zero]
  have hdis : ¬((y<0 ∧ 0<z ∧ 0<A) ∧ (z<0 ∧ 0<y ∧ A<0)) := by
    rintro ⟨h,k⟩
    exact lt_asymm h.1 k.2.1
  by_cases h : y<0 ∧ 0<z ∧ 0<A
  · have k : ¬(z<0 ∧ 0<y ∧ A<0) := fun k=>hdis ⟨h,k⟩
    simp only [ite_eq_left h,ite_eq_right k]
  · by_cases k : z<0 ∧ 0<y ∧ A<0 <;> simp only [h,k,and_self,ite_false,ite_true,neg_zero,neg_neg]

lemma positive_triangle_degree {y z w A B C : ℝ}
    (hy : y≠0) (hz : z≠0) (hw : w≠0) (hA : A≠0) (hB : B≠0) (hC : C≠0)
    (hp : 0<A+B+C) (hr : y*B+z*C+w*A=0) :
    crossing y z A+crossing z w B+crossing w y C=
      if 0<A ∧ 0<B ∧ 0<C then 1 else 0 := by
  rcases lt_or_gt_of_ne hy with hy|hy <;>
    rcases lt_or_gt_of_ne hz with hz|hz <;>
    rcases lt_or_gt_of_ne hw with hw|hw <;>
    rcases lt_or_gt_of_ne hA with hA|hA <;>
    rcases lt_or_gt_of_ne hB with hB|hB <;>
    rcases lt_or_gt_of_ne hC with hC|hC <;>
    (have hy' := lt_asymm hy
     have hz' := lt_asymm hz
     have hw' := lt_asymm hw
     have hA' := lt_asymm hA
     have hB' := lt_asymm hB
     have hC' := lt_asymm hC
     simp only [crossing,hy,hz,hw,hA,hB,hC,hy',hz',hw',hA',hB',hC',
       and_self,and_true,and_false,ite_true,ite_false]
     norm_num)
  all_goals
    first
    | have h1 := mul_pos hy hB
    | have h1 := mul_pos_of_neg_of_neg hy hB
    | have h1 := mul_neg_of_neg_of_pos hy hB
    | have h1 := mul_neg_of_pos_of_neg hy hB
    first
    | have h2 := mul_pos hz hC
    | have h2 := mul_pos_of_neg_of_neg hz hC
    | have h2 := mul_neg_of_neg_of_pos hz hC
    | have h2 := mul_neg_of_pos_of_neg hz hC
    first
    | have h3 := mul_pos hw hA
    | have h3 := mul_pos_of_neg_of_neg hw hA
    | have h3 := mul_neg_of_neg_of_pos hw hA
    | have h3 := mul_neg_of_pos_of_neg hw hA
    linarith

def area (a b c : ℂ) : ℝ :=
  (b.re-a.re)*(c.im-a.im)-(b.im-a.im)*(c.re-a.re)

lemma area_swap (a b p : ℂ) : area b a p= -area a b p := by
  unfold area
  ring
lemma area_cyclic (a b c : ℂ) : area b c a=area a b c := by
  unfold area
  ring
lemma area_sum (a b c p : ℂ) : area a b p+area b c p+area c a p=area a b c := by
  unfold area
  ring
lemma area_relation (a b c p : ℂ) :
    (a.im-p.im)*area b c p+(b.im-p.im)*area c a p+(c.im-p.im)*area a b p=0 := by
  unfold area
  ring

def edgeIndex (p a b : ℂ) : ℤ := crossing (a.im-p.im) (b.im-p.im) (area a b p)
lemma edgeIndex_swap (p a b : ℂ) : edgeIndex p b a= -edgeIndex p a b := by
  unfold edgeIndex
  rw [area_swap,crossing_neg]

def Inside (a b c p : ℂ) : Prop := 0<area a b p ∧ 0<area b c p ∧ 0<area c a p

def Generic (a b c p : ℂ) : Prop :=
  a.im≠p.im ∧ b.im≠p.im ∧ c.im≠p.im ∧ area a b p≠0 ∧ area b c p≠0 ∧ area c a p≠0

lemma triangle_index {a b c p : ℂ} (harea : 0<area a b c) (hgen : Generic a b c p) :
    edgeIndex p a b+edgeIndex p b c+edgeIndex p c a=if Inside a b c p then 1 else 0 := by
  have ht := positive_triangle_degree (sub_ne_zero.mpr hgen.1) (sub_ne_zero.mpr hgen.2.1)
    (sub_ne_zero.mpr hgen.2.2.1) hgen.2.2.2.1 hgen.2.2.2.2.1 hgen.2.2.2.2.2
    (by rw [area_sum]; exact harea) (area_relation a b c p)
  by_cases h : Inside a b c p
  · rw [ite_eq_left h]
    change 0<area a b p ∧ 0<area b c p ∧ 0<area c a p at h
    rw [ite_eq_left h] at ht
    exact ht
  · rw [ite_eq_right h]
    change ¬(0<area a b p ∧ 0<area b c p ∧ 0<area c a p) at h
    rw [ite_eq_right h] at ht
    exact ht

lemma inside_open (a b c : ℂ) : IsOpen {p | Inside a b c p} := by
  have H (a b : ℂ) : Continuous (area a b) := by unfold area; fun_prop
  exact (isOpen_lt continuous_const (H a b)).inter
    ((isOpen_lt continuous_const (H b c)).inter (isOpen_lt continuous_const (H c a)))

theorem generic_unique {D : Type*} [Fintype D] (a b c : D → ℂ) (u v w p : ℂ)
    (hpos : ∀ d,0<area (a d) (b d) (c d)) (ho : 0<area u v w)
    (hgen : ∀ d,Generic (a d) (b d) (c d) p) (hgo : Generic u v w p)
    (hchain : ∀ f : ℂ → ℂ → ℤ,(∀ x y,f y x= -f x y) →
      (∑ d : D,(f (a d) (b d)+f (b d) (c d)+f (c d) (a d)))=f u v+f v w+f w u)
    {d e : D} (hd : Inside (a d) (b d) (c d) p) (he : Inside (a e) (b e) (c e) p) : d=e := by
  classical
  have ht := hchain (edgeIndex p) (edgeIndex_swap p)
  simp only [triangle_index (hpos _) (hgen _),triangle_index ho hgo] at ht
  by_contra hde
  have hb : (2:ℤ)≤∑ i,if Inside (a i) (b i) (c i) p then (1:ℤ) else 0 := by
    calc
      (2:ℤ)=∑ i∈({d,e}:Finset D),if Inside (a i) (b i) (c i) p then (1:ℤ) else 0 := by
        rw [Finset.sum_pair hde]
        simp only [hd,he,ite_true]
        norm_num
      _ ≤ ∑ i,if Inside (a i) (b i) (c i) p then (1:ℤ) else 0 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intro i hi hi'
        split_ifs <;> norm_num
  rw [ht] at hb
  split_ifs at hb <;> norm_num at hb

end CannonTriangleWinding

end
end
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonFaceIncidence CannonPackingGeometry

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

structure FacialCycle (F : ι → Arc ℂ) (d : Faces F) where
  a : ℂ
  b : ℂ
  c : ℂ
  e : ι
  f : ι
  g : ι
  ab : a≠b
  ac : a≠c
  bc : b≠c
  vertices : faceVertices F d={a,b,c}
  mem_e : e∈regionEdges F ConnectedComponents.mk d
  mem_f : f∈regionEdges F ConnectedComponents.mk d
  mem_g : g∈regionEdges F ConnectedComponents.mk d
  spans_e : Spans (F e) a b
  spans_f : Spans (F f) b c
  spans_g : Spans (F g) c a

omit [DecidableEq ι] [Nonempty ι] in
lemma facialCycle_exists (F : ι → Arc ℂ)
    (hF : Pairwise fun i j=>Compatible (F i) (F j))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q}))
    (d : Faces F) (hthree : (faceVertices F d).card=3) : Nonempty (FacialCycle F d) := by
  obtain ⟨a,b,c,e,f,g,hab,hac,hbc,hV,he,hf,hg,hse,hsf,hsg⟩ := triangular_face_cycle F hF Q hQ hK d hthree
  exact ⟨⟨a,b,c,e,f,g,hab,hac,hbc,hV,he,hf,hg,hse,hsf,hsg⟩⟩

variable {F : ι → Arc ℂ} {d : Faces F}

def FacialCycle.reverse (C : FacialCycle F d) : FacialCycle F d where
  a := C.a
  b := C.c
  c := C.b
  e := C.g
  f := C.f
  g := C.e
  ab := C.ac
  ac := C.ab
  bc := C.bc.symm
  vertices := by
    classical
    rw [C.vertices,Finset.pair_comm C.b C.c]
  mem_e := C.mem_g
  mem_f := C.mem_f
  mem_g := C.mem_e
  spans_e := C.spans_g.symm
  spans_f := C.spans_f.symm
  spans_g := C.spans_e.symm

omit [DecidableEq ι] [Nonempty ι] in
lemma FacialCycle.mem_a (C : FacialCycle F d) : C.a∈faceVertices F d := by rw [C.vertices]; simp
omit [DecidableEq ι] [Nonempty ι] in
lemma FacialCycle.mem_b (C : FacialCycle F d) : C.b∈faceVertices F d := by rw [C.vertices]; simp
omit [DecidableEq ι] [Nonempty ι] in
lemma FacialCycle.mem_c (C : FacialCycle F d) : C.c∈faceVertices F d := by rw [C.vertices]; simp

omit [DecidableEq ι] [Nonempty ι] in
lemma FacialCycle.edge_ne (C : FacialCycle F d) : C.e≠C.f ∧ C.e≠C.g ∧ C.f≠C.g := by
  have H := C.spans_e
  constructor
  · intro he
    rw [he] at H
    exact C.ac (H.symm.other_unique C.spans_f)
  constructor
  · intro he
    rw [he] at H
    exact C.bc (H.other_unique C.spans_g.symm)
  · intro he
    have H' := C.spans_f
    rw [he] at H'
    exact C.ab (C.spans_g.other_unique H'.symm)

omit [DecidableEq ι] [Nonempty ι] in
lemma FacialCycle.edges (C : FacialCycle F d)
    (hF : Pairwise fun i j=>Compatible (F i) (F j))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q})) :
    regionEdges F ConnectedComponents.mk d={C.e,C.f,C.g} := by
  classical
  symm
  apply Set.eq_of_subset_of_ncard_le
  · intro i hi
    rcases hi with rfl|rfl|rfl
    · exact C.mem_e
    · exact C.mem_f
    · exact C.mem_g
  · have hcard := noncut_facial_vertices_edges F hF Q hQ hK d
    have hv : (faceVertices F d).card=3 := by rw [C.vertices]; simp [C.ab,C.ac,C.bc]
    rw [hv] at hcard
    change Nat.card (regionEdges F ConnectedComponents.mk d)≤_
    rw [←hcard]
    simp [C.edge_ne.1,C.edge_ne.2.1,C.edge_ne.2.2]
  · exact Set.toFinite _

lemma area_eq_orientedArea (a b c : ℂ) : CannonTriangleWinding.area a b c=orientedArea a b c := by
  simp only [CannonTriangleWinding.area,orientedArea,Complex.mul_im,Complex.conj_re,
    Complex.sub_re,Complex.conj_im,Complex.sub_im]
  ring

omit [DecidableEq ι] [Nonempty ι] in
lemma FacialCycle.orient (C : FacialCycle F d) (z : ℂ → ℂ)
    (hne : orientedArea (z C.a) (z C.b) (z C.c)≠0) :
    ∃ C' : FacialCycle F d,0<CannonTriangleWinding.area (z C'.a) (z C'.b) (z C'.c) := by
  rw [←area_eq_orientedArea] at hne
  by_cases hp : 0<CannonTriangleWinding.area (z C.a) (z C.b) (z C.c)
  · exact ⟨C,hp⟩
  · refine ⟨C.reverse,?_⟩
    change 0<CannonTriangleWinding.area (z C.a) (z C.c) (z C.b)
    rw [area_eq_orientedArea,←neg_neg (orientedArea (z C.a) (z C.c) (z C.b)),←orientedArea_swap,
      ←area_eq_orientedArea]
    exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hp) hne)

end CannonEmbeddedArc.Arc

end
end
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonFaceIncidence CannonPackingGeometry

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {F : ι → Arc ℂ} {d : Faces F}

def FacialCycle.flux {R : Type*} [Zero R] (C : FacialCycle F d) (f : ℂ → ℂ → R) (i : ι) : R :=
  if i=C.e then f C.a C.b else if i=C.f then f C.b C.c else if i=C.g then f C.c C.a else 0

omit [Nonempty ι] in
lemma FacialCycle.sum_flux {R : Type*} [AddCommMonoid R] (C : FacialCycle F d) (f : ℂ → ℂ → R) :
    ∑ i,C.flux f i=f C.a C.b+f C.b C.c+f C.c C.a := by
  classical
  have heq (i : ι) : C.flux f i=(if i=C.e then f C.a C.b else 0)+
      (if i=C.f then f C.b C.c else 0)+(if i=C.g then f C.c C.a else 0) := by
    by_cases he : i=C.e
    · subst i; simp [flux,C.edge_ne.1,C.edge_ne.2.1]
    by_cases hf : i=C.f
    · subst i; simp [flux,he,C.edge_ne.2.2]
    by_cases hg : i=C.g
    · subst i; simp [flux,he,hf]
    · simp [flux,he,hf,hg]
  simp only [heq,Finset.sum_add_distrib]
  simp

omit [Nonempty ι] in
lemma FacialCycle.flux_nonmem {R : Type*} [Zero R] (C : FacialCycle F d) (f : ℂ → ℂ → R)
    {i : ι} (hi : i∉regionEdges F ConnectedComponents.mk d) : C.flux f i=0 := by
  have he : i≠C.e := fun h=>hi (h ▸ C.mem_e)
  have hf : i≠C.f := fun h=>hi (h ▸ C.mem_f)
  have hg : i≠C.g := fun h=>hi (h ▸ C.mem_g)
  simp [flux,he,hf,hg]

omit [Nonempty ι] in
lemma FacialCycle.edge_data (C : FacialCycle F d)
    (hF : Pairwise fun i j=>Compatible (F i) (F j))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q})) (z : ℂ → ℂ)
    (hp : 0<CannonTriangleWinding.area (z C.a) (z C.b) (z C.c))
    {i : ι} (hi : i∈regionEdges F ConnectedComponents.mk d) :
    ∃ a b c : ℂ, Spans (F i) a b ∧ c∈faceVertices F d ∧ c≠a ∧ c≠b ∧
      0<CannonTriangleWinding.area (z a) (z b) (z c) ∧
      ∀ (R : Type*) [Zero R] (f : ℂ → ℂ → R),C.flux f i=f a b := by
  rw [C.edges hF Q hQ hK] at hi
  rcases hi with rfl|rfl|rfl
  · refine ⟨C.a,C.b,C.c,C.spans_e,C.mem_c,C.ac.symm,C.bc.symm,hp,?_⟩
    intro R inst f; simp [flux]
  · refine ⟨C.b,C.c,C.a,C.spans_f,C.mem_a,C.ab,C.ac,?_,?_⟩
    · rwa [CannonTriangleWinding.area_cyclic]
    · intro R inst f; simp [flux,C.edge_ne.1.symm]
  · refine ⟨C.c,C.a,C.b,C.spans_g,C.mem_b,C.bc,C.ab.symm,?_,?_⟩
    · rwa [CannonTriangleWinding.area_cyclic,CannonTriangleWinding.area_cyclic]
    · intro R inst f; simp [flux,C.edge_ne.2.1.symm,C.edge_ne.2.2.symm]

lemma folded_side_reversed {a : Arc ℂ} {u v w x y t : ℂ} (z : ℂ → ℂ)
    (h1 : Spans a u v) (h2 : Spans a x y)
    (hp : 0<CannonTriangleWinding.area (z u) (z v) (z w))
    (hq : 0<CannonTriangleWinding.area (z x) (z y) (z t))
    (hop : orientedArea (z (a 0)) (z (a 1)) (z w)*orientedArea (z (a 0)) (z (a 1)) (z t)<0) :
    x=v ∧ y=u := by
  simp only [←area_eq_orientedArea] at hop
  rcases h1 with h1|h1 <;> rcases h2 with h2|h2
  · have hx : x=u := h2.1.symm.trans h1.1
    have hy : y=v := h2.2.symm.trans h1.2
    rw [h1.1,h1.2] at hop
    rw [hx,hy] at hq
    exact (not_lt_of_gt (mul_pos hp hq) hop).elim
  · exact ⟨h2.1.symm.trans h1.2,h2.2.symm.trans h1.1⟩
  · exact ⟨h2.1.symm.trans h1.2,h2.2.symm.trans h1.1⟩
  · have hx : x=u := h2.1.symm.trans h1.1
    have hy : y=v := h2.2.symm.trans h1.2
    rw [h1.2,h1.1,CannonTriangleWinding.area_swap (z u) (z v) (z w),
      CannonTriangleWinding.area_swap (z u) (z v) (z t),neg_mul_neg] at hop
    rw [hx,hy] at hq
    exact (not_lt_of_gt (mul_pos hp hq) hop).elim

omit [Nonempty ι] in
lemma FacialCycle.flux_cancel {R : Type*} [AddCommGroup R]
    (hF : Pairwise fun i j=>Compatible (F i) (F j))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q}))
    {e : Faces F} (C : FacialCycle F d) (E : FacialCycle F e)
    (z : ℂ → ℂ) (hC : 0<CannonTriangleWinding.area (z C.a) (z C.b) (z C.c))
    (hE : 0<CannonTriangleWinding.area (z E.a) (z E.b) (z E.c))
    (f : ℂ → ℂ → R) (hf : ∀ x y,f y x= -f x y) {i : ι}
    (hi : i∈regionEdges F ConnectedComponents.mk d) (hj : i∈regionEdges F ConnectedComponents.mk e)
    (hop : ∀ u∈faceVertices F d,u≠F i 0 → u≠F i 1 →
      ∀ v∈faceVertices F e,v≠F i 0 → v≠F i 1 →
      orientedArea (z (F i 0)) (z (F i 1)) (z u)*
        orientedArea (z (F i 0)) (z (F i 1)) (z v)<0) : C.flux f i+E.flux f i=0 := by
  obtain ⟨a,b,c,hsp,hc,hca,hcb,hp,hval⟩ := C.edge_data hF Q hQ hK z hC hi
  obtain ⟨u,v,w,hsp',hw,hwu,hwv,hp',hval'⟩ := E.edge_data hF Q hQ hK z hE hj
  have avoid {q a b:ℂ} (hsp:Spans (F i) a b) (ha:q≠a) (hb:q≠b) : q≠F i 0 ∧ q≠F i 1 := by
    rcases hsp with h|h
    · simpa only [h.1,h.2] using And.intro ha hb
    · simpa only [h.1,h.2] using And.intro hb ha
  have hd := folded_side_reversed z hsp hsp' hp hp'
    (hop c hc (avoid hsp hca hcb).1 (avoid hsp hca hcb).2
      w hw (avoid hsp' hwu hwv).1 (avoid hsp' hwu hwv).2)
  rw [hval R f,hval' R f,hd.1,hd.2,hf a b,add_neg_cancel]

end CannonEmbeddedArc.Arc

end
end
end
end

end OAI

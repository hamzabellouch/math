import Mathlib
import OAI.Geometry.Cannon.PlaneTopology.InteriorBallCover
import OAI.Geometry.Cannon.PlaneTopology.BoundaryBallCover
import OAI.Geometry.Cannon.PlaneTopology.CompactifiedFace
import OAI.Geometry.Cannon.Conformal.Sphere

namespace OAI

section
section
section
noncomputable section
namespace CannonTriangleWinding
open Set Metric Topology

lemma area_combo (a b x y : ℂ) (s t : ℝ) (hst : s+t=1) :
    area a b (s • x+t • y)=s*area a b x+t*area a b y := by
  have ht : t=1-s := by linarith
  subst t
  simp only [area,Complex.add_re,Complex.add_im,Complex.smul_re,Complex.smul_im,smul_eq_mul]
  ring

def ClosedInside (a b c p : ℂ) : Prop := 0≤area a b p ∧ 0≤area b c p ∧ 0≤area c a p
lemma closedInside_convex (a b c : ℂ) : Convex ℝ {p | ClosedInside a b c p} := by
  intro x hx y hy s t hs ht hst
  change 0≤area a b (s • x+t • y) ∧ 0≤area b c (s • x+t • y) ∧ 0≤area c a (s • x+t • y)
  rw [area_combo _ _ _ _ _ _ hst,area_combo _ _ _ _ _ _ hst,area_combo _ _ _ _ _ _ hst]
  exact ⟨add_nonneg (mul_nonneg hs hx.1) (mul_nonneg ht hy.1),
    add_nonneg (mul_nonneg hs hx.2.1) (mul_nonneg ht hy.2.1),
    add_nonneg (mul_nonneg hs hx.2.2) (mul_nonneg ht hy.2.2)⟩
lemma area_barycentric (a b c p : ℂ) (h : area a b c≠0) :
    (area b c p/area a b c) • a+(area c a p/area a b c) • b+(area a b p/area a b c) • c=p := by
  apply Complex.ext <;> simp only [Complex.add_re,Complex.add_im,Complex.smul_re,Complex.smul_im,smul_eq_mul]
  · field_simp
    simp only [area]
    ring
  · field_simp
    simp only [area]
    ring

lemma convexHull_eq_closedInside {a b c : ℂ} (h : 0<area a b c) :
    convexHull ℝ ({a,b,c}:Set ℂ)={p | ClosedInside a b c p} := by
  apply Subset.antisymm
  · apply convexHull_min _ (closedInside_convex a b c)
    have az (x y : ℂ) : area x y x=0 := by simp [area]
    have bz (x y : ℂ) : area x y y=0 := by unfold area; ring
    have ha : ClosedInside a b c a := ⟨by rw [az],by rw [area_cyclic]; exact h.le,by rw [bz]⟩
    have hb : ClosedInside a b c b := ⟨by rw [bz],by rw [az],by rw [area_cyclic,area_cyclic]; exact h.le⟩
    have hc : ClosedInside a b c c := ⟨h.le,by rw [bz],by rw [az]⟩
    rintro p (rfl|rfl|rfl) <;> assumption
  · intro p hp
    let w : Fin 3 → ℝ := ![area b c p/area a b c,area c a p/area a b c,area a b p/area a b c]
    let v : Fin 3 → ℂ := ![a,b,c]
    apply mem_convexHull_of_exists_fintype w v
    · intro i
      fin_cases i
      · exact div_nonneg hp.2.1 h.le
      · exact div_nonneg hp.2.2 h.le
      · exact div_nonneg hp.1 h.le
    · simp only [w,Fin.sum_univ_three]
      change area b c p/area a b c+area c a p/area a b c+area a b p/area a b c=1
      rw [←add_div,←add_div]
      have hs := area_sum a b c p
      convert div_self h.ne' using 1
      congr 1
      linarith
    · intro i
      fin_cases i <;> simp [v]
    · simp only [w,v,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
      exact area_barycentric a b c p h.ne'

lemma convexHull_interior_nonempty {a b c : ℂ} (h : 0<area a b c) :
    (interior (convexHull ℝ ({a,b,c}:Set ℂ))).Nonempty := by
  have hsub : {p | Inside a b c p}⊆convexHull ℝ ({a,b,c}:Set ℂ) := by
    rw [convexHull_eq_closedInside h]
    exact fun p hp=>⟨hp.1.le,hp.2.1.le,hp.2.2.le⟩
  have hmean (x y z : ℂ) : area x y ((3:ℝ)⁻¹ • (x+y+z))=area x y z/3 := by
    simp only [area,Complex.add_re,Complex.add_im,Complex.smul_re,Complex.smul_im,smul_eq_mul]
    ring
  have hcent : Inside a b c ((3:ℝ)⁻¹ • (a+b+c)) := by
    constructor
    · rw [hmean]; positivity
    constructor
    · have he : a+b+c=b+c+a := by ring
      rw [he,hmean,area_cyclic]
      positivity
    · have he : a+b+c=c+a+b := by ring
      rw [he,hmean,area_cyclic,area_cyclic]
      positivity
  exact ⟨_,(interior_mono hsub) (by rw [(inside_open a b c).interior_eq]; exact hcent)⟩

lemma area_isOpenMap {a b c : ℂ} (h : 0<area a b c) : IsOpenMap (area a b) := by
  let L : ℂ →L[ℝ] ℝ := (b.re-a.re) • Complex.imCLM-(b.im-a.im) • Complex.reCLM
  have hL : Function.Surjective L := by
    intro y
    refine ⟨(y / area a b c) • (c-a),?_⟩
    rw [map_smul]
    have he : L (c-a)=area a b c := by simp [L,area]
    rw [he,smul_eq_mul,div_mul_cancel₀ _ h.ne']
  have he : area a b=fun p=>L (p-a) := by
    funext p
    simp [L,area]
  rw [he]
  exact (L.isOpenMap hL).comp (Homeomorph.subRight a).isOpenMap

lemma area_continuous (a b : ℂ) : Continuous (area a b) := by
  unfold area
  fun_prop

lemma convexHull_interior {a b c : ℂ} (h : 0<area a b c) :
    interior (convexHull ℝ ({a,b,c}:Set ℂ))={p | Inside a b c p} := by
  have h1 := (area_isOpenMap h).preimage_interior_eq_interior_preimage (area_continuous a b) (Ici 0)
  have hb : 0<area b c a := by simpa only [area_cyclic] using h
  have hc : 0<area c a b := by simpa only [area_cyclic] using h
  have h2 := (area_isOpenMap hb).preimage_interior_eq_interior_preimage (area_continuous b c) (Ici 0)
  have h3 := (area_isOpenMap hc).preimage_interior_eq_interior_preimage (area_continuous c a) (Ici 0)
  rw [interior_Ici] at h1 h2 h3
  rw [convexHull_eq_closedInside h]
  change interior ((area a b ⁻¹' Ici 0)∩((area b c ⁻¹' Ici 0)∩(area c a ⁻¹' Ici 0)))=_
  rw [interior_inter,interior_inter,←h1,←h2,←h3]
  ext p
  simp only [mem_inter_iff,mem_preimage,mem_Ioi,mem_ofPred_eq,Inside]

lemma convexHull_closure_inside {a b c : ℂ} (h : 0<area a b c) :
    closure {p | Inside a b c p}=convexHull ℝ ({a,b,c}:Set ℂ) := by
  rw [←convexHull_interior h]
  rw [(convex_convexHull ℝ _).closure_interior_eq_closure_of_nonempty_interior (convexHull_interior_nonempty h)]
  have hc : IsClosed (convexHull ℝ ({a,b,c}:Set ℂ)) := by
    rw [convexHull_eq_closedInside h]
    exact (isClosed_le continuous_const (area_continuous a b)).inter
      ((isClosed_le continuous_const (area_continuous b c)).inter
        (isClosed_le continuous_const (area_continuous c a)))
  exact hc.closure_eq

lemma segment_subset_frontier {a b c : ℂ} (h : 0<area a b c) :
    segment ℝ a b⊆frontier (convexHull ℝ ({a,b,c}:Set ℂ)) := by
  intro p hp
  change p∈closure (convexHull ℝ ({a,b,c}:Set ℂ)) ∧ p∉interior (convexHull ℝ ({a,b,c}:Set ℂ))
  refine ⟨subset_closure ((convex_convexHull ℝ ({a,b,c}:Set ℂ)).segment_subset (subset_convexHull ℝ _ (by simp)) (subset_convexHull ℝ _ (by simp)) hp),?_⟩
  rw [convexHull_interior h]
  obtain ⟨s,t,hs,ht,hst,rfl⟩:=hp
  change ¬ Inside a b c (s • a+t • b)
  have hz : area a b (s • a+t • b)=0 := by
    rw [area_combo _ _ _ _ _ _ hst]
    unfold area
    ring
  exact fun hh=>by have := hh.1; rw [hz] at this; linarith

lemma vertices_segment_frontier {a b c x y : ℂ} (h : 0<area a b c)
    (hx : x∈({a,b,c}:Set ℂ)) (hy : y∈({a,b,c}:Set ℂ)) :
    segment ℝ x y⊆frontier (convexHull ℝ ({a,b,c}:Set ℂ)) := by
  intro p hp
  change p∈closure (convexHull ℝ ({a,b,c}:Set ℂ)) ∧ p∉interior (convexHull ℝ ({a,b,c}:Set ℂ))
  refine ⟨subset_closure ((convex_convexHull ℝ _).segment_subset
    (subset_convexHull ℝ _ hx) (subset_convexHull ℝ _ hy) hp),?_⟩
  rw [convexHull_interior h]
  obtain ⟨s,t,hs,ht,hst,rfl⟩:=hp
  have hz : area a b (s • x+t • y)=0 ∨ area b c (s • x+t • y)=0 ∨ area c a (s • x+t • y)=0 := by
    rcases hx with rfl|rfl|rfl <;> rcases hy with rfl|rfl|rfl <;>
      simp only [area_combo _ _ _ _ _ _ hst] <;> unfold area <;> ring_nf <;> tauto
  intro hh
  rcases hz with hz|hz|hz
  · have := hh.1; rw [hz] at this; linarith
  · have := hh.2.1; rw [hz] at this; linarith
  · have := hh.2.2; rw [hz] at this; linarith

end CannonTriangleWinding

end
end
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Topology Metric unitInterval CannonFaceIncidence CannonTriangleWinding
open scoped OnePoint

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {F : ι → Arc ℂ} {d : Faces F}

omit [DecidableEq ι] [Nonempty ι] in
lemma FacialCycle.hull_eq (C : FacialCycle F d) (z : ℂ → ℂ) :
    faceHull F z d=convexHull ℝ ({z C.a,z C.b,z C.c}:Set ℂ) := by
  unfold faceHull
  rw [C.vertices]
  simp only [Finset.coe_insert,Finset.coe_singleton,image_insert_eq,image_singleton]

omit [DecidableEq ι] [Nonempty ι] in
lemma graph_extension_frontier (F : ι → Arc ℂ)
    (hF : Pairwise fun i j=>Compatible (F i) (F j))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃p∈Q,segment ℝ p.1 p.2)
    (z : ℂ → ℂ) (g : C(ℂ,ℂ))
    (hg : ∀ i t,g (F i t)=Path.segment (z (F i 0)) (z (F i 1)) t)
    (d : Faces F) (C : FacialCycle F d) (hp : 0<area (z C.a) (z C.b) (z C.c))
    {x : ℂ} (hx : x∈closure (face F d)) (hxK : x∈⋃i,range (F i)) :
    g x∈frontier (faceHull F z d) := by
  let _ : LocallyConnectedSpace ((⋃ i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i=>(F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  let _ : DiscreteTopology (ConnectedComponents ((⋃ i,range (F i))ᶜ : Set ℂ)) := inferInstance
  have hcl := tame_region_closure F hF Q hQ ConnectedComponents.continuous_coe d
  change closure (face F d)=face F d∪_ at hcl
  rw [hcl] at hx
  have hxE : x∈⋃i∈regionEdges F ConnectedComponents.mk d,range (F i) := by
    rcases hx with hx|hx
    · exact (hx.1 hxK).elim
    · exact hx
  obtain ⟨i,hi,t,rfl⟩ := mem_iUnion₂.mp hxE
  have hend (e : I) (he : e=0 ∨ e=1) : F i e∈faceVertices F d := by
    apply (mem_faceVertices F _ _).mpr
    exact ⟨⟨i,by rcases he with rfl|rfl; exact Or.inl rfl; exact Or.inr rfl⟩,
      region_edge_in_closure F hF Q hQ ConnectedComponents.continuous_coe hi ⟨e,rfl⟩⟩
  have h0 : z (F i 0)∈({z C.a,z C.b,z C.c}:Set ℂ) := by
    have := hend 0 (Or.inl rfl)
    rw [C.vertices] at this
    simp only [Finset.mem_insert,Finset.mem_singleton] at this
    rcases this with h|h|h <;> simp [h]
  have h1 : z (F i 1)∈({z C.a,z C.b,z C.c}:Set ℂ) := by
    have := hend 1 (Or.inr rfl)
    rw [C.vertices] at this
    simp only [Finset.mem_insert,Finset.mem_singleton] at this
    rcases this with h|h|h <;> simp [h]
  rw [hg,C.hull_eq]
  exact vertices_segment_frontier hp h0 h1 (by rw [←Path.range_segment]; exact mem_range_self t)

theorem exists_spherical_facewise_realization (F : ι → Arc ℂ) [Fintype (Faces F)]
    (hF : Pairwise fun i j=>Compatible (F i) (F j))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃p∈Q,segment ℝ p.1 p.2)
    (hcorner : ∀ d : Faces F,(faceVertices F d).Nonempty) (z : ℂ → ℂ)
    (out : Faces F) (hout : ∀ d : Faces F,d≠out → IsCompact (closure (face F d)))
    (O : FacialCycle F out) (ho : 0<area (z O.a) (z O.b) (z O.c))
    (hfill : (⋃ d : {d : Faces F // d≠out},faceHull F z d.val)=faceHull F z out) :
    ∃ J : OnePoint ℂ≃ₜOnePoint ℂ,
      (∀ x∈frontier (faceHull F z out),J (x:OnePoint ℂ)=(x:OnePoint ℂ)) ∧
      J '' ((↑) '' faceHull F z out : Set (OnePoint ℂ))=
        (((↑) '' interior (faceHull F z out) : Set (OnePoint ℂ)))ᶜ ∧
      ∃ f : C(OnePoint ℂ,OnePoint ℂ),Function.Surjective f ∧
        (∀ d : Faces F,d≠out → MapsTo (fun x : ℂ=>f (x:OnePoint ℂ))
          (closure (face F d)) ((↑) '' faceHull F z d)) ∧
        MapsTo (fun x : ℂ=>f (x:OnePoint ℂ)) (closure (face F out))
          (J '' ((↑) '' faceHull F z out : Set (OnePoint ℂ))) ∧
        (∀ i t,f ((F i t:ℂ):OnePoint ℂ)=((Path.segment (z (F i 0)) (z (F i 1)) t:ℂ):OnePoint ℂ)) := by
  classical
  let S := OnePoint ℂ
  have hK : IsCompact (faceHull F z out) := ((faceVertices F out).finite_toSet.image z).isCompact_convexHull ℝ
  have hi : (interior (faceHull F z out)).Nonempty := by rw [O.hull_eq]; exact convexHull_interior_nonempty ho
  obtain ⟨J,hfix,hreflect⟩ := CannonSphereReflection.exists_convex_reflection (faceHull F z out) hK
    (convex_convexHull ℝ _) hi
  let q := z O.a
  have hq : q∈faceHull F z out := subset_convexHull ℝ _ ⟨O.a,O.mem_a,rfl⟩
  obtain ⟨g,K,hKc,hgK,hg,hgD⟩:=exists_eventually_constant_facewise_realization F hF Q hQ hcorner z out hout q hq
  let fD (d : Faces F) : C(ℂ,S) := if d=out then
    ⟨fun x=>J ((g x:ℂ):S),J.continuous.comp (OnePoint.continuous_coe.comp g.continuous)⟩ else
    ⟨fun x=>(g x:ℂ),OnePoint.continuous_coe.comp g.continuous⟩
  have hgraph (d : Faces F) (x : ℂ) (hxd : x∈closure (face F d)) (hxK : x∈⋃i,range (F i)) :
      fD d x=((g x:ℂ):S) := by
    dsimp [fD]
    split_ifs with hd
    · subst d
      exact hfix _ (graph_extension_frontier F hF Q hQ z g hg out O ho hxd hxK)
    · rfl
  obtain ⟨f,hf⟩ := CannonFiniteClosedGluing.exists_gluing
    (fun d : Faces F=>closure (face F d)) (fun _=>isClosed_closure)
    (facial_closures_cover F hF Q hQ) fD (by
      intro d e x hxd hxe
      by_cases hde : d=e
      · rw [hde]
      have hxK : x∈⋃i,range (F i) := by
        by_contra hxK
        let c : Faces F := ConnectedComponents.mk ⟨x,hxK⟩
        have hc : x∈face F c := ⟨hxK,rfl⟩
        exact hde ((same_face_of_mem_closure F hc hxd).symm.trans (same_face_of_mem_closure F hc hxe))
      exact (hgraph d x hxd hxK).trans (hgraph e x hxe hxK).symm)
  let L : Set ℂ := K∪⋃ d : {d : Faces F // d≠out},closure (face F d.val)
  have hL : IsCompact L := hKc.union (isCompact_iUnion fun d=>hout d.val d.property)
  have hfL (x : ℂ) (hx : x∉L) : f x=J (q:S) := by
    obtain ⟨d,hd⟩ := facial_closures_cover F hF Q hQ x
    have he : d=out := by
      by_contra hn
      exact hx (Or.inr (mem_iUnion.mpr ⟨⟨d,hn⟩,hd⟩))
    subst d
    rw [hf out x hd]
    simp only [fD,ite_eq_left rfl,ContinuousMap.coe_mk,hgK x (fun h=>hx (Or.inl h))]
  let fS : S → S := OnePoint.rec (J (q:S)) f
  have hfS : Continuous fS := by
    rw [OnePoint.continuous_iff]
    constructor
    · apply Filter.Tendsto.congr' (f₁:=fun _ : ℂ=>J (q:S)) ?_ tendsto_const_nhds
      exact Filter.hasBasis_coclosedCompact.mem_iff.mpr ⟨L,⟨hL.isClosed,hL⟩,fun x hx=>(hfL x hx).symm⟩
    · exact f.continuous
  refine ⟨J,hfix,hreflect,⟨fS,hfS⟩,?_,?_,?_,?_⟩
  · intro y
    by_cases hy : y∈((↑) '' interior (faceHull F z out) : Set S)
    · obtain ⟨v,hv,rfl⟩:=hy
      have hvK := interior_subset hv
      rw [←hfill] at hvK
      obtain ⟨d,hd⟩:=mem_iUnion.mp hvK
      obtain ⟨x,hx,hgx⟩:=(hgD d.val).2 hd
      refine ⟨(x:S),?_⟩
      change f x=(v:S)
      rw [hf d.val x (subset_closure hx)]
      simp only [fD,ite_eq_right d.property,ContinuousMap.coe_mk,hgx]
    · have hyJ : y∈J '' ((↑) '' faceHull F z out : Set S) := by rw [hreflect]; exact hy
      obtain ⟨_,⟨v,hv,rfl⟩,rfl⟩:=hyJ
      obtain ⟨x,hx,hgx⟩:=(hgD out).2 hv
      refine ⟨(x:S),?_⟩
      change f x=J (v:S)
      rw [hf out x (subset_closure hx)]
      simp only [fD,ite_eq_left rfl,ContinuousMap.coe_mk,hgx]
  · intro d hd x hx
    change f x∈_
    rw [hf d x hx]
    simp only [fD,ite_eq_right hd,ContinuousMap.coe_mk]
    exact mem_image_of_mem _ ((hgD d).1 hx)
  · intro x hx
    change f x∈_
    rw [hf out x hx]
    simp only [fD,ite_eq_left rfl,ContinuousMap.coe_mk]
    exact mem_image_of_mem J (mem_image_of_mem _ ((hgD out).1 hx))
  · intro i t
    obtain ⟨d,hd⟩:=facial_closures_cover F hF Q hQ (F i t)
    change f (F i t)=_
    rw [hf d _ hd,hgraph d _ hd (mem_iUnion.mpr ⟨i,mem_range_self t⟩),hg]
end CannonEmbeddedArc.Arc

end
end
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology CannonFaceIncidence CannonTriangleWinding
open scoped OnePoint

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {F : ι → Arc ℂ} [Fintype (Faces F)] {out : Faces F}

theorem DevelopedFaces.spherical_realization (B : DevelopedFaces F out)
    (hF : Pairwise fun i j=>Compatible (F i) (F j))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃i,range (F i))\{q}))
    (hthree : ∀ d,(faceVertices F d).card=3)
    (hout : ∀ d : Faces F,d≠out → IsCompact (closure (face F d))) :
    ∃ z : ℂ → ℂ,
      (∀ d,d≠out → ∀ q∈faceVertices F d,z q=B.chart d q) ∧
      (∀ i,dist (z (F i 0)) (z (F i 1))=B.radius (F i 0)+B.radius (F i 1)) ∧
      (∀ u,Vertex F u → ∀ v,Vertex F v → u≠v → B.radius u+B.radius v≤dist (z u) (z v)) ∧
      ∃ J : OnePoint ℂ≃ₜOnePoint ℂ,
        (∀ x∈frontier (faceHull F z out),J (x:OnePoint ℂ)=(x:OnePoint ℂ)) ∧
        J '' ((↑) '' faceHull F z out : Set (OnePoint ℂ))=
          (((↑) '' interior (faceHull F z out) : Set (OnePoint ℂ)))ᶜ ∧
        ∃ f : C(OnePoint ℂ,OnePoint ℂ),Function.Surjective f ∧
          (∀ d : Faces F,d≠out → MapsTo (fun x : ℂ=>f (x:OnePoint ℂ))
            (closure (face F d)) ((↑) '' faceHull F z d)) ∧
          MapsTo (fun x : ℂ=>f (x:OnePoint ℂ)) (closure (face F out))
            (J '' ((↑) '' faceHull F z out : Set (OnePoint ℂ))) ∧
          (∀ i t,f ((F i t:ℂ):OnePoint ℂ)=((Path.segment (z (F i 0)) (z (F i 1)) t:ℂ):OnePoint ℂ)) := by
  classical
  obtain ⟨z,C,O,hz,hlen,hpos,ho,hchain,hdis⟩:=B.univalent_triangles hF Q hQ hK hthree
  have hfill : (⋃ d : {d : Faces F // d≠out},faceHull F z d.val)=faceHull F z out := by
    have H:=triangle_closures_fill (fun d=>z (C d).a) (fun d=>z (C d).b) (fun d=>z (C d).c)
      (z O.a) (z O.b) (z O.c) hpos ho (hchain ℤ)
    simp only [convexHull_closure_inside (hpos _),convexHull_closure_inside ho] at H
    simp_rw [(C _).hull_eq,O.hull_eq]
    exact H
  have hcorner (d : Faces F) : (faceVertices F d).Nonempty := Finset.card_pos.mp (by rw [hthree]; norm_num)
  refine ⟨z,hz,hlen,?_,exists_spherical_facewise_realization F hF Q hQ hcorner z out hout O ho hfill⟩
  intro q hq v hv hqv
  by_cases hqo : q∈faceVertices F out
  · by_cases hvo : v∈faceVertices F out
    · exact (O.developed_length hqo hvo hqv z B.radius hlen).ge
    · have H:=B.disk_disjoint_of_interior hF Q hQ hK z hz hlen C O hpos ho
        (hchain ℤ) hdis hv hq hvo hqv.symm
      have HH:=(disjoint_ball_ball_iff (B.radius_pos v) (B.radius_pos q)).mp H
      simpa only [add_comm,dist_comm] using HH
  · have H:=B.disk_disjoint_of_interior hF Q hQ hK z hz hlen C O hpos ho
      (hchain ℤ) hdis hq hv hqo hqv
    exact (disjoint_ball_ball_iff (B.radius_pos q) (B.radius_pos v)).mp H
end CannonEmbeddedArc.Arc

end
end
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Topology Metric unitInterval CannonFaceIncidence

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem exists_facewise_surjective_realization (F : ι → Arc ℂ)
    (hF : Pairwise fun i j=>Compatible (F i) (F j))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃p∈Q,segment ℝ p.1 p.2)
    (hcorner : ∀ d : Faces F,(faceVertices F d).Nonempty) (z : ℂ → ℂ) :
    ∃ g : C(ℂ,ℂ),
      (∀ i t,g (F i t)=Path.segment (z (F i 0)) (z (F i 1)) t) ∧
      ∀ d : Faces F,MapsTo g (closure (face F d)) (faceHull F z d) ∧
        faceHull F z d⊆g '' face F d := by
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
  have hlocal (d : Faces F) := CannonLocalRealization.exists_local_surjection
    (faceHull F z d) (face F d) (((faceVertices F d).finite_toSet.image z).isCompact_convexHull ℝ)
    (face_open F d) (face_nonempty F d) g
  choose gd hgd honto using hlocal
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
    · intro y hy
      obtain ⟨x,hx,hxy⟩:=honto d hy
      refine ⟨x,hx,?_⟩
      rw [hf₀ d x (subset_closure hx)]
      change P d (gd d x)=y
      rw [hxy]
      exact hfix d y hy
end CannonEmbeddedArc.Arc

end
end
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonFaceIncidence

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {F : ι → Arc ℂ} [Fintype (Faces F)] {d : Faces F}

omit [DecidableEq ι] [Nonempty ι] [Fintype (Faces F)] in
lemma FacialCycle.hull_radius_bound (C : FacialCycle F d) (z : ℂ → ℂ) (ρ : ℂ → ℝ)
    (hρ : ∀ v,0<ρ v) (c : ℝ) (hc : 0<c)
    (hlen : ∀ i,dist (z (F i 0)) (z (F i 1))=ρ (F i 0)+ρ (F i 1))
    (hring : ∀ i u v,Spans (F i) u v → c*ρ u≤ρ v ∧ c*ρ v≤ρ u)
    {v : ℂ} (hv : v∈faceVertices F d) :
    faceHull F z d⊆closedBall (z v) ((1+c⁻¹)*ρ v) := by
  apply convexHull_min _ (convex_closedBall _ _)
  rintro _ ⟨w,hw,rfl⟩
  rw [mem_closedBall]
  by_cases hwv : w=v
  · subst w
    simp only [dist_self]
    exact mul_nonneg (add_nonneg zero_le_one (inv_nonneg.mpr hc.le)) (hρ v).le
  · obtain ⟨i,hi⟩:=C.pair_edge hw hv hwv
    rw [hi.developed_length z ρ (hlen i)]
    have hr : ρ w≤c⁻¹*ρ v := by
      have hh := (hring i w v hi).1
      exact (le_div_iff₀ hc).mpr (by nlinarith) |>.trans_eq (by rw [div_eq_mul_inv,mul_comm])
    nlinarith

omit [DecidableEq ι] [Nonempty ι] [Fintype (Faces F)] in
lemma facial_star_image_bound (z : ℂ → ℂ) (ρ : ℂ → ℝ) (hρ : ∀ v,0<ρ v)
    (c : ℝ) (hc : 0<c) (C : ∀ d : Faces F,FacialCycle F d)
    (hlen : ∀ i,dist (z (F i 0)) (z (F i 1))=ρ (F i 0)+ρ (F i 1))
    (hring : ∀ i u v,Spans (F i) u v → c*ρ u≤ρ v ∧ c*ρ v≤ρ u)
    (g : C(ℂ,ℂ)) (hg : ∀ d : Faces F,MapsTo g (closure (face F d)) (faceHull F z d))
    (v : ℂ) : MapsTo g (⋃ d∈{d : Faces F | v∈faceVertices F d},closure (face F d))
      (closedBall (z v) ((1+c⁻¹)*ρ v)) := by
  intro x hx
  obtain ⟨d,hd,hx⟩:=mem_iUnion₂.mp hx
  exact (C d).hull_radius_bound z ρ hρ c hc hlen hring hd (hg d hx)
end CannonEmbeddedArc.Arc

end
end
end
end

end OAI

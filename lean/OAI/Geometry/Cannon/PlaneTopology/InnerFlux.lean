import Mathlib
import OAI.Geometry.Cannon.PlaneTopology.Crossing
import OAI.Geometry.Cannon.CirclePacking.Cycle

namespace OAI

section
section
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonFaceIncidence CannonPackingGeometry

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {F : ι → Arc ℂ} [Fintype (Faces F)] {out : Faces F}
attribute [local instance] Classical.propDecidable

def innerFlux {R : Type*} [AddCommMonoid R]
    (C : ∀ d : {d : Faces F // d≠out},FacialCycle F d.val) (f : ℂ → ℂ → R) (i : ι) : R :=
  ∑ d,(C d).flux f i

omit [Nonempty ι] in
lemma innerFlux_sum {R : Type*} [AddCommMonoid R]
    (C : ∀ d : {d : Faces F // d≠out},FacialCycle F d.val) (f : ℂ → ℂ → R) :
    (∑ i,innerFlux C f i)=∑ d,CannonTriangleBoundary.cycle f (C d).a (C d).b (C d).c := by
  unfold innerFlux
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  exact (C d).sum_flux f

omit [DecidableEq ι] [Fintype (Faces F)] in
lemma boundary_edge_other
    (hF : Pairwise fun i j=>Compatible (F i) (F j))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q}))
    {i : ι} (hi : i∈regionEdges F ConnectedComponents.mk out) :
    ∃ d : Faces F,d≠out ∧ i∈regionEdges F ConnectedComponents.mk d := by
  classical
  let _ : LocallyConnectedSpace ((⋃ i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i=>(F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  let _ : DiscreteTopology (ConnectedComponents ((⋃ i,range (F i))ᶜ : Set ℂ)) := inferInstance
  obtain ⟨a,b,hab,ha,hb⟩ := noncut_edge_two_faces F hF Q hQ hK i
  rcases edge_face_unique_two F hF Q hQ i hab ha hb hi with ho|ho
  · exact ⟨b,fun h=>hab (ho.symm.trans h.symm),hb⟩
  · exact ⟨a,fun h=>hab (h.trans ho),ha⟩

lemma innerFlux_boundary {R : Type*} [AddCommMonoid R]
    (hF : Pairwise fun i j=>Compatible (F i) (F j))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (C : ∀ d : {d : Faces F // d≠out},FacialCycle F d.val)
    (f : ℂ → ℂ → R) {i : ι} {d : Faces F} (hd : d≠out)
    (hi : i∈regionEdges F ConnectedComponents.mk out)
    (hdi : i∈regionEdges F ConnectedComponents.mk d) :
    innerFlux C f i=(C ⟨d,hd⟩).flux f i := by
  classical
  unfold innerFlux
  apply Finset.sum_eq_single (⟨d,hd⟩ : {d : Faces F // d≠out})
  · intro e he hed
    apply (C e).flux_nonmem f
    intro hie
    rcases edge_face_unique_two F hF Q hQ i hd hdi hi hie with h|h
    · exact hed (Subtype.ext h)
    · exact e.property h
  · simp

lemma innerFlux_interior {R : Type*} [AddCommGroup R]
    (hF : Pairwise fun i j=>Compatible (F i) (F j))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q}))
    (C : ∀ d : {d : Faces F // d≠out},FacialCycle F d.val)
    (z : ℂ → ℂ) (hpos : ∀ d,0<CannonTriangleWinding.area (z (C d).a) (z (C d).b) (z (C d).c))
    (hop : ∀ i (d e : {d : Faces F // d≠out}),d≠e →
      i∈regionEdges F ConnectedComponents.mk d.val → i∈regionEdges F ConnectedComponents.mk e.val →
      ∀ u∈faceVertices F d.val,u≠F i 0 → u≠F i 1 →
      ∀ v∈faceVertices F e.val,v≠F i 0 → v≠F i 1 →
      orientedArea (z (F i 0)) (z (F i 1)) (z u)*
        orientedArea (z (F i 0)) (z (F i 1)) (z v)<0)
    (f : ℂ → ℂ → R) (hf : ∀ x y,f y x= -f x y)
    {i : ι} (hi : i∉regionEdges F ConnectedComponents.mk out) : innerFlux C f i=0 := by
  classical
  let _ : LocallyConnectedSpace ((⋃ i,range (F i))ᶜ : Set ℂ) :=
    (isClosed_iUnion_of_finite fun i=>(F i).compact_range.isClosed).isOpen_compl.locallyConnectedSpace
  let _ : DiscreteTopology (ConnectedComponents ((⋃ i,range (F i))ᶜ : Set ℂ)) := inferInstance
  obtain ⟨a,b,hab,ha,hb⟩ := noncut_edge_two_faces F hF Q hQ hK i
  have hao : a≠out := fun h=>hi (h ▸ ha)
  have hbo : b≠out := fun h=>hi (h ▸ hb)
  let da : {d : Faces F // d≠out} := ⟨a,hao⟩
  let db : {d : Faces F // d≠out} := ⟨b,hbo⟩
  have hdd : da≠db := fun h=>hab (congrArg Subtype.val h)
  have heq : (∑ d∈({da,db}:Finset {d : Faces F // d≠out}),(C d).flux f i)=innerFlux C f i := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro d hd hd'
    apply (C d).flux_nonmem f
    intro hie
    rcases edge_face_unique_two F hF Q hQ i hab ha hb hie with h|h
    · exact hd' (by simp only [Finset.mem_insert,Finset.mem_singleton]; exact Or.inl (Subtype.ext h))
    · exact hd' (by simp only [Finset.mem_insert,Finset.mem_singleton]; exact Or.inr (Subtype.ext h))
  rw [←heq,Finset.sum_pair hdd]
  exact (C da).flux_cancel hF Q hQ hK (C db) z (hpos da) (hpos db) f hf ha hb (hop i da db hdd ha hb)

end CannonEmbeddedArc.Arc

end
end
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonFaceIncidence CannonPackingGeometry CannonTriangleBoundary

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {F : ι → Arc ℂ} [Fintype (Faces F)] {out : Faces F}
attribute [local instance] Classical.propDecidable

lemma boundary_flux_signed
    (hF : Pairwise fun i j=>Compatible (F i) (F j))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q}))
    (C : ∀ d : {d : Faces F // d≠out},FacialCycle F d.val)
    (z : ℂ → ℂ) (hpos : ∀ d,0<CannonTriangleWinding.area (z (C d).a) (z (C d).b) (z (C d).c))
    {i : ι} (hi : i∈regionEdges F ConnectedComponents.mk out)
    {a b : ℂ} (hab : Spans (F i) a b) :
    ∃ s : Bool,∀ (R : Type) [AddCommGroup R] (f : ℂ → ℂ → R),
      (∀ x y,f y x= -f x y) → innerFlux C f i=signed s (f a b) := by
  obtain ⟨d,hd,hdi⟩ := boundary_edge_other hF Q hQ hK hi
  obtain ⟨u,v,w,hsp,hw,hwu,hwv,hp,hval⟩ := (C ⟨d,hd⟩).edge_data hF Q hQ hK z (hpos _) hdi
  rcases hab.endpoints_eq hsp with h|h
  · refine ⟨true,?_⟩
    intro R inst f hf
    rw [innerFlux_boundary hF Q hQ C f hd hi hdi,hval R f,h.1,h.2]
    rfl
  · refine ⟨false,?_⟩
    intro R inst f hf
    rw [innerFlux_boundary hF Q hQ C f hd hi hdi,hval R f,h.1,h.2,hf a b]
    rfl

omit [DecidableEq ι] [Nonempty ι] in
lemma sum_three_support {R : Type*} [AddCommMonoid R] (f : ι → R)
    {e g h : ι} (heg : e≠g) (heh : e≠h) (hgh : g≠h)
    (hz : ∀ i,i≠e → i≠g → i≠h → f i=0) : ∑ i,f i=f e+f g+f h := by
  classical
  have H : (∑ i∈({e,g,h}:Finset ι),f i)=∑ i,f i := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i hi hn
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hn
    exact hz i hn.1 hn.2.1 hn.2.2
  rw [←H]
  simp [heg,heh,hgh,add_assoc]

theorem positive_facial_chain
    (hF : Pairwise fun i j=>Compatible (F i) (F j))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q}))
    (C : ∀ d : {d : Faces F // d≠out},FacialCycle F d.val) (O : FacialCycle F out)
    (z : ℂ → ℂ) (hpos : ∀ d,0<CannonTriangleWinding.area (z (C d).a) (z (C d).b) (z (C d).c))
    (hop : ∀ i (d e : {d : Faces F // d≠out}),d≠e →
      i∈regionEdges F ConnectedComponents.mk d.val → i∈regionEdges F ConnectedComponents.mk e.val →
      ∀ u∈faceVertices F d.val,u≠F i 0 → u≠F i 1 →
      ∀ v∈faceVertices F e.val,v≠F i 0 → v≠F i 1 →
      orientedArea (z (F i 0)) (z (F i 1)) (z u)*
        orientedArea (z (F i 0)) (z (F i 1)) (z v)<0) :
    ∃ O' : FacialCycle F out,∀ (R : Type) [AddCommGroup R] (f : ℂ → ℂ → R),
      (∀ x y,f y x= -f x y) →
      (∑ d,cycle f (C d).a (C d).b (C d).c)=cycle f O'.a O'.b O'.c := by
  classical
  obtain ⟨s,hs⟩ := boundary_flux_signed hF Q hQ hK C z hpos O.mem_e O.spans_e
  obtain ⟨t,ht⟩ := boundary_flux_signed hF Q hQ hK C z hpos O.mem_f O.spans_f
  obtain ⟨r,hr⟩ := boundary_flux_signed hF Q hQ hK C z hpos O.mem_g O.spans_g
  have H (R : Type) [AddCommGroup R] (f : ℂ → ℂ → R) (hf : ∀ x y,f y x= -f x y) :
      (∑ d,cycle f (C d).a (C d).b (C d).c)=
        signed s (f O.a O.b)+signed t (f O.b O.c)+signed r (f O.c O.a) := by
    rw [←innerFlux_sum C f]
    have hz (i : ι) (he : i≠O.e) (hf' : i≠O.f) (hg : i≠O.g) : innerFlux C f i=0 := by
      apply innerFlux_interior hF Q hQ hK C z hpos hop f hf
      rw [O.edges hF Q hQ hK]
      simpa only [Set.mem_insert_iff,Set.mem_singleton_iff,not_or] using And.intro he ⟨hf',hg⟩
    rw [sum_three_support (innerFlux C f) O.edge_ne.1 O.edge_ne.2.1 O.edge_ne.2.2 hz,
      hs R f hf,ht R f hf,hr R f hf]
  obtain ⟨hst,hsr⟩ := triangle_boundary_signs (fun d=>(C d).a) (fun d=>(C d).b) (fun d=>(C d).c)
    O.ab O.ac O.bc s t r (H ℤ)
  subst t; subst r
  cases s with
  | true =>
    refine ⟨O,?_⟩
    intro R inst f hf
    simpa only [signed,ite_true,cycle] using H R f hf
  | false =>
    refine ⟨O.reverse,?_⟩
    intro R inst f hf
    have HH := H R f hf
    simp only [signed] at HH
    rw [HH]
    change -f O.a O.b+ -f O.b O.c+ -f O.c O.a=f O.a O.c+f O.c O.b+f O.b O.a
    rw [hf O.c O.a,hf O.b O.c,hf O.a O.b]
    abel

end CannonEmbeddedArc.Arc

end
end
section
noncomputable section
namespace CannonTriangleWinding
open Set Topology

lemma dense_ne_of_openMap {X : Type*} [TopologicalSpace X] (f : X → ℝ)
    (hf : IsOpenMap f) (t : ℝ) : Dense {x | f x≠t} := by
  apply dense_iff_inter_open.mpr
  intro U hU hne
  obtain ⟨y,hy,ht⟩ := (dense_compl_singleton t).inter_open_nonempty (f '' U)
    (hf U hU) (hne.image f)
  obtain ⟨x,hx,rfl⟩ := hy
  exact ⟨x,hx,ht⟩

lemma area_openMap {a b : ℂ} (hab : a≠b) : IsOpenMap (area a b) := by
  let L : ℂ →L[ℝ] ℝ := (b.re-a.re) • Complex.imCLM-(b.im-a.im) • Complex.reCLM
  have hL (p : ℂ) : L p=(b.re-a.re)*p.im-(b.im-a.im)*p.re := rfl
  have hsurj : Function.Surjective L := by
    intro t
    by_cases h : b.re-a.re=0
    · have h' : b.im-a.im≠0 := by
        intro hh
        exact hab (Complex.ext (sub_eq_zero.mp h).symm (sub_eq_zero.mp hh).symm)
      refine ⟨⟨-t/(b.im-a.im),0⟩,?_⟩
      rw [hL]
      simp only [h,zero_mul,zero_sub]
      field_simp
    · refine ⟨⟨0,t/(b.re-a.re)⟩,?_⟩
      rw [hL]
      simp only [mul_zero,sub_zero]
      exact mul_div_cancel₀ _ h
  have ho : IsOpenMap (fun p : ℂ=>p-a) := isOpenMap_sub_right a
  exact (L.isOpenMap hsurj).comp ho

lemma generic_dense_open (a b c : ℂ) (hab : a≠b) (hbc : b≠c) (hca : c≠a) :
    Dense {p | Generic a b c p} ∧ IsOpen {p | Generic a b c p} := by
  have hd (x : ℂ) : Dense {p : ℂ | x.im≠p.im} := by
    simpa only [ne_comm] using dense_ne_of_openMap Complex.im Complex.isOpenMap_im x.im
  have he (x y : ℂ) (hxy : x≠y) : Dense {p | area x y p≠0} :=
    dense_ne_of_openMap (area x y) (area_openMap hxy) 0
  have ho (x : ℂ) : IsOpen {p : ℂ | x.im≠p.im} := isOpen_ne_fun continuous_const Complex.continuous_im
  have hp (x y : ℂ) : IsOpen {p | area x y p≠0} := by
    apply isOpen_ne_fun _ continuous_const
    unfold area
    fun_prop
  have Hr := ((he a b hab).inter_of_isOpen_right
    ((he b c hbc).inter_of_isOpen_right (he c a hca) (hp c a)) ((hp b c).inter (hp c a)))
  have HrO := (hp a b).inter ((hp b c).inter (hp c a))
  have Hq := (hd c).inter_of_isOpen_right Hr HrO
  have HqO := (ho c).inter HrO
  have HH := (hd b).inter_of_isOpen_right Hq HqO
  have HHO := (ho b).inter HqO
  exact ⟨(hd a).inter_of_isOpen_right HH HHO,(ho a).inter HHO⟩

lemma area_pos_distinct {a b c : ℂ} (h : 0<area a b c) : a≠b ∧ b≠c ∧ c≠a := by
  constructor
  · intro he; subst b; simp [area] at h
  constructor
  · intro he; subst c; have : area a b b=0 := by unfold area; ring
    rw [this] at h; exact lt_irrefl _ h
  · intro he; subst c; simp [area] at h

theorem triangle_interiors_disjoint {D : Type*} [Fintype D]
    (a b c : D → ℂ) (u v w : ℂ)
    (hpos : ∀ d,0<area (a d) (b d) (c d)) (ho : 0<area u v w)
    (hchain : ∀ f : ℂ → ℂ → ℤ,(∀ x y,f y x= -f x y) →
      (∑ d : D,(f (a d) (b d)+f (b d) (c d)+f (c d) (a d)))=f u v+f v w+f w u) :
    Pairwise fun d e=>Disjoint {p | Inside (a d) (b d) (c d) p}
      {p | Inside (a e) (b e) (c e) p} := by
  have hg (d : D) := generic_dense_open (a d) (b d) (c d)
    (area_pos_distinct (hpos d)).1 (area_pos_distinct (hpos d)).2.1 (area_pos_distinct (hpos d)).2.2
  have hgO := generic_dense_open u v w (area_pos_distinct ho).1
    (area_pos_distinct ho).2.1 (area_pos_distinct ho).2.2
  have hG : Dense ((⋂ d : D,{p | Generic (a d) (b d) (c d) p})∩{p | Generic u v w p}) :=
    (dense_iInter_of_isOpen (fun d=>(hg d).2) (fun d=>(hg d).1)).inter_of_isOpen_right hgO.1 hgO.2
  intro d e hde
  apply Set.disjoint_left.mpr
  intro p hp hp'
  let U := {p | Inside (a d) (b d) (c d) p}∩{p | Inside (a e) (b e) (c e) p}
  obtain ⟨q,hqU,hqG⟩ := hG.inter_open_nonempty U
    ((inside_open _ _ _).inter (inside_open _ _ _)) ⟨p,hp,hp'⟩
  exact hde (generic_unique a b c u v w q hpos ho (fun i=>mem_iInter.mp hqG.1 i)
    hqG.2 hchain hqU.1 hqU.2)

end CannonTriangleWinding

end
end
section
noncomputable section
namespace CannonEmbeddedArc.Arc
open Set Metric Topology unitInterval CannonFaceIncidence CannonPackingGeometry CannonTriangleBoundary

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {F : ι → Arc ℂ} [Fintype (Faces F)] {out : Faces F}
attribute [local instance] Classical.propDecidable

omit [DecidableEq ι] in
lemma positive_outer_of_chain
    (hF : Pairwise fun i j=>Compatible (F i) (F j))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q}))
    (C : ∀ d : {d : Faces F // d≠out},FacialCycle F d.val) (O : FacialCycle F out)
    (z : ℂ → ℂ) (hpos : ∀ d,0<CannonTriangleWinding.area (z (C d).a) (z (C d).b) (z (C d).c))
    (hchain : ∀ (R : Type) [AddCommGroup R] (f : ℂ → ℂ → R),
      (∀ x y,f y x= -f x y) →
      (∑ d,cycle f (C d).a (C d).b (C d).c)=cycle f O.a O.b O.c) :
    0<CannonTriangleWinding.area (z O.a) (z O.b) (z O.c) := by
  classical
  obtain ⟨d,hd,hdi⟩ := boundary_edge_other hF Q hQ hK O.mem_e
  let _ : Nonempty {d : Faces F // d≠out} := ⟨⟨d,hd⟩⟩
  let f : ℂ → ℂ → ℝ := fun x y=>(z x).re*(z y).im-(z x).im*(z y).re
  have hf (x y : ℂ) : f y x= -f x y := by dsimp [f]; ring
  have heq (a b c : ℂ) : cycle f a b c=CannonTriangleWinding.area (z a) (z b) (z c) := by
    dsimp [cycle,f,CannonTriangleWinding.area]; ring
  have H := hchain ℝ f hf
  simp only [heq] at H
  rw [←H]
  exact Finset.sum_pos (fun d hd=>hpos d) Finset.univ_nonempty

theorem DevelopedFaces.univalent_triangles (B : DevelopedFaces F out)
    (hF : Pairwise fun i j=>Compatible (F i) (F j))
    (Q : Finset (ℂ × ℂ)) (hQ : ∀ i,range (F i)⊆⋃ p∈Q,segment ℝ p.1 p.2)
    (hK : ∀ q : ℂ,IsPreconnected ((⋃ i,range (F i))\{q}))
    (hthree : ∀ d,(faceVertices F d).card=3) :
    ∃ z : ℂ → ℂ,∃ C : ∀ d : {d : Faces F // d≠out},FacialCycle F d.val,
      ∃ O : FacialCycle F out,
      (∀ d,d≠out → ∀ q∈faceVertices F d,z q=B.chart d q) ∧
      (∀ i,dist (z (F i 0)) (z (F i 1))=B.radius (F i 0)+B.radius (F i 1)) ∧
      (∀ d,0<CannonTriangleWinding.area (z (C d).a) (z (C d).b) (z (C d).c)) ∧
      0<CannonTriangleWinding.area (z O.a) (z O.b) (z O.c) ∧
      (∀ (R : Type) [AddCommGroup R] (f : ℂ → ℂ → R),
        (∀ x y,f y x= -f x y) →
        (∑ d,cycle (fun x y=>f (z x) (z y)) (C d).a (C d).b (C d).c)=
          cycle f (z O.a) (z O.b) (z O.c)) ∧
      Pairwise (fun d e=>Disjoint
        {p | CannonTriangleWinding.Inside (z (C d).a) (z (C d).b) (z (C d).c) p}
        {p | CannonTriangleWinding.Inside (z (C e).a) (z (C e).b) (z (C e).c) p}) := by
  classical
  obtain ⟨z,hz,hlen,hne,hop⟩ := B.global_metric_centers F hF Q hQ hK
  have exC (d : {d : Faces F // d≠out}) : ∃ C : FacialCycle F d.val,
      0<CannonTriangleWinding.area (z C.a) (z C.b) (z C.c) := by
    obtain ⟨C⟩ := facialCycle_exists F hF Q hQ hK d.val (hthree d.val)
    exact C.orient z (hne d.val d.property C.a C.mem_a C.b C.mem_b C.c C.mem_c C.ab C.ac C.bc)
  choose C hpos using exC
  obtain ⟨O⟩ := facialCycle_exists F hF Q hQ hK out (hthree out)
  obtain ⟨O,hchain⟩ := positive_facial_chain hF Q hQ hK C O z hpos (by
    intro i d e hde hi hj
    exact hop i d.val e.val (fun h=>hde (Subtype.ext h)) d.property e.property hi hj)
  have ho := positive_outer_of_chain hF Q hQ hK C O z hpos hchain
  have H (R : Type) [AddCommGroup R] (f : ℂ → ℂ → R) (hf : ∀ x y,f y x= -f x y) :=
    hchain R (fun x y=>f (z x) (z y)) (fun x y=>hf (z x) (z y))
  refine ⟨z,C,O,hz,hlen,hpos,ho,H,?_⟩
  exact CannonTriangleWinding.triangle_interiors_disjoint (fun d=>z (C d).a) (fun d=>z (C d).b)
      (fun d=>z (C d).c) (z O.a) (z O.b) (z O.c) hpos ho (H ℤ)

end CannonEmbeddedArc.Arc

end
end
end
end

end OAI

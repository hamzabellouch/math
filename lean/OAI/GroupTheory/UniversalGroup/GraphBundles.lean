import OAI.GroupTheory.UniversalGroup.SphereHomotopies

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology
open scoped TensorProduct

namespace UniversalFInfinity.GraphBundle

section
open Set Topology
open scoped unitInterval
universe u v w z
variable {C : Type u}
variable {A : Type v} [TopologicalSpace A] {B : Type w} [TopologicalSpace B]
variable (τ : C → C) (L R : C → C(B,A))

abbrev Inner := Set.Ioo (0:ℝ) 1
abbrev Core := (C × A) ⊕ (C × (Inner × B))
def Space (_ : C → C) (_ _ : C → C(B,A)) := Core (C := C) (A := A) (B := B)
def vertex (c : C) (x : A) : Space τ L R := Sum.inl (c,x)
def interior (c : C) (s : Inner) (x : B) : Space τ L R := Sum.inr (c,(s,x))

def edge (c : C) (t : I) (x : B) : Space τ L R := by
  classical
  exact if h0 : t = 0 then vertex τ L R c (L c x) else
    if h1 : t = 1 then vertex τ L R (τ c) (R c x) else
      interior τ L R c ⟨t.1,lt_of_le_of_ne t.2.1 (fun h => h0 (Subtype.ext h.symm)),
        lt_of_le_of_ne t.2.2 (fun h => h1 (Subtype.ext h))⟩ x

lemma edge_zero (c : C) (x : B) : edge τ L R c 0 x = vertex τ L R c (L c x) := by simp [edge]
lemma edge_one (c : C) (x : B) : edge τ L R c 1 x = vertex τ L R (τ c) (R c x) := by simp [edge]
lemma edge_inner (c : C) (s : Inner) (x : B) :
    edge τ L R c ⟨s.1,s.2.1.le,s.2.2.le⟩ x = interior τ L R c s x := by
  unfold edge
  split_ifs with h0 h1
  · exact False.elim (s.2.1.ne' (congrArg Subtype.val h0))
  · exact False.elim (s.2.2.ne (congrArg Subtype.val h1))
  · rfl

variable [TopologicalSpace C] [DiscreteTopology C]

abbrev Raw := (C × A) ⊕ (C × (I × B))
def quotient : Raw (C := C) (A := A) (B := B) → Space τ L R :=
  Sum.elim (fun z => vertex τ L R z.1 z.2) (fun z => edge τ L R z.1 z.2.1 z.2.2)
instance : TopologicalSpace (Space τ L R) :=
  TopologicalSpace.coinduced (quotient τ L R) inferInstance

omit [DiscreteTopology C] in
lemma continuous_quotient : Continuous (quotient τ L R) := continuous_coinduced_rng
omit [DiscreteTopology C] in
lemma continuous_vertex : Continuous (fun z : C × A => vertex τ L R z.1 z.2) :=
  (continuous_quotient τ L R).comp continuous_inl
omit [DiscreteTopology C] in
lemma continuous_edge : Continuous (fun z : C × (I × B) => edge τ L R z.1 z.2.1 z.2.2) :=
  (continuous_quotient τ L R).comp continuous_inr

def vertexMap (c : C) : C(A,Space τ L R) :=
  ⟨vertex τ L R c,(continuous_vertex τ L R).comp (continuous_const.prodMk continuous_id)⟩
def edgeMap (c : C) : C(I × B,Space τ L R) :=
  ⟨fun z => edge τ L R c z.1 z.2,(continuous_edge τ L R).comp (continuous_const.prodMk continuous_id)⟩

lemma continuous_iff {Y : Type z} [TopologicalSpace Y] (f : Space τ L R → Y) :
    Continuous f ↔ (∀ c,Continuous (fun x => f (vertex τ L R c x))) ∧
      ∀ c,Continuous (fun z : I × B => f (edge τ L R c z.1 z.2)) := by
  change Continuous[TopologicalSpace.coinduced (quotient τ L R) inferInstance,_] f ↔ _
  rw [continuous_coinduced_dom,continuous_sum_dom]
  exact and_congr continuous_prod_of_discrete_left continuous_prod_of_discrete_left

lemma closed_of_slices {D : Type*} [TopologicalSpace D] {S : Set (C × D)}
    (h : ∀ c,IsClosed ((fun x => (c,x)) ⁻¹' S)) : IsClosed S := by
  rw [←isOpen_compl_iff]
  apply isOpen_iff_forall_mem_open.mpr
  intro z hz
  refine ⟨{z.1} ×ˢ ((fun x => (z.1,x)) ⁻¹' S)ᶜ,?_,
    (isOpen_discrete {z.1}).prod (h z.1).isOpen_compl,⟨rfl,hz⟩⟩
  intro p hp
  have he : p.1 = z.1 := hp.1
  simpa only [Set.mem_compl_iff,Set.mem_preimage,←he] using hp.2

lemma isClosed_iff (S : Set (Space τ L R)) :
    IsClosed S ↔ (∀ c,IsClosed ((vertex τ L R c) ⁻¹' S)) ∧
      ∀ c,IsClosed ((fun z : I × B => edge τ L R c z.1 z.2) ⁻¹' S) := by
  change @IsClosed _ (TopologicalSpace.coinduced (quotient τ L R) inferInstance) S ↔ _
  rw [isClosed_coinduced,isClosed_sum_iff]
  constructor
  · rintro ⟨hv,he⟩
    exact ⟨fun c => hv.preimage (continuous_const.prodMk continuous_id),
      fun c => he.preimage (continuous_const.prodMk continuous_id)⟩
  · rintro ⟨hv,he⟩
    exact ⟨closed_of_slices hv,closed_of_slices he⟩

variable {Y : Type z} [TopologicalSpace Y]
variable (v : C → C(A,Y)) (e : C → C(I × B,Y))
variable (he0 : ∀ c x,e c (0,x) = v c (L c x))
variable (he1 : ∀ c x,e c (1,x) = v (τ c) (R c x))

def liftFun : Space τ L R → Y :=
  Sum.elim (fun z => v z.1 z.2) (fun z => e z.1 (⟨z.2.1.1,z.2.1.2.1.le,z.2.1.2.2.le⟩,z.2.2))
omit [TopologicalSpace C] [DiscreteTopology C] in
lemma liftFun_vertex (c : C) (x : A) : liftFun τ L R v e (vertex τ L R c x) = v c x := rfl
omit [TopologicalSpace C] [DiscreteTopology C] in
include he0 he1 in
lemma liftFun_edge (c : C) (t : I) (x : B) : liftFun τ L R v e (edge τ L R c t x) = e c (t,x) := by
  classical
  unfold edge
  split_ifs with h0 h1
  · subst t; exact (he0 c x).symm
  · subst t; exact (he1 c x).symm
  · rfl

def lift : C(Space τ L R,Y) :=
  ⟨liftFun τ L R v e,(continuous_iff τ L R _).mpr
    ⟨fun c => (v c).continuous,fun c => by
      have h : (fun z : I × B => liftFun τ L R v e (edge τ L R c z.1 z.2)) = e c := by
        funext z; exact liftFun_edge τ L R v e he0 he1 c z.1 z.2
      rw [h]; exact (e c).continuous⟩⟩
lemma lift_vertex (c : C) (x : A) : lift τ L R v e he0 he1 (vertex τ L R c x) = v c x := rfl
lemma lift_edge (c : C) (z : I × B) : lift τ L R v e he0 he1 (edge τ L R c z.1 z.2) = e c z :=
  liftFun_edge τ L R v e he0 he1 c z.1 z.2
end

section
open Set Topology
open scoped unitInterval
universe u v w z
variable {C : Type u} [TopologicalSpace C] [DiscreteTopology C]
variable {A : Type v} [TopologicalSpace A] {B : Type w} [TopologicalSpace B]
variable (τ : C → C) (L R : C → C(B,A))

omit [TopologicalSpace C] [DiscreteTopology C] in
lemma edge_preimage_vertices (S : Set (C × A)) (c : C) :
    (fun z : I × B => edge τ L R c z.1 z.2) ⁻¹'
      ((fun z : C × A => vertex τ L R z.1 z.2) '' S) =
    ({0} ×ˢ ((fun x => (c,L c x)) ⁻¹' S)) ∪
      ({1} ×ˢ ((fun x => (τ c,R c x)) ⁻¹' S)) := by
  classical
  ext ⟨t,x⟩
  change edge τ L R c t x ∈ ((fun z : C × A => vertex τ L R z.1 z.2) '' S) ↔
    (t = 0 ∧ (c,L c x) ∈ S) ∨ (t = 1 ∧ (τ c,R c x) ∈ S)
  by_cases h0 : t = 0
  · subst t
    rw [edge_zero]
    simp only [true_and,zero_ne_one,false_and,or_false]
    constructor
    · rintro ⟨a,ha,he⟩
      have heq : a = (c,L c x) := Sum.inl.inj he
      exact heq ▸ ha
    · intro h; exact ⟨(c,L c x),h,rfl⟩
  · by_cases h1 : t = 1
    · subst t
      rw [edge_one]
      simp only [one_ne_zero,false_and,true_and,false_or]
      constructor
      · rintro ⟨a,ha,he⟩
        have heq : a = (τ c,R c x) := Sum.inl.inj he
        exact heq ▸ ha
      · intro h; exact ⟨(τ c,R c x),h,rfl⟩
    · have ht : ∃ z : Inner,t = ⟨z.1,z.2.1.le,z.2.2.le⟩ :=
        ⟨⟨t.1,lt_of_le_of_ne t.2.1 (fun h => h0 (Subtype.ext h.symm)),
          lt_of_le_of_ne t.2.2 (fun h => h1 (Subtype.ext h))⟩,rfl⟩
      obtain ⟨s,rfl⟩ := ht
      rw [edge_inner]
      simp only [h0,h1,false_and,or_self,iff_false]
      rintro ⟨a,_,he⟩
      change (Sum.inl a : Core (C := C) (A := A) (B := B)) = Sum.inr (c,(s,x)) at he
      cases he

lemma base_closedEmbedding : IsClosedEmbedding (fun z : C × A => vertex τ L R z.1 z.2) := by
  apply IsClosedEmbedding.of_continuous_injective_isClosedMap (continuous_vertex τ L R)
    Sum.inl_injective
  intro S hS
  apply (isClosed_iff τ L R _).mpr
  constructor
  · intro c
    have he : (vertex τ L R c) ⁻¹' ((fun z : C × A => vertex τ L R z.1 z.2) '' S) =
        (fun x => (c,x)) ⁻¹' S := by
      ext x
      change (∃ a ∈ S, (Sum.inl a : Space τ L R) = Sum.inl (c,x)) ↔ (c,x) ∈ S
      simp only [Sum.inl.injEq]
      constructor
      · rintro ⟨a,ha,he⟩; cases he; exact ha
      · intro h; exact ⟨(c,x),h,rfl⟩
    rw [he]
    exact hS.preimage (continuous_const.prodMk continuous_id)
  · intro c
    rw [edge_preimage_vertices]
    exact (isClosed_singleton.prod (hS.preimage (continuous_const.prodMk (L c).continuous))).union
      (isClosed_singleton.prod (hS.preimage (continuous_const.prodMk (R c).continuous)))

omit [TopologicalSpace C] [DiscreteTopology C] in
lemma interior_preimage [DecidableEq C] (c d : C) (s : Inner) (x : B) :
    (fun z : I × B => edge τ L R c z.1 z.2) ⁻¹' {interior τ L R d s x} =
      (if c = d then {((⟨s.1,s.2.1.le,s.2.2.le⟩ : I),x)} else ∅ : Set (I × B)) := by
  classical
  ext ⟨t,y⟩
  change edge τ L R c t y = interior τ L R d s x ↔ _
  have hright : (t,y) ∈ (if c = d then {((⟨s.1,s.2.1.le,s.2.2.le⟩ : I),x)} else ∅ : Set (I × B)) ↔
      c = d ∧ t.1 = s.1 ∧ y = x := by
    split_ifs with h
    · simp only [Set.mem_singleton_iff,Prod.mk.injEq,h,true_and]
      exact and_congr Subtype.ext_iff Iff.rfl
    · simp only [Set.mem_empty_iff_false,h,false_and]
  rw [hright]
  by_cases h0 : t = 0
  · subst t
    rw [edge_zero]
    constructor
    · intro h
      change (Sum.inl (c,L c y) : Core (C := C) (A := A) (B := B)) = Sum.inr (d,(s,x)) at h
      cases h
    · rintro ⟨_,h,_⟩; exact False.elim (s.2.1.ne' h.symm)
  · by_cases h1 : t = 1
    · subst t
      rw [edge_one]
      constructor
      · intro h
        change (Sum.inl (τ c,R c y) : Core (C := C) (A := A) (B := B)) = Sum.inr (d,(s,x)) at h
        cases h
      · rintro ⟨_,h,_⟩; exact False.elim (s.2.2.ne h.symm)
    · have ht : ∃ z : Inner,t = ⟨z.1,z.2.1.le,z.2.2.le⟩ :=
        ⟨⟨t.1,lt_of_le_of_ne t.2.1 (fun h => h0 (Subtype.ext h.symm)),
          lt_of_le_of_ne t.2.2 (fun h => h1 (Subtype.ext h))⟩,rfl⟩
      obtain ⟨s',rfl⟩ := ht
      rw [edge_inner]
      constructor
      · intro h
        have he : (c,(s',y)) = (d,(s,x)) := Sum.inr.inj h
        exact ⟨congrArg Prod.fst he,congrArg (fun z => z.2.1.1) he,
          congrArg (fun z => z.2.2) he⟩
      · rintro ⟨rfl,hs,rfl⟩
        have he : s' = s := Subtype.ext hs
        rw [he]
end

section
open Set Topology
open scoped unitInterval
universe u v w z
variable {C : Type u} [TopologicalSpace C] [DiscreteTopology C]
variable {A : Type v} [TopologicalSpace A] {B : Type w} [TopologicalSpace B] [T1Space B]
variable (τ : C → C) (L R : C → C(B,A))

lemma selection_closed {J : Type z} (c : J → C) (hc : Function.Injective c)
    (s : J → Inner) (x : J → B) (S : Set (Space τ L R))
    (hS : S ⊆ Set.range (fun j => interior τ L R (c j) (s j) (x j))) : IsClosed S := by
  classical
  apply (isClosed_iff τ L R S).mpr
  constructor
  · intro d
    have he : (vertex τ L R d) ⁻¹' S = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro a ha
      obtain ⟨j,hj⟩ := hS ha
      change (Sum.inr (c j,(s j,x j)) : Core (C := C) (A := A) (B := B)) = Sum.inl (d,a) at hj
      cases hj
    rw [he]; exact isClosed_empty
  · intro d
    have hfinite : ((fun z : I × B => edge τ L R d z.1 z.2) ⁻¹' S).Finite := by
      by_cases hex : ∃ j,c j = d
      · obtain ⟨j,hj⟩ := hex
        apply (Set.finite_singleton (((⟨(s j).1,(s j).2.1.le,(s j).2.2.le⟩ : I),x j))).subset
        intro z hz
        obtain ⟨i,hi⟩ := hS hz
        have hmem : z ∈ (fun z : I × B => edge τ L R d z.1 z.2) ⁻¹'
            {interior τ L R (c i) (s i) (x i)} := hi.symm
        rw [interior_preimage] at hmem
        split_ifs at hmem with hdi
        · have hij : i = j := hc (hdi.symm.trans hj.symm)
          simpa only [hij] using hmem
        · exact False.elim hmem
      · have he : (fun z : I × B => edge τ L R d z.1 z.2) ⁻¹' S = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro z hz
          obtain ⟨i,hi⟩ := hS hz
          have hmem : z ∈ (fun z : I × B => edge τ L R d z.1 z.2) ⁻¹'
              {interior τ L R (c i) (s i) (x i)} := hi.symm
          rw [interior_preimage,ite_eq_right (fun h => hex ⟨i,h.symm⟩)] at hmem
          exact hmem
        rw [he]; exact Set.finite_empty
    exact hfinite.isClosed

theorem compact_finitely_many_edges {K : Set (Space τ L R)} (hK : IsCompact K) :
    {c : C | ∃ (s : Inner) (x : B), interior τ L R c s x ∈ K}.Finite := by
  classical
  let J := {c : C | ∃ (s : Inner) (x : B), interior τ L R c s x ∈ K}
  let s : J → Inner := fun j => j.2.choose
  let x : J → B := fun j => j.2.choose_spec.choose
  let y : J → Space τ L R := fun j => interior τ L R j.1 (s j) (x j)
  have hyK (j : J) : y j ∈ K := j.2.choose_spec.choose_spec
  have hinj : Function.Injective y := by
    intro i j hij
    apply Subtype.ext
    have he : (i.1,(s i,x i)) = (j.1,(s j,x j)) := Sum.inr.inj hij
    exact congrArg Prod.fst he
  have hall : ∀ S ⊆ Set.range y, IsClosed S :=
    selection_closed τ L R Subtype.val Subtype.val_injective s x
  have hcompact : IsCompact (Set.range y) :=
    hK.of_isClosed_subset (hall _ subset_rfl) (Set.range_subset_iff.mpr hyK)
  have hdiscrete : IsDiscrete (Set.range y) := by
    apply isDiscrete_iff_forall_mem_exists_isClosed.mpr
    intro S hS
    exact ⟨S,hall S hS,Set.inter_eq_left.mpr hS⟩
  have hrange := hcompact.finite hdiscrete
  have : Finite J := (Set.finite_range_iff hinj).mp hrange
  exact Set.toFinite J

omit [T1Space B] in

theorem compact_finitely_many_vertices {K : Set (Space τ L R)} (hK : IsCompact K) :
    {c : C | ∃ x : A,vertex τ L R c x ∈ K}.Finite := by
  have hc : IsCompact ((fun z : C × A => vertex τ L R z.1 z.2) ⁻¹' K) :=
    (base_closedEmbedding τ L R).isProperMap.isCompact_preimage hK
  have hf := (hc.image continuous_fst).finite_of_discrete
  convert hf using 1
  ext c
  constructor
  · rintro ⟨x,hx⟩; exact ⟨(c,x),hx,rfl⟩
  · rintro ⟨⟨d,x⟩,hx,h⟩
    change d = c at h
    subst d; exact ⟨x,hx⟩
end

open Set Topology
open scoped unitInterval
universe u v w
variable {C : Type u} {A : Type v} [TopologicalSpace A] {B : Type w} [TopologicalSpace B]
variable (τ : C → C) (L R : C → C(B,A))

@[simp] lemma vertex_eq_vertex (c d : C) (x y : A) :
    vertex τ L R c x = vertex τ L R d y ↔ c = d ∧ x = y := by
  change (Sum.inl (c,x) : Core (C := C) (A := A) (B := B)) = Sum.inl (d,y) ↔ _
  simp only [Sum.inl.injEq,Prod.mk.injEq]
@[simp] lemma vertex_ne_interior (c d : C) (x : A) (s : Inner) (y : B) :
    vertex τ L R c x ≠ interior τ L R d s y := by
  intro h
  change (Sum.inl (c,x) : Core (C := C) (A := A) (B := B)) = Sum.inr (d,(s,y)) at h
  cases h
@[simp] lemma interior_ne_vertex (c d : C) (s : Inner) (x : B) (y : A) :
    interior τ L R c s x ≠ vertex τ L R d y :=
  (vertex_ne_interior τ L R d c y s x).symm
@[simp] lemma interior_eq_interior (c d : C) (s t : Inner) (x y : B) :
    interior τ L R c s x = interior τ L R d t y ↔ c = d ∧ s = t ∧ x = y := by
  change (Sum.inr (c,(s,x)) : Core (C := C) (A := A) (B := B)) = Sum.inr (d,(t,y)) ↔ _
  simp only [Sum.inr.injEq,Prod.mk.injEq]

lemma edge_eq_vertex (c d : C) (t : I) (x : B) (y : A) :
    edge τ L R c t x = vertex τ L R d y ↔
    (t = 0 ∧ c = d ∧ L c x = y) ∨ (t = 1 ∧ τ c = d ∧ R c x = y) := by
  by_cases h0 : t = 0
  · subst t
    rw [edge_zero,vertex_eq_vertex]
    simp only [true_and,zero_ne_one,false_and,or_false]
  · by_cases h1 : t = 1
    · subst t
      rw [edge_one,vertex_eq_vertex]
      simp only [true_and,one_ne_zero,false_and,false_or]
    · let s : Inner := ⟨t.1,lt_of_le_of_ne t.2.1 (fun h => h0 (Subtype.ext h.symm)),
        lt_of_le_of_ne t.2.2 (fun h => h1 (Subtype.ext h))⟩
      have he : edge τ L R c t x = interior τ L R c s x := edge_inner τ L R c s x
      rw [he]
      simp only [interior_ne_vertex,h0,h1,false_and,or_self]

lemma edgeImage_vertex_slice [DecidableEq C] (c d : C) (S : Set (I × B)) :
    (vertex τ L R d) ⁻¹' ((fun z : I × B => edge τ L R c z.1 z.2) '' S) =
      (if d = c then (L c) '' ((fun x : B => ((0:I),x)) ⁻¹' S) else ∅) ∪
      (if d = τ c then (R c) '' ((fun x : B => ((1:I),x)) ⁻¹' S) else ∅) := by
  classical
  ext y
  change (∃ z ∈ S,edge τ L R c z.1 z.2 = vertex τ L R d y) ↔ _
  constructor
  · rintro ⟨⟨t,x⟩,hx,he⟩
    rcases (edge_eq_vertex τ L R c d t x y).mp he with ⟨rfl,hcd,hx'⟩ | ⟨rfl,hcd,hx'⟩
    · exact Or.inl (by rw [ite_eq_left hcd.symm]; exact ⟨x,hx,hx'⟩)
    · exact Or.inr (by rw [ite_eq_left hcd.symm]; exact ⟨x,hx,hx'⟩)
  · intro h
    rcases h with h|h
    · split_ifs at h with hcd
      · obtain ⟨x,hx,hx'⟩ := h
        exact ⟨(0,x),hx,(edge_eq_vertex τ L R c d 0 x y).mpr (Or.inl ⟨rfl,hcd.symm,hx'⟩)⟩
      · exact False.elim h
    · split_ifs at h with hcd
      · obtain ⟨x,hx,hx'⟩ := h
        exact ⟨(1,x),hx,(edge_eq_vertex τ L R c d 1 x y).mpr (Or.inr ⟨rfl,hcd.symm,hx'⟩)⟩
      · exact False.elim h

lemma edgeImage_vertex_closed (c d : C) (S : Set (I × B)) (hS : IsClosed S)
    (hL : IsClosedMap (L c)) (hR : IsClosedMap (R c)) :
    IsClosed ((vertex τ L R d) ⁻¹' ((fun z : I × B => edge τ L R c z.1 z.2) '' S)) := by
  classical
  rw [edgeImage_vertex_slice]
  apply IsClosed.union
  · split_ifs
    · exact hL _ (hS.preimage (continuous_const.prodMk continuous_id))
    · exact isClosed_empty
  · split_ifs
    · exact hR _ (hS.preimage (continuous_const.prodMk continuous_id))
    · exact isClosed_empty
end UniversalFInfinity.GraphBundle

end

end OAI

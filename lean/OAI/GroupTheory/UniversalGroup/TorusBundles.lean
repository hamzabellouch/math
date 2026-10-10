import OAI.GroupTheory.UniversalGroup.AscendingTorus

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

namespace UniversalFInfinity.Milnor
open Set Topology
universe u v
variable {G : Type u} [Group G] {H : Type v} [Group H]
lemma map_smul (φ : G →* H) (g : G) (x : Space G) :
    map φ id Function.injective_id (g • x) = φ g • map φ id Function.injective_id x := by
  change map φ id Function.injective_id (map (g * ·) id Function.injective_id x) =
    map (φ g * ·) id Function.injective_id (map φ id Function.injective_id x)
  rw [map_comp,map_comp]
  have he : (φ ∘ (g * ·)) = ((φ g * ·) ∘ φ) := funext (map_mul φ g)
  rw [he]
omit [Group G] [Group H] in
lemma map_leftInverse (φ : G → H) (ψ : H → G) (h : Function.LeftInverse ψ φ) :
    Function.LeftInverse (map ψ id Function.injective_id) (map φ id Function.injective_id) := by
  intro x
  rw [map_comp]
  have he : ψ ∘ φ = id := funext h
  rw [he]
  exact map_id x
omit [Group H] in
lemma map_closedEmbedding (φ : G → H) (hφ : Function.Injective φ) :
    IsClosedEmbedding (map φ id Function.injective_id) := by
  obtain ⟨ψ,hψ⟩ := hφ.hasLeftInverse
  exact (map_leftInverse φ ψ hψ).isClosedEmbedding
    (map ψ id Function.injective_id).continuous (map φ id Function.injective_id).continuous

def smulMap (g : G) : C(Space G,Space G) := ⟨(g • ·),continuous_const_smul g⟩
lemma smulMap_closedEmbedding (g : G) : IsClosedEmbedding (smulMap g) := by
  exact (Homeomorph.smul g).isClosedEmbedding
end UniversalFInfinity.Milnor

namespace UniversalFInfinity.TorusGeometry
open Set Topology AscendingTorus
universe u
variable {U : Type u} [Group U] (f : Monoid.End U)

instance cosetTopology : TopologicalSpace (Coset f) := ⊥
instance : DiscreteTopology (Coset f) := ⟨rfl⟩

def transition (c : Coset f) : C(Milnor.Space U,Milnor.Space U) :=
  (Milnor.smulMap (cosetOffset f c)).comp (Milnor.map f id Function.injective_id)
lemma transition_apply (c : Coset f) (x : Milnor.Space U) :
    transition f c x = cosetOffset f c • Milnor.map f id Function.injective_id x := rfl
lemma transition_embedding (hf : Function.Injective f) (c : Coset f) :
    IsClosedEmbedding (transition f c) :=
  (Milnor.smulMap_closedEmbedding _).comp (Milnor.map_closedEmbedding f hf)

abbrev Space := GraphBundle.Space (next f) (fun _ => ContinuousMap.id (Milnor.Space U)) (transition f)
def vertex (c : Coset f) (x : Milnor.Space U) : Space f := GraphBundle.vertex _ _ _ c x

def coordinateAction (g : Torus f) (c : Coset f) : C(Milnor.Space U,Milnor.Space U) :=
  Milnor.smulMap (actionOffset f g c)
lemma coordinateAction_compatible (hf : Function.Injective f) (g : Torus f) (c : Coset f) (x : Milnor.Space U) :
    coordinateAction f g (next f c) (transition f c x) =
      transition f (g • c) (coordinateAction f g c x) := by
  change actionOffset f g (next f c) • (cosetOffset f c • Milnor.map f id Function.injective_id x) =
    cosetOffset f (g • c) • Milnor.map f id Function.injective_id (actionOffset f g c • x)
  calc
    _ = (actionOffset f g (next f c) * cosetOffset f c) •
        Milnor.map f id Function.injective_id x := (mul_smul _ _ _).symm
    _ = (cosetOffset f (g • c) * f (actionOffset f g c)) •
        Milnor.map f id Function.injective_id x :=
      congrArg (fun element : U => element • Milnor.map f id Function.injective_id x)
        (actionOffset_next f hf g c)
    _ = cosetOffset f (g • c) •
        (f (actionOffset f g c) • Milnor.map f id Function.injective_id x) := mul_smul _ _ _
    _ = _ := congrArg (cosetOffset f (g • c) • ·)
      (Milnor.map_smul f (actionOffset f g c) x).symm
lemma coordinateAction_one (hf : Function.Injective f) (c : Coset f) (x : Milnor.Space U) :
    coordinateAction f 1 c x = x := by
  change actionOffset f 1 c • x = x
  rw [actionOffset_one f hf,one_smul]
lemma coordinateAction_mul (hf : Function.Injective f) (g h : Torus f) (c : Coset f) (x : Milnor.Space U) :
    coordinateAction f (g*h) c x = coordinateAction f g (h • c) (coordinateAction f h c x) := by
  change actionOffset f (g*h) c • x = actionOffset f g (h • c) • (actionOffset f h c • x)
  rw [actionOffset_mul f hf,mul_smul]

@[instance_reducible]
def action (hf : Function.Injective f) : MulAction (Torus f) (Space f) :=
  GraphBundle.graphAction (next f) (transition f) (next_smul f) (coordinateAction f)
    (coordinateAction_compatible f hf) (coordinateAction_one f hf) (coordinateAction_mul f hf)

variable [Fact (Function.Injective f)]
local notation "hf" => (Fact.out : Function.Injective f)
local instance : MulAction (Torus f) (Space f) := action f hf
instance action_continuous : ContinuousConstSMul (Torus f) (Space f) :=
  GraphBundle.graphAction_continuous (next f) (transition f) (next_smul f) (coordinateAction f)
    (coordinateAction_compatible f hf) (coordinateAction_one f hf) (coordinateAction_mul f hf)
lemma smul_vertex (g : Torus f) (c : Coset f) (x : Milnor.Space U) :
    g • vertex f c x = vertex f (g • c) (actionOffset f g c • x) := rfl
lemma smul_edge (g : Torus f) (c : Coset f) (t : unitInterval) (x : Milnor.Space U) :
    g • GraphBundle.edge (next f) (fun _ => ContinuousMap.id _) (transition f) c t x =
      GraphBundle.edge (next f) (fun _ => ContinuousMap.id _) (transition f) (g • c) t (actionOffset f g c • x) :=
  GraphBundle.actionMap_edge (next f) (transition f) (next_smul f) (coordinateAction f)
    (coordinateAction_compatible f hf) g c t x
end UniversalFInfinity.TorusGeometry

namespace UniversalFInfinity.GraphBundle

section
open Set Topology
open scoped unitInterval
universe u v w z r
variable {C : Type u} [TopologicalSpace C] [DiscreteTopology C]
variable {A : Type v} [TopologicalSpace A] {B : Type w} [TopologicalSpace B]
variable {A' : Type z} [TopologicalSpace A'] {B' : Type r} [TopologicalSpace B']
variable (τ : C → C) (L R : C → C(B,A)) (L' R' : C → C(B',A'))
variable (i : C(A,A')) (j : C(B,B'))
variable (hL : ∀ c x,i (L c x) = L' c (j x)) (hR : ∀ c x,i (R c x) = R' c (j x))

def inclusionFun : Space τ L R → Space τ L' R' :=
  Sum.map (Prod.map id i) (Prod.map id (Prod.map id j))
omit [TopologicalSpace C] [DiscreteTopology C] in
lemma inclusionFun_vertex (c : C) (x : A) :
    inclusionFun τ L R L' R' i j (vertex τ L R c x) = vertex τ L' R' c (i x) := rfl
omit [TopologicalSpace C] [DiscreteTopology C] in
lemma inclusionFun_interior (c : C) (t : Inner) (x : B) :
    inclusionFun τ L R L' R' i j (interior τ L R c t x) = interior τ L' R' c t (j x) := rfl
include hL hR in
omit [TopologicalSpace C] [DiscreteTopology C] in
lemma inclusionFun_edge (c : C) (t : I) (x : B) :
    inclusionFun τ L R L' R' i j (edge τ L R c t x) = edge τ L' R' c t (j x) := by
  classical
  by_cases h0 : t = 0
  · subst t; rw [edge_zero,edge_zero,inclusionFun_vertex,hL]
  by_cases h1 : t = 1
  · subst t; rw [edge_one,edge_one,inclusionFun_vertex,hR]
  let s : Inner := ⟨t.1,lt_of_le_of_ne t.2.1 (fun h => h0 (Subtype.ext h.symm)),
    lt_of_le_of_ne t.2.2 (fun h => h1 (Subtype.ext h))⟩
  change inclusionFun τ L R L' R' i j (edge τ L R c ⟨s.1,s.2.1.le,s.2.2.le⟩ x) =
    edge τ L' R' c ⟨s.1,s.2.1.le,s.2.2.le⟩ (j x)
  rw [edge_inner,edge_inner]; rfl

def inclusion : C(Space τ L R,Space τ L' R') :=
  ⟨inclusionFun τ L R L' R' i j,(continuous_iff τ L R _).mpr ⟨fun c =>
    (vertexMap τ L' R' c).continuous.comp i.continuous,fun c => by
      have he : (fun p : I × B => inclusionFun τ L R L' R' i j (edge τ L R c p.1 p.2)) =
          (fun p : I × B => edge τ L' R' c p.1 (j p.2)) := funext (fun p => inclusionFun_edge τ L R L' R' i j hL hR c p.1 p.2)
      rw [he]
      exact (edgeMap τ L' R' c).continuous.comp (continuous_fst.prodMk (j.continuous.comp continuous_snd))⟩⟩
lemma inclusion_vertex (c : C) (x : A) :
    inclusion τ L R L' R' i j hL hR (vertex τ L R c x) = vertex τ L' R' c (i x) := rfl
lemma inclusion_interior (c : C) (t : Inner) (x : B) :
    inclusion τ L R L' R' i j hL hR (interior τ L R c t x) = interior τ L' R' c t (j x) := rfl
lemma inclusion_edge (c : C) (t : I) (x : B) :
    inclusion τ L R L' R' i j hL hR (edge τ L R c t x) = edge τ L' R' c t (j x) :=
  inclusionFun_edge τ L R L' R' i j hL hR c t x

lemma inclusion_injective (hi : Function.Injective i) (hj : Function.Injective j) :
    Function.Injective (inclusion τ L R L' R' i j hL hR) :=
  Sum.map_injective.mpr ⟨Function.injective_id.prodMap hi,Function.injective_id.prodMap (Function.injective_id.prodMap hj)⟩

lemma inclusion_vertex_preimage (S : Set (Space τ L R)) (c : C) :
    (vertex τ L' R' c) ⁻¹' (inclusion τ L R L' R' i j hL hR '' S) =
      i '' ((vertex τ L R c) ⁻¹' S) := by
  ext x
  constructor
  · rintro ⟨a,ha,he⟩
    change Core (C := C) (A := A) (B := B) at a
    cases a with
    | inl a =>
      have hh : (a.1,i a.2) = (c,x) := Sum.inl.inj he
      obtain rfl := congrArg Prod.fst hh
      exact ⟨a.2,ha,congrArg Prod.snd hh⟩
    | inr a => cases he
  · rintro ⟨y,hy,rfl⟩; exact ⟨vertex τ L R c y,hy,rfl⟩

lemma inclusion_edge_preimage (S : Set (Space τ L R)) (c : C) :
    (fun p : I × B' => edge τ L' R' c p.1 p.2) ⁻¹' (inclusion τ L R L' R' i j hL hR '' S) =
      ({0} ×ˢ ((L' c) ⁻¹' (i '' ((vertex τ L R c) ⁻¹' S)))) ∪
      ({1} ×ˢ ((R' c) ⁻¹' (i '' ((vertex τ L R (τ c)) ⁻¹' S)))) ∪
      (Prod.map id j '' ((fun p : I × B => edge τ L R c p.1 p.2) ⁻¹' S)) := by
  classical
  ext ⟨t,x⟩
  constructor
  · intro h
    by_cases h0 : t = 0
    · subst t; apply Or.inl; apply Or.inl; refine ⟨rfl,?_⟩
      rw [Set.mem_preimage,edge_zero] at h
      exact (Set.ext_iff.mp (inclusion_vertex_preimage τ L R L' R' i j hL hR S c) _).mp h
    by_cases h1 : t = 1
    · subst t; apply Or.inl; apply Or.inr; refine ⟨rfl,?_⟩
      rw [Set.mem_preimage,edge_one] at h
      exact (Set.ext_iff.mp (inclusion_vertex_preimage τ L R L' R' i j hL hR S (τ c)) _).mp h
    let s : Inner := ⟨t.1,lt_of_le_of_ne t.2.1 (fun h => h0 (Subtype.ext h.symm)),
      lt_of_le_of_ne t.2.2 (fun h => h1 (Subtype.ext h))⟩
    change edge τ L' R' c ⟨s.1,s.2.1.le,s.2.2.le⟩ x ∈ inclusion τ L R L' R' i j hL hR '' S at h
    rw [edge_inner] at h
    obtain ⟨a,ha,he⟩ := h
    change Core (C := C) (A := A) (B := B) at a
    cases a with
    | inl a => cases he
    | inr a =>
      have hh : (a.1,(a.2.1,j a.2.2)) = (c,(s,x)) := Sum.inr.inj he
      have hc : a.1 = c := congrArg Prod.fst hh
      have ht : a.2.1 = s := congrArg (fun p : C × (Inner × B') => p.2.1) hh
      have hx : j a.2.2 = x := congrArg (fun p : C × (Inner × B') => p.2.2) hh
      apply Or.inr
      refine ⟨(t,a.2.2),?_,Prod.ext rfl hx⟩
      change edge τ L R c ⟨s.1,s.2.1.le,s.2.2.le⟩ a.2.2 ∈ S
      rw [edge_inner,←hc,←ht]
      exact ha
  · rintro (h|h)
    · rcases h with h|h
      · have ht : t = 0 := h.1; subst t
        rw [Set.mem_preimage,edge_zero]
        exact (Set.ext_iff.mp (inclusion_vertex_preimage τ L R L' R' i j hL hR S c) _).mpr h.2
      · have ht : t = 1 := h.1; subst t
        rw [Set.mem_preimage,edge_one]
        exact (Set.ext_iff.mp (inclusion_vertex_preimage τ L R L' R' i j hL hR S (τ c)) _).mpr h.2
    · obtain ⟨⟨r,y⟩,hy,he⟩ := h
      have ht : r = t := congrArg Prod.fst he
      have hx : j y = x := congrArg Prod.snd he
      subst t; subst x
      exact ⟨edge τ L R c r y,hy,inclusion_edge τ L R L' R' i j hL hR c r y⟩

lemma inclusion_closedEmbedding (hi : IsClosedEmbedding i) (hj : IsClosedEmbedding j) :
    IsClosedEmbedding (inclusion τ L R L' R' i j hL hR) := by
  apply IsClosedEmbedding.of_continuous_injective_isClosedMap (inclusion τ L R L' R' i j hL hR).continuous
    (inclusion_injective τ L R L' R' i j hL hR hi.injective hj.injective)
  intro S hS
  obtain ⟨hv,he⟩ := (isClosed_iff τ L R S).mp hS
  apply (isClosed_iff τ L' R' _).mpr
  constructor
  · intro c; rw [inclusion_vertex_preimage]; exact hi.isClosedMap _ (hv c)
  · intro c; rw [inclusion_edge_preimage]
    exact ((isClosed_singleton.prod ((hi.isClosedMap _ (hv c)).preimage (L' c).continuous)).union
      (isClosed_singleton.prod ((hi.isClosedMap _ (hv (τ c))).preimage (R' c).continuous))).union
      ((IsClosedEmbedding.prodMap IsClosedEmbedding.id hj).isClosedMap _ (he c))
end

open Set Topology
open scoped unitInterval
universe u v w
variable {C : Type u} [TopologicalSpace C] [DiscreteTopology C]
variable {A : Type v} [TopologicalSpace A] {B : Type w} [TopologicalSpace B] [T1Space B]
variable (τ : C → C) (L R : C → C(B,A))

theorem compact_coordinates (hτ : ∀ c,τ c ≠ c)
    (hL : ∀ c,IsClosedEmbedding (L c)) (hR : ∀ c,IsClosedEmbedding (R c))
    {K : Set (Space τ L R)} (hK : IsCompact K) :
    ∃ (KA : Set A) (KB : Set B), IsCompact KA ∧ IsCompact KB ∧
      (∀ c x,vertex τ L R c x ∈ K → x ∈ KA) ∧
      (∀ c s x,interior τ L R c s x ∈ K → x ∈ KB) := by
  let KA := Prod.snd '' ((fun z : C × A => vertex τ L R z.1 z.2) ⁻¹' K)
  let J := {c : C | ∃ s x,interior τ L R c s x ∈ K}
  let KB := ⋃ c ∈ J, Prod.snd '' ((fun z : I × B => edge τ L R c z.1 z.2) ⁻¹' K)
  have hJ : J.Finite := compact_finitely_many_edges τ L R hK
  have hA : IsCompact KA :=
    ((base_closedEmbedding τ L R).isProperMap.isCompact_preimage hK).image continuous_snd
  have hB : IsCompact KB := by
    apply hJ.isCompact_biUnion
    intro c _
    exact ((edge_closedEmbedding τ L R c (hτ c) (hL c) (hR c)).isProperMap.isCompact_preimage hK).image continuous_snd
  refine ⟨KA,KB,hA,hB,?_,?_⟩
  · intro c x hx
    exact ⟨(c,x),hx,rfl⟩
  · intro c s x hx
    apply Set.mem_iUnion₂.mpr
    refine ⟨c,⟨s,x,hx⟩,?_⟩
    refine ⟨(⟨s.1,s.2.1.le,s.2.2.le⟩,x),?_,rfl⟩
    change edge τ L R c ⟨s.1,s.2.1.le,s.2.2.le⟩ x ∈ K
    rwa [edge_inner]
end UniversalFInfinity.GraphBundle

namespace UniversalFInfinity.TorusGeometry

section
open Set Topology Milnor UniversalFInfinity.Simplicial AscendingTorus
open scoped Classical unitInterval
universe u v
variable {U : Type u} [Group U] (f : Monoid.End U)
local instance (priority := 2000) (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)

def vertexShapes (S : Shapes U) : Shapes U := S ∪ imageShapes f id (basedShapes U S)
lemma vertexShapes_left (S : Shapes U) : S ⊆ vertexShapes f S := Finset.subset_union_left
lemma vertexShapes_map (S : Shapes U) (s : Face (stage U S)) :
    faceImage f id s.1 ∈ stage U (vertexShapes f S) := by
  apply orbitSpan_mono (show imageShapes f id (basedShapes U S) ⊆ basedShapes U (vertexShapes f S) from
    fun x hx => Finset.mem_insert_of_mem (Finset.mem_union_right _ hx))
  exact faceImage_controlled f id Function.injective_id (basedShapes U S) s

def stageForward (S : Shapes U) : C(Milnor.Stage U S,Milnor.Stage U (vertexShapes f S)) :=
  mapC _ _ (Milnor.vertexMap f id) (vertexShapes_map f S)
lemma stageForward_full (S : Shapes U) (x : Milnor.Stage U S) :
    stageFull U (vertexShapes f S) (stageForward f S x) =
      map f id Function.injective_id (stageFull U S x) := rfl

def left (S : Shapes U) : C(Milnor.Stage U S,Milnor.Stage U (vertexShapes f S)) :=
  stageIncl U S (vertexShapes f S) (vertexShapes_left f S)
def right (S : Shapes U) (c : Coset f) : C(Milnor.Stage U S,Milnor.Stage U (vertexShapes f S)) :=
  (stageSmul U (vertexShapes f S) (cosetOffset f c)).comp (stageForward f S)
lemma left_full (S : Shapes U) (_c : Coset f) (x : Milnor.Stage U S) :
    stageFull U (vertexShapes f S) (left f S x) = (ContinuousMap.id (Milnor.Space U)) (stageFull U S x) := rfl
lemma right_full (S : Shapes U) (c : Coset f) (x : Milnor.Stage U S) :
    stageFull U (vertexShapes f S) (right f S c x) = transition f c (stageFull U S x) := rfl

abbrev Stage (S : Shapes U) := GraphBundle.Space (next f) (fun _ => left f S) (right f S)
def stageFull (S : Shapes U) : C(Stage f S,Space f) :=
  GraphBundle.inclusion (next f) (fun _ => left f S) (right f S)
    (fun _ => ContinuousMap.id _) (transition f) (Milnor.stageFull U (vertexShapes f S)) (Milnor.stageFull U S)
    (left_full f S) (right_full f S)
lemma stageFull_closedEmbedding (S : Shapes U) : IsClosedEmbedding (stageFull f S) :=
  GraphBundle.inclusion_closedEmbedding _ _ _ _ _ _ _ _ _
    (Milnor.stageFull_embedding U _) (Milnor.stageFull_embedding U _)
lemma stageFull_vertex (S : Shapes U) (c : Coset f) (x : Milnor.Stage U (vertexShapes f S)) :
    stageFull f S (GraphBundle.vertex _ _ _ c x) = vertex f c (Milnor.stageFull U _ x) := rfl
lemma stageFull_interior (S : Shapes U) (c : Coset f) (t : GraphBundle.Inner) (x : Milnor.Stage U S) :
    stageFull f S (GraphBundle.interior _ _ _ c t x) = GraphBundle.interior _ _ _ c t (Milnor.stageFull U _ x) := rfl
lemma stageFull_edge (S : Shapes U) (c : Coset f) (t : I) (x : Milnor.Stage U S) :
    stageFull f S (GraphBundle.edge _ _ _ c t x) = GraphBundle.edge _ _ _ c t (Milnor.stageFull U _ x) :=
  GraphBundle.inclusion_edge _ _ _ _ _ _ _ _ _ c t x

lemma next_ne (c : Coset f) : next f c ≠ c := by
  intro h
  have he := height_next f c
  rw [h] at he
  omega

theorem compact_controlled (hf : Function.Injective f) {K : Set (Space f)} (hK : IsCompact K) :
    ∃ S : Shapes U, K ⊆ Set.range (stageFull f S) := by
  obtain ⟨KA,KB,hA,hB,hVA,hEB⟩ := GraphBundle.compact_coordinates (next f)
    (fun _ => ContinuousMap.id (Milnor.Space U)) (transition f) (next_ne f)
    (fun _ => IsClosedEmbedding.id) (transition_embedding f hf) hK
  obtain ⟨S,hS⟩ := Milnor.compact_controlled U hA
  obtain ⟨T,hT⟩ := Milnor.compact_controlled U hB
  let R := S ∪ T
  refine ⟨R,?_⟩
  intro x hx
  change GraphBundle.Core (C := Coset f) (A := Milnor.Space U) (B := Milnor.Space U) at x
  cases x with
  | inl x =>
    obtain ⟨y,hy⟩ := hS (hVA x.1 x.2 hx)
    let z := stageIncl U S (vertexShapes f R) (Finset.subset_union_left.trans (vertexShapes_left f R)) y
    exact ⟨GraphBundle.vertex _ _ _ x.1 z,congrArg (vertex f x.1) hy⟩
  | inr x =>
    obtain ⟨y,hy⟩ := hT (hEB x.1 x.2.1 x.2.2 hx)
    let z := stageIncl U T R Finset.subset_union_right y
    exact ⟨GraphBundle.interior _ _ _ x.1 x.2.1 z,
      congrArg (GraphBundle.interior _ _ _ x.1 x.2.1) hy⟩
end

open Set Topology Milnor AscendingTorus
open scoped Classical unitInterval
universe u v
variable {U : Type u} [Group U] (f : Monoid.End U)
variable [Fact (Function.Injective f)]
local notation "hf" => (Fact.out : Function.Injective f)
local instance : MulAction (Torus f) (Space f) := action f hf

lemma stage_range_smul (S : Shapes U) (g : Torus f) {x : Space f}
    (hx : x ∈ Set.range (stageFull f S)) : g • x ∈ Set.range (stageFull f S) := by
  obtain ⟨a,rfl⟩ := hx
  change GraphBundle.Core (C := Coset f) (A := Milnor.Stage U (vertexShapes f S)) (B := Milnor.Stage U S) at a
  cases a with
  | inl a =>
    refine ⟨GraphBundle.vertex _ _ _ (g • a.1) (actionOffset f g a.1 • a.2),?_⟩
    change vertex f (g • a.1) (Milnor.stageFull U _ (actionOffset f g a.1 • a.2)) =
      g • vertex f a.1 (Milnor.stageFull U _ a.2)
    rw [smul_vertex,Milnor.stageFull_smul]
  | inr a =>
    refine ⟨GraphBundle.interior _ _ _ (g • a.1) a.2.1 (actionOffset f g a.1 • a.2.2),?_⟩
    change stageFull f S (GraphBundle.interior (next f) (fun _ => left f S) (right f S)
      (g • a.1) a.2.1 (actionOffset f g a.1 • a.2.2)) =
      g • stageFull f S (GraphBundle.interior (next f) (fun _ => left f S) (right f S) a.1 a.2.1 a.2.2)
    rw [stageFull_interior,stageFull_interior,Milnor.stageFull_smul]
    let t : unitInterval := ⟨a.2.1.1,a.2.1.2.1.le,a.2.1.2.2.le⟩
    have h1 : GraphBundle.interior (next f) (fun _ => ContinuousMap.id (Milnor.Space U)) (transition f)
        a.1 a.2.1 (Milnor.stageFull U _ a.2.2) =
        GraphBundle.edge (next f) (fun _ => ContinuousMap.id (Milnor.Space U)) (transition f)
        a.1 t (Milnor.stageFull U _ a.2.2) := (GraphBundle.edge_inner _ _ _ _ _ _).symm
    rw [h1,smul_edge,GraphBundle.edge_inner]

lemma compact_orbit_controlled {K : Set (Space f)} (hK : IsCompact K) :
    ∃ S : Shapes U, ∀ g : Torus f, (g • ·) '' K ⊆ Set.range (stageFull f S) := by
  obtain ⟨S,hS⟩ := compact_controlled f hf hK
  refine ⟨S,?_⟩
  intro g x hx
  obtain ⟨y,hy,rfl⟩ := hx
  exact stage_range_smul f S g (hS hy)

variable {X : Type v} [TopologicalSpace X] [MulAction (Torus f) X]
lemma equivariant_controlled (hX : Milnor.CompactFundamentalSet (Torus f) (X := X))
    (a : C(X,Space f)) (he : ∀ (g : Torus f) x,a (g • x) = g • a x) :
    ∃ S : Shapes U, Set.range a ⊆ Set.range (stageFull f S) := by
  obtain ⟨K,hK,hcov⟩ := hX
  obtain ⟨S,hS⟩ := compact_orbit_controlled f (hK.image a.continuous)
  refine ⟨S,?_⟩
  rintro _ ⟨x,rfl⟩
  obtain ⟨g,y,hy,rfl⟩ := hcov x
  rw [he]
  exact hS g ⟨a y,⟨y,hy,rfl⟩,rfl⟩

omit [MulAction (Torus f) X] [Fact (Function.Injective f)] in
def factorStage (a : C(X,Space f)) (S : Shapes U)
    (ha : Set.range a ⊆ Set.range (stageFull f S)) : C(X,Stage f S) where
  toFun x := (ha (Set.mem_range_self x)).choose
  continuous_toFun := (stageFull_closedEmbedding f S).isEmbedding.continuous_iff.mpr (by
    convert a.continuous using 1
    funext x
    exact (ha (Set.mem_range_self x)).choose_spec)
omit [MulAction (Torus f) X] [Fact (Function.Injective f)] in
lemma factorStage_spec (a : C(X,Space f)) (S : Shapes U)
    (ha : Set.range a ⊆ Set.range (stageFull f S)) (x : X) :
    stageFull f S (factorStage f a S ha x) = a x := (ha (Set.mem_range_self x)).choose_spec
end UniversalFInfinity.TorusGeometry

end

end OAI

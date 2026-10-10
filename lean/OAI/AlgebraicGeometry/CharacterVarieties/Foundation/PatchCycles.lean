import OAI.AlgebraicGeometry.CharacterVarieties.Foundation.ComplementaryPatches

namespace OAI

noncomputable section
open scoped Classical Matrix

namespace IntegralCharacterVarieties.FiniteCycles
open scoped Classical
variable {α : Type*} (σ : Equiv.Perm α)

/-- A cyclicly ordered embedded boundary polygon. -/
structure Polygon (l : ℕ) where
  positive : 0<l
  side : Fin l ↪ α
  next : ∀ j, σ (side j)=side ⟨(j.val+1)%l,Nat.mod_lt _ positive⟩

namespace Polygon
variable {σ} {l : ℕ} (C : Polygon σ l)
def Support : Set α := Set.range C.side

lemma next_in_support (a : α) : σ a∈C.Support ↔ a∈C.Support := by
  constructor
  · rintro ⟨j,hj⟩
    let i : Fin l := ⟨(j.val+l-1)%l,Nat.mod_lt _ C.positive⟩
    have hstep : (⟨(i.val+1)%l,Nat.mod_lt _ C.positive⟩ : Fin l)=j := by
      apply Fin.ext
      dsimp [i]
      rw [Nat.mod_add_mod,Nat.sub_add_cancel (by have := C.positive; omega),
        Nat.add_mod_right,Nat.mod_eq_of_lt j.isLt]
    refine ⟨i,σ.injective ?_⟩
    rw [C.next,hstep,hj]
  · rintro ⟨j,rfl⟩
    exact ⟨⟨(j.val+1)%l,Nat.mod_lt _ C.positive⟩,(C.next j).symm⟩

/-- Separate this new disk from any old label shared by its working strip coordinates. No occurrence or existing corner transport is changed. -/
noncomputable def separate {F : Type*} (f : α → F) (a : α) : Option F :=
  if a∈C.Support then none else some (f a)

@[simp] lemma separate_none_iff {F : Type*} (f : α → F) (a : α) :
    C.separate f a=none ↔ a∈C.Support := by
  simp [separate]

@[simp] lemma separate_side {F : Type*} (f : α → F) (j : Fin l) :
    C.separate f (C.side j)=none := by
  apply (C.separate_none_iff f _).2
  exact ⟨j,rfl⟩

lemma separate_old {F : Type*} (f : α → F) (a : α) (ha : a∉C.Support) :
    C.separate f a=some (f a) := by simp [separate,ha]

lemma separate_next {F : Type*} (f : α → F) (hf : ∀ a, f (σ a)=f a) (a : α) :
    C.separate f (σ a)=C.separate f a := by
  rw [separate,separate,C.next_in_support,hf]

/-- The new facet's entire boundary side set, not just an embedded subset, is exactly the given polygon. This makes its unique boundary equation available. -/
noncomputable def newSides {F : Type*} (f : α → F) :
    Fin l ≃ {a // C.separate f a=none} where
  toFun j := ⟨C.side j,C.separate_side f j⟩
  invFun a := (C.separate_none_iff f a.val).1 a.property |>.choose
  left_inv j := C.side.injective ((C.separate_none_iff f (C.side j)).1
      (C.separate_side f j)).choose_spec
  right_inv a := Subtype.ext ((C.separate_none_iff f a.val).1 a.property).choose_spec

end Polygon
end IntegralCharacterVarieties.FiniteCycles

namespace IntegralCharacterVarieties.FiniteCycles
open scoped Classical
variable {α : Type*} {σ : Equiv.Perm α}

/-- Lexicographic subdivision of a cyclic polygon by routed blocks. -/
def blockPolygon {m n : ℕ} (hm : 0 < m) (f : (Fin m × Fin (n+1)) ↪ α)
    (step : ∀ t (i : Fin n), σ (f (t,i.castSucc))=f (t,i.succ))
    (wrap : ∀ t, σ (f (t,Fin.last n))=f (⟨(t.val+1)% m,Nat.mod_lt _ hm⟩,0)) :
    Polygon σ (m*(n+1)) where
  positive := Nat.mul_pos hm (Nat.succ_pos n)
  side := finProdFinEquiv.symm.toEmbedding.trans f
  next j := by
    obtain ⟨⟨t,i⟩,rfl⟩ := (finProdFinEquiv (m:=m) (n:=n+1)).surjective j
    simp only [Function.Embedding.trans_apply,Equiv.toEmbedding_apply,Equiv.symm_apply_apply]
    refine Fin.lastCases ?_ (fun i => ?_) i
    · rw [wrap]
      congr 1
      apply finProdFinEquiv.injective
      rw [Equiv.apply_symm_apply]
      apply Fin.ext
      simp only [finProdFinEquiv_apply_val,Fin.val_zero,Fin.val_last,zero_add]
      have he : n+(n+1)*t.val+1=(n+1)*(t.val+1) := by ring
      rw [he,Nat.mul_comm m (n+1),Nat.mul_mod_mul_left]
    · rw [step]
      congr 1
      apply finProdFinEquiv.injective
      rw [Equiv.apply_symm_apply]
      apply Fin.ext
      simp only [finProdFinEquiv_apply_val,Fin.val_succ,Fin.val_castSucc]
      have hlt := (finProdFinEquiv (t,i.succ)).isLt
      simp only [finProdFinEquiv_apply_val,Fin.val_succ] at hlt
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
end IntegralCharacterVarieties.FiniteCycles

namespace IntegralCharacterVarieties.OccurrenceIncidence
open scoped Classical
open VertexTable
namespace PortPatch.ParentPath
variable {T : Type} {V I A B : T → Type} {k : (t : T) → V t → Kind}
variable (P : (t : T) → PortPatch (k t) (I t) (A t) (B t))
variable (e : ((t : T) × A t) ≃ ((t : T) × B t))
variable (he : ∀ a, (familyKind k ((PortPatch.family P).minus (.inr (e a))).val.1).arity
      ((PortPatch.family P).minus (.inr (e a))).val.2 =
      (familyKind k ((PortPatch.family P).plus (.inr a)).val.1).arity
      ((PortPatch.family P).plus (.inr a)).val.2)
variable {t : T} {n : ℕ} {a : A t} {b : B t} (C : ParentPath (P t) n a b)

lemma inner_side (i : Fin n) :
    ((PortPatch.family P).complete e he).sideOf (familyEnd k t (C.node i.succ))=
      ⟨(PortPatch.family P).plus (.inl ⟨t,C.seam i⟩),none⟩ := by
  apply sideNumber_injective
  rw [PortWiring.sideOf_number]
  have hp : (⟨⟨t,(C.node i.succ).1⟩,(C.node i.succ).2.1⟩ : LocalPort _ (familyKind k))=
      ((PortPatch.family P).plus (.inl ⟨t,C.seam i⟩)).val :=
    congrArg (fun p : LocalPort (V t) (k t) => (⟨⟨t,p.1⟩,p.2⟩ : LocalPort _ (familyKind k))) (C.plus_port i)
  dsimp only [familyEnd,sideNumber]
  rw [C.parent,hp]
  exact congrArg (fun z => (z.1,(none : Option ℕ)))
    (((PortPatch.family P).complete e he).endOf_portAt
      ((PortPatch.family P).plus (.inl ⟨t,C.seam i⟩),true))

end PortPatch.ParentPath
namespace PortPatch
variable {T : Type} {I A : T → Type} {n : ℕ}

def routeSeam (a : (t : T) → A t) (s : (t : T) → Fin n → I t)
    (ti : T × Fin (n+1)) : ((t : T) × I t) ⊕ ((t : T) × A t) :=
  Fin.cases (.inr ⟨ti.1,a ti.1⟩) (fun i => .inl ⟨ti.1,s ti.1 i⟩) ti.2

lemma routeSeam_injective (a : (t : T) → A t) (s : (t : T) → Fin n → I t)
    (hs : ∀ t,Function.Injective (s t)) : Function.Injective (routeSeam a s) := by
  rintro ⟨t,i⟩ ⟨u,j⟩ hh
  revert hh
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    intro hh
  · have htu : t=u := (Sigma.mk.inj_iff.mp (Sum.inr.inj hh)).1
    subst u
    rfl
  · cases hh
  · cases hh
  · have hh := Sigma.mk.inj_iff.mp (Sum.inl.inj hh)
    have htu : t=u := hh.1
    subst u
    have hij : i=j := hs t (eq_of_heq hh.2)
    subst j
    rfl

namespace ParentPath
variable {m n : ℕ} {V I A B : Fin m → Type} {k : (t : Fin m) → V t → Kind}
variable (P : (t : Fin m) → PortPatch (k t) (I t) (A t) (B t))
variable (e : ((t : Fin m) × A t) ≃ ((t : Fin m) × B t))
variable (he : ∀ a, (familyKind k ((family P).minus (.inr (e a))).val.1).arity
      ((family P).minus (.inr (e a))).val.2 =
      (familyKind k ((family P).plus (.inr a)).val.1).arity ((family P).plus (.inr a)).val.2)
variable {a : (t : Fin m) → A t} {b : (t : Fin m) → B t}
variable (C : (t : Fin m) → ParentPath (P t) n (a t) (b t))

lemma route_side (t : Fin m) (j : Fin (n+1)) :
    ((family P).complete e he).sideOf (familyEnd k t ((C t).node j))=
      ⟨(family P).plus (routeSeam a (fun t => (C t).seam) (t,j)),none⟩ := by
  refine Fin.cases ?_ (fun i => ?_) j
  · exact (C t).first_side P e he
  · exact (C t).inner_side P e he i

lemma route_sides_injective (hs : ∀ t, Function.Injective (C t).seam) :
    Function.Injective (fun ti : Fin m × Fin (n+1) =>
      ((family P).complete e he).sideOf (familyEnd k ti.1 ((C ti.1).node ti.2))) := by
  intro ti uj hh
  have hh := congrArg Sigma.fst hh
  dsimp only at hh
  rw [route_side P e he C,route_side P e he C] at hh
  exact routeSeam_injective a (fun t => (C t).seam) hs ((family P).plus.injective hh)

variable {F : Type}
variable (facet : Side ((family P).complete e he).Seam ((family P).complete e he).seamArity → F)
variable (hc : ∀ x, facet (((family P).complete e he).sideOf (localMate x))=
  facet (((family P).complete e he).sideOf x))

/-- A cycle of patch routes is an embedded polygon for the boundary permutation. There is no extra topological closure hypothesis. -/
def cyclicPolygon (hm : 0 < m) (hs : ∀ t, Function.Injective (C t).seam)
    (route : ∀ t, e.symm ⟨t,b t⟩=⟨⟨(t.val+1)%m,Nat.mod_lt _ hm⟩,
      a ⟨(t.val+1)%m,Nat.mod_lt _ hm⟩⟩) :
    IntegralCharacterVarieties.FiniteCycles.Polygon
      (((family P).complete e he).assemble facet hc).vertexAssembly.corners.boundaryNext
      (m*(n+1)) :=
  IntegralCharacterVarieties.FiniteCycles.blockPolygon hm
    ⟨(fun ti => ((family P).complete e he).sideOf (familyEnd k ti.1 ((C ti.1).node ti.2))),
      route_sides_injective P e he C hs⟩
    (fun t i => (C t).boundary_step P e he facet hc i)
    (fun t => by
      change (((family P).complete e he).assemble facet hc).vertexAssembly.corners.boundaryNext
        (((family P).complete e he).sideOf (familyEnd k t ((C t).node (Fin.last n))))=_
      rw [PortWiring.boundaryNext_local]
      · rw [familyEnd_mate,(C t).last_side P e he,route t]
        exact ((C _).first_side P e he).symm
      · change (k t ((C t).node (Fin.last n)).1).table.endpoint ((C t).node (Fin.last n)).2.1=
          ((C t).node (Fin.last n)).2.2.isNone
        rw [(C t).parent,(C t).positive]
        rfl)
end ParentPath
end PortPatch
end IntegralCharacterVarieties.OccurrenceIncidence

namespace IntegralCharacterVarieties.OccurrenceIncidence.ComplementaryPatch
open scoped Classical
open VertexTable

lemma uParentPath_seam_injective : Function.Injective uParentPath.seam := by
  intro i j hh
  fin_cases i <;> fin_cases j <;> first | rfl | cases hh
lemma qParentPath_seam_injective : Function.Injective qParentPath.seam := by
  intro i j hh
  fin_cases i <;> fin_cases j <;> first | rfl | cases hh

/-- Exhaustive local topological description of the U boundary. No child of a whole port can be confused with its parent even at a self-incidence. -/
lemma u_parent_exhaustive (x : LocalEnd Vertex kind)
    (hx : (decoration x.1).color x.2=.U) :
    ∃ j : Fin 3, x=uParentPath.node j ∨ x=localMate (uParentPath.node j) := by
  rcases x with ⟨v,p,c⟩
  cases v <;> cases p <;> cases c with
  | none => first
    | exact ⟨0,Or.inl rfl⟩
    | exact ⟨0,Or.inr rfl⟩
    | exact ⟨1,Or.inl rfl⟩
    | exact ⟨1,Or.inr rfl⟩
    | exact ⟨2,Or.inl rfl⟩
    | exact ⟨2,Or.inr rfl⟩
    | cases hx
  | some j =>
    dsimp only [kind,Kind.table,reverse,split,splitChild,Passage.table,passage] at j
    fin_cases j <;> cases hx

lemma q_parent_exhaustive (x : LocalEnd Vertex kind)
    (hx : (decoration x.1).color x.2=.Q) :
    ∃ j : Fin 3, x=qParentPath.node j ∨ x=localMate (qParentPath.node j) := by
  rcases x with ⟨v,p,c⟩
  cases v <;> cases p <;> cases c with
  | none => first
    | exact ⟨0,Or.inl rfl⟩
    | exact ⟨0,Or.inr rfl⟩
    | exact ⟨1,Or.inl rfl⟩
    | exact ⟨1,Or.inr rfl⟩
    | exact ⟨2,Or.inl rfl⟩
    | exact ⟨2,Or.inr rfl⟩
    | cases hx
  | some j =>
    dsimp only [kind,Kind.table,reverse,split,splitChild,Passage.table,passage] at j
    fin_cases j <;> cases hx

end IntegralCharacterVarieties.OccurrenceIncidence.ComplementaryPatch

namespace IntegralCharacterVarieties.FiniteCycles
open scoped Classical
variable {α : Type} [Finite α] {σ : Equiv.Perm α} {l : ℕ}
namespace Polygon
variable (C : Polygon σ l)

def start : Fin l := ⟨0,C.positive⟩

omit [Finite α] in
lemma iterate_side (j : Fin l) (n : ℕ) :
    (σ^[n]) (C.side j)=C.side ⟨(j.val+n)%l,Nat.mod_lt _ C.positive⟩ := by
  induction n with
  | zero => simp only [Function.iterate_zero,Function.id_def,Nat.add_zero,Nat.mod_eq_of_lt j.isLt]
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih,C.next]
    congr 1
    apply Fin.ext
    exact Nat.mod_add_mod _ _ _

omit [Finite α] in
lemma side_sameCycle (i j : Fin l) : σ.SameCycle (C.side i) (C.side j) := by
  have h : (σ^[j.val+l-i.val]) (C.side i)=C.side j := by
    rw [C.iterate_side]
    congr 1
    apply Fin.ext
    have he : i.val+(j.val+l-i.val)=j.val+l := by have := i.isLt; omega
    change (i.val+(j.val+l-i.val))%l=j.val
    rw [he,Nat.add_mod_right,Nat.mod_eq_of_lt j.isLt]
  exact ⟨(j.val+l-i.val : ℕ),by simpa only [zpow_natCast,Equiv.Perm.coe_pow] using h⟩

/-- Its separated new-facet label has only one orbit; this identifies the ENTIRE new facet boundary, in an arbitrary sewn global occurrence diagram. -/
noncomputable def newComponent {F : Type} (f : α → F) :
    FacetComponents σ (C.separate f) none :=
  ⟨Quotient.mk (Equiv.Perm.SameCycle.setoid σ) (C.side C.start),by
    change C.separate f (representative σ _)=none
    apply (C.separate_none_iff f _).2
    have hc : σ.SameCycle (representative σ
      (Quotient.mk (Equiv.Perm.SameCycle.setoid σ) (C.side C.start))) (C.side C.start) :=
      Quotient.exact (Quotient.out_eq
        (Quotient.mk (Equiv.Perm.SameCycle.setoid σ) (C.side C.start)))
    obtain ⟨n,hn⟩ := hc.symm.exists_nat_pow_eq
    exact ⟨⟨(C.start.val+n)%l,Nat.mod_lt _ C.positive⟩,(C.iterate_side C.start n).symm.trans hn⟩⟩

lemma newComponent_unique {F : Type} (f : α → F)
    (c : FacetComponents σ (C.separate f) none) : c=C.newComponent f := by
  apply Subtype.ext
  have hc : C.separate f (representative σ c.val)=none := c.property
  obtain ⟨j,hj⟩ := (C.separate_none_iff f _).1 hc
  change c.val=Quotient.mk (Equiv.Perm.SameCycle.setoid σ) (C.side C.start)
  calc
    c.val=Quotient.mk (Equiv.Perm.SameCycle.setoid σ) (representative σ c.val) :=
      (Quotient.out_eq c.val).symm
    _=Quotient.mk (Equiv.Perm.SameCycle.setoid σ) (C.side C.start) := by
      rw [← hj]
      exact Quotient.sound (C.side_sameCycle j C.start)

noncomputable def newComponents {F : Type} (f : α → F) :
    Unit ≃ FacetComponents σ (C.separate f) none where
  toFun _ := C.newComponent f
  invFun _ := ()
  left_inv _ := rfl
  right_inv c := (C.newComponent_unique f c).symm

theorem new_boundary_count {F : Type} (f : α → F) :
    componentCount σ (C.separate f) none=1 := by
  change Nat.card (FacetComponents σ (C.separate f) none)=1
  rw [← Nat.card_congr (C.newComponents f)]
  simp
end Polygon
end IntegralCharacterVarieties.FiniteCycles

namespace IntegralCharacterVarieties.FiniteCycles
open scoped Classical
namespace Polygon
variable {α : Type} [Finite α] {σ : Equiv.Perm α} {l : ℕ} (C : Polygon σ l)

/-- An exhaustive polygon determines the entire named facet boundary, not merely a cycle inside it. This does not change any original side label. -/
theorem componentCount_of_support {F : Type} (f : α → F) (u : F)
    (h : ∀ z, z∈C.Support ↔ f z=u) : componentCount σ f u=1 := by
  let e : FacetComponents σ f u ≃ FacetComponents σ (C.separate f) none :=
    Equiv.subtypeEquivProp (funext (fun c => propext (((C.separate_none_iff f _).trans (h _)).symm)))
  change Nat.card (FacetComponents σ f u)=1
  rw [Nat.card_congr e]
  exact C.new_boundary_count f
end Polygon
end IntegralCharacterVarieties.FiniteCycles

namespace IntegralCharacterVarieties.OccurrenceIncidence
open scoped Classical
open VertexTable
namespace PortWiring
variable {V : Type} {k : V → Kind} (W : PortWiring k)
lemma sideOf_surjective : Function.Surjective W.sideOf := by
  let A := W.assemble (fun _ => ()) (fun _ => rfl)
  intro z
  let x := A.realize.symm (z,true)
  refine ⟨x,?_⟩
  have h := W.realize_assemble (fun _ => ()) (fun _ => rfl) x
  have hx : A.realize x=(z,true) := A.realize.apply_symm_apply _
  change A.realize x=_ at h
  rw [hx] at h
  exact (congrArg Prod.fst h).symm
end PortWiring
end IntegralCharacterVarieties.OccurrenceIncidence

namespace IntegralCharacterVarieties.OccurrenceIncidence.ComplementaryPatch
open scoped Classical
open VertexTable
namespace Cyclic
variable {m : ℕ}
abbrev patches : (t : Fin m) → PortPatch kind (Fin 10) (Fin 4) (Fin 4) := fun _ => patch
abbrev colors := familyDecoration (fun _ : Fin m => decoration)
variable (e : ((_ : Fin m) × Fin 4) ≃ ((_ : Fin m) × Fin 4))
variable (he : ∀ a, (familyKind (fun _ : Fin m => kind) ((PortPatch.family patches).minus (.inr (e a))).val.1).arity
      ((PortPatch.family patches).minus (.inr (e a))).val.2 =
      (familyKind (fun _ : Fin m => kind) ((PortPatch.family patches).plus (.inr a)).val.1).arity
      ((PortPatch.family patches).plus (.inr a)).val.2)
abbrev wiring := (PortPatch.family patches).complete e he
variable (hd : (wiring e he).ColorCompatible (colors (m:=m)))
abbrev assembly := (wiring e he).fromDecoration colors hd

include hd in
lemma color_mate (x) :
    (wiring e he).coloredFacet colors ((wiring e he).sideOf (localMate x))=
      (wiring e he).coloredFacet colors ((wiring e he).sideOf x) := by
  rw [(wiring e he).sideOf_color colors hd,(wiring e he).sideOf_color colors hd]
  exact (colors x.1).corner x.2

variable (hm : 0 < m)
variable (ru : ∀ t : Fin m, e.symm ⟨t,0⟩=⟨⟨(t.val+1)%m,Nat.mod_lt _ hm⟩,0⟩)

def uPolygon : IntegralCharacterVarieties.FiniteCycles.Polygon
    (assembly e he hd).vertexAssembly.corners.boundaryNext (m*3) :=
  PortPatch.ParentPath.cyclicPolygon patches e he (fun _ => uParentPath)
    ((wiring e he).coloredFacet colors) (color_mate e he hd) hm
    (fun _ => uParentPath_seam_injective) ru

lemma u_side (t : Fin m) (j : Fin 3) :
    (uPolygon e he hd hm ru).side (finProdFinEquiv (t,j))=
      (wiring e he).sideOf (familyEnd (fun _ : Fin m => kind) t (uParentPath.node j)) := by
  simp only [uPolygon,PortPatch.ParentPath.cyclicPolygon,FiniteCycles.blockPolygon,
    Function.Embedding.trans_apply,Equiv.toEmbedding_apply,Equiv.symm_apply_apply]
  rfl

lemma u_node_mem (t : Fin m) (j : Fin 3) :
    (wiring e he).sideOf (familyEnd (fun _ : Fin m => kind) t (uParentPath.node j))∈
      (uPolygon e he hd hm ru).Support :=
  ⟨finProdFinEquiv (t,j),u_side e he hd hm ru t j⟩

lemma u_support_color (z) :
    z∈(uPolygon e he hd hm ru).Support ↔ (wiring e he).coloredFacet colors z=.U := by
  constructor
  · rintro ⟨j,rfl⟩
    obtain ⟨⟨t,j⟩,rfl⟩ := (finProdFinEquiv (m:=m) (n:=3)).surjective j
    rw [u_side e he hd hm ru,(wiring e he).sideOf_color colors hd]
    exact parent_path_colors.1 j
  · intro hz
    obtain ⟨⟨⟨t,v⟩,p,c⟩,rfl⟩ := (wiring e he).sideOf_surjective z
    rw [(wiring e he).sideOf_color colors hd] at hz
    change (decoration v).color ⟨p,c⟩=.U at hz
    obtain ⟨j,hj|hj⟩ := u_parent_exhaustive ⟨v,p,c⟩ hz
    · change (wiring e he).sideOf (familyEnd (fun _ : Fin m => kind) t ⟨v,p,c⟩)∈_
      rw [hj]
      exact u_node_mem e he hd hm ru t j
    · change (wiring e he).sideOf (familyEnd (fun _ : Fin m => kind) t ⟨v,p,c⟩)∈_
      rw [hj,← familyEnd_mate]
      have hn := u_node_mem e he hd hm ru t j
      apply ((uPolygon e he hd hm ru).next_in_support _).2 at hn
      dsimp only [assembly,PortWiring.fromDecoration] at hn
      rw [PortWiring.boundaryNext_local] at hn
      · exact hn
      · change (kind (uParentPath.node j).1).table.endpoint (uParentPath.node j).2.1=
          (uParentPath.node j).2.2.isNone
        rw [uParentPath.parent,uParentPath.positive]
        rfl

include hm ru in
/-- The named U facet has exactly one boundary component, with no separation of labels and no unproved disk-topology interface. -/
theorem u_boundary_count : IntegralCharacterVarieties.FiniteCycles.componentCount
    (assembly e he hd).vertexAssembly.corners.boundaryNext
    ((wiring e he).coloredFacet colors) .U=1 :=
  (uPolygon e he hd hm ru).componentCount_of_support _ _ (u_support_color e he hd hm ru)

variable (rq : ∀ t : Fin m, e.symm ⟨t,1⟩=⟨⟨(t.val+1)%m,Nat.mod_lt _ hm⟩,1⟩)

def qPolygon : IntegralCharacterVarieties.FiniteCycles.Polygon
    (assembly e he hd).vertexAssembly.corners.boundaryNext (m*3) :=
  PortPatch.ParentPath.cyclicPolygon patches e he (fun _ => qParentPath)
    ((wiring e he).coloredFacet colors) (color_mate e he hd) hm
    (fun _ => qParentPath_seam_injective) rq

lemma q_side (t : Fin m) (j : Fin 3) :
    (qPolygon e he hd hm rq).side (finProdFinEquiv (t,j))=
      (wiring e he).sideOf (familyEnd (fun _ : Fin m => kind) t (qParentPath.node j)) := by
  simp only [qPolygon,PortPatch.ParentPath.cyclicPolygon,FiniteCycles.blockPolygon,
    Function.Embedding.trans_apply,Equiv.toEmbedding_apply,Equiv.symm_apply_apply]
  rfl

lemma q_node_mem (t : Fin m) (j : Fin 3) :
    (wiring e he).sideOf (familyEnd (fun _ : Fin m => kind) t (qParentPath.node j))∈
      (qPolygon e he hd hm rq).Support :=
  ⟨finProdFinEquiv (t,j),q_side e he hd hm rq t j⟩

lemma q_support_color (z) :
    z∈(qPolygon e he hd hm rq).Support ↔ (wiring e he).coloredFacet colors z=.Q := by
  constructor
  · rintro ⟨j,rfl⟩
    obtain ⟨⟨t,j⟩,rfl⟩ := (finProdFinEquiv (m:=m) (n:=3)).surjective j
    rw [q_side e he hd hm rq,(wiring e he).sideOf_color colors hd]
    exact parent_path_colors.2.1 j
  · intro hz
    obtain ⟨⟨⟨t,v⟩,p,c⟩,rfl⟩ := (wiring e he).sideOf_surjective z
    rw [(wiring e he).sideOf_color colors hd] at hz
    change (decoration v).color ⟨p,c⟩=.Q at hz
    obtain ⟨j,hj|hj⟩ := q_parent_exhaustive ⟨v,p,c⟩ hz
    · change (wiring e he).sideOf (familyEnd (fun _ : Fin m => kind) t ⟨v,p,c⟩)∈_
      rw [hj]
      exact q_node_mem e he hd hm rq t j
    · change (wiring e he).sideOf (familyEnd (fun _ : Fin m => kind) t ⟨v,p,c⟩)∈_
      rw [hj,← familyEnd_mate]
      have hn := q_node_mem e he hd hm rq t j
      apply ((qPolygon e he hd hm rq).next_in_support _).2 at hn
      dsimp only [assembly,PortWiring.fromDecoration] at hn
      rw [PortWiring.boundaryNext_local] at hn
      · exact hn
      · change (kind (qParentPath.node j).1).table.endpoint (qParentPath.node j).2.1=
          (qParentPath.node j).2.2.isNone
        rw [qParentPath.parent,qParentPath.positive]
        rfl

include hm rq in
/-- The named Q facet has exactly one boundary component, with no separation of labels and no unproved disk-topology interface. -/
theorem q_boundary_count : IntegralCharacterVarieties.FiniteCycles.componentCount
    (assembly e he hd).vertexAssembly.corners.boundaryNext
    ((wiring e he).coloredFacet colors) .Q=1 :=
  (qPolygon e he hd hm rq).componentCount_of_support _ _ (q_support_color e he hd hm rq)

end Cyclic
end IntegralCharacterVarieties.OccurrenceIncidence.ComplementaryPatch


namespace IntegralCharacterVarieties.OccurrenceIncidence
open scoped Classical
open VertexTable
namespace VariableGallery
variable {l : ℕ} (kind : Fin (l+1) → Kind)
variable (ha : ∀ j : Fin l, (kind j.castSucc).arity (kind j.castSucc).output=
  (kind j.succ).arity (kind j.succ).input)

/-- Every gallery, including arbitrary splitting/merging and adjacent passages, has its input-to-output parent boundary route. All unconsumed branch ports remain exposed by `patch`; no branch is deleted here. -/
noncomputable def parentPath : PortPatch.ParentPath (patch kind ha) l
    ⟨input kind 0, first_exposed kind⟩
    ⟨output kind (Fin.last l), last_exposed kind⟩ where
  node j := ⟨j,(kind j).input,none⟩
  parent _ := rfl
  parentMate j := by rw [parent_corner kind]
  positive j := (kind j).input_endpoint
  seam := id
  plus_port _ := rfl
  minus_port j := by rw [parent_corner kind]; rfl
  first_port := rfl
  last_port := by rw [parent_corner kind]; rfl

lemma parentPath_seam_injective : Function.Injective (parentPath kind ha).seam :=
  Function.injective_id
end VariableGallery
end IntegralCharacterVarieties.OccurrenceIncidence

namespace IntegralCharacterVarieties.FiniteCycles
open scoped Classical

/-- Unequal-length rows of a cyclic boundary are one permutation orbit. Length is not padded by fictitious vertices or zero-rank blocks. -/
theorem variableCyclic_sameCycle {α : Type} (σ : Equiv.Perm α) {m : ℕ}
    (n : Fin (m+1) → ℕ) (node : (t : Fin (m+1)) → Fin (n t+1) → α)
    (step : ∀ t (j : Fin (n t)), σ (node t j.castSucc)=node t j.succ)
    (wrap : ∀ t, σ (node t (Fin.last (n t)))=
      node ⟨(t.val+1)%(m+1),Nat.mod_lt _ (Nat.succ_pos _)⟩ 0)
    (t : Fin (m+1)) (j : Fin (n t+1)) : σ.SameCycle (node 0 0) (node t j) := by
  have within (t : Fin (m+1)) (j : Fin (n t+1)) :
      (σ^[j.val]) (node t 0)=node t j := by
    refine Fin.induction ?_ (fun i ih => ?_) j
    · rfl
    · simp only [Fin.val_castSucc] at ih
      rw [Fin.val_succ,Function.iterate_succ_apply',ih,step]
  have inner (t : Fin (m+1)) (j : Fin (n t+1)) :
      σ.SameCycle (node t 0) (node t j) :=
    ⟨(j.val : ℕ),by simpa only [zpow_natCast,Equiv.Perm.coe_pow] using within t j⟩
  have outer (t : Fin (m+1)) : σ.SameCycle (node t 0)
      (node ⟨(t.val+1)%(m+1),Nat.mod_lt _ (Nat.succ_pos _)⟩ 0) := by
    refine ⟨(n t+1 : ℕ),?_⟩
    simp only [zpow_natCast,Equiv.Perm.coe_pow]
    rw [Function.iterate_succ_apply']
    have h := within t (Fin.last (n t))
    simp only [Fin.val_last] at h
    rw [h,wrap]
  have row (t : Fin (m+1)) : σ.SameCycle (node 0 0) (node t 0) := by
    refine Fin.induction (.rfl) (fun i ih => ?_) t
    apply ih.trans
    have h := outer i.castSucc
    have hv : (⟨(i.castSucc.val+1)%(m+1),Nat.mod_lt _ (Nat.succ_pos _)⟩ : Fin (m+1))=i.succ := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt i.succ.isLt
    rw [hv] at h
    exact h
  exact (row t).trans (inner t j)

/-- A named facet has one boundary precisely when all its sides belong to the orbit of one of its sides. No new separated labeling is introduced. -/
theorem componentCount_of_connected {α F : Type} [Finite α] (σ : Equiv.Perm α)
    (facet : α → F) (hc : ∀ x, facet (σ x)=facet x) (u : F)
    (x : α) (hx : facet x=u)
    (connected : ∀ y, facet y=u → σ.SameCycle x y) :
    componentCount σ facet u=1 := by
  have fac (a b : α) (h : σ.SameCycle a b) : facet a=facet b := by
    obtain ⟨n,hn⟩ := h.exists_nat_pow_eq
    exact (iterate_facet σ facet hc a n).symm.trans (congrArg facet hn)
  let c : FacetComponents σ facet u :=
    ⟨Quotient.mk (Equiv.Perm.SameCycle.setoid σ) x,by
      change facet (representative σ _)=u
      exact (fac _ x (Quotient.exact (Quotient.out_eq
        (Quotient.mk (Equiv.Perm.SameCycle.setoid σ) x)))).trans hx⟩
  have unique (d : FacetComponents σ facet u) : d=c := by
    apply Subtype.ext
    change d.val=Quotient.mk (Equiv.Perm.SameCycle.setoid σ) x
    rw [← Quotient.out_eq d.val]
    apply Quotient.sound
    exact (connected (representative σ d.val) d.property).symm
  let e : Unit ≃ FacetComponents σ facet u :=
    ⟨fun _ => c,fun _ => (),fun _ => rfl,fun d => (unique d).symm⟩
  change Nat.card (FacetComponents σ facet u)=1
  rw [← Nat.card_congr e]
  simp
end IntegralCharacterVarieties.FiniteCycles

end

end OAI

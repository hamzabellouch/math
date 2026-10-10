import OAI.AlgebraicGeometry.CharacterVarieties.Foundation.SurfacePresentation

namespace OAI

noncomputable section
open scoped Classical Matrix

namespace IntegralCharacterVarieties.FiniteCycles
open scoped Classical
variable {α : Type} [Finite α] (p : Equiv.Perm α)

abbrev Component := Quotient (Equiv.Perm.SameCycle.setoid p)

def representative (c : Component p) : α := c.out

def length (c : Component p) : ℕ := Function.minimalPeriod p (representative p c)

lemma length_pos (c : Component p) : 0 < length p c :=
  Function.minimalPeriod_pos_of_mem_periodicPts (p.injective.mem_periodicPts _)

def entry (c : Component p) (i : Fin (length p c)) : α := (p^[i.val]) (representative p c)

omit [Finite α] in
lemma component_at (c : Component p) (i : Fin (length p c)) :
    Quotient.mk (Equiv.Perm.SameCycle.setoid p) (entry p c i)=c := by
  calc
    Quotient.mk (Equiv.Perm.SameCycle.setoid p) (entry p c i) = Quotient.mk (Equiv.Perm.SameCycle.setoid p) (representative p c) := by
      apply Quotient.sound
      exact (Equiv.Perm.SameCycle.rfl.pow_left)
    _ = c := Quotient.out_eq c

lemma at_next (c : Component p) (i : Fin (length p c)) :
    p (entry p c i)=entry p c ⟨(i.val+1) % length p c,Nat.mod_lt _ (length_pos p c)⟩ := by
  change p ((p^[i.val]) (representative p c)) = (p^[(i.val+1) % length p c]) (representative p c)
  dsimp only [length]
  rw [Function.iterate_mod_minimalPeriod_eq,Function.iterate_succ_apply']

omit [Finite α] in
lemma at_injective (c : Component p) : Function.Injective (entry p c) := by
  intro i j h
  apply Fin.ext
  exact (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod i.isLt j.isLt).mp h

lemma at_surjective (x : α) : ∃ c i, entry p c i=x := by
  let c : Component p := Quotient.mk (Equiv.Perm.SameCycle.setoid p) x
  have hc : p.SameCycle (representative p c) x := Quotient.exact (Quotient.out_eq c)
  obtain ⟨n,hn⟩ := hc.exists_nat_pow_eq
  refine ⟨c,⟨n % length p c,Nat.mod_lt _ (length_pos p c)⟩,?_⟩
  change (p^[n % Function.minimalPeriod p (representative p c)]) (representative p c)=x
  rw [Function.iterate_mod_minimalPeriod_eq]
  exact hn

/-- Every side occurrence appears once, even in self-incidence cycles. -/
def enumeration : ((c : Component p) × Fin (length p c)) ≃ α :=
  Equiv.ofBijective (fun z => entry p z.1 z.2) ⟨by
    rintro ⟨c,i⟩ ⟨d,j⟩ h
    have hcd : c=d := (component_at p c i).symm.trans ((congrArg (Quotient.mk (Equiv.Perm.SameCycle.setoid p)) h).trans (component_at p d j))
    subst d
    exact congrArg (Sigma.mk c) (at_injective p c h),by
    intro x
    obtain ⟨c,i,h⟩ := at_surjective p x
    exact ⟨⟨c,i⟩,h⟩⟩

variable {F : Type} (facet : α → F) (hfacet : ∀ x, facet (p x)=facet x)

include hfacet in
omit [Finite α] in
lemma iterate_facet (x : α) (n : ℕ) : facet ((p^[n]) x)=facet x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',hfacet,ih]

def componentFacet (c : Component p) : F := facet (representative p c)

include hfacet in
omit [Finite α] in
lemma at_facet (c : Component p) (i : Fin (length p c)) :
    facet (entry p c i)=componentFacet p facet c := iterate_facet p facet hfacet _ _

abbrev FacetComponents (f : F) := {c : Component p // componentFacet p facet c=f}

instance finiteComponents : Finite (Component p) := inferInstance
instance finiteFacetComponents (f : F) : Finite (FacetComponents p facet f) := inferInstance

noncomputable def componentCount (f : F) : ℕ := Nat.card (FacetComponents p facet f)
noncomputable def componentIndex (f : F) : Fin (componentCount p facet f) ≃ FacetComponents p facet f :=
  (Finite.equivFin (FacetComponents p facet f)).symm

def boundaryLength (f : F) (b : Fin (componentCount p facet f)) : ℕ :=
  length p (componentIndex p facet f b).val

lemma boundaryLength_pos (f : F) (b : Fin (componentCount p facet f)) :
    0 < boundaryLength p facet f b := length_pos p _

/-- Historical facet labels survive grouping: several cycles may belong to one surface, and a side on that surface can occur any number of times. -/
def facetEnumeration :
    ((f : F) × (b : Fin (componentCount p facet f)) × Fin (boundaryLength p facet f b)) ≃ α :=
  (Equiv.sigmaCongrRight (fun f => Equiv.sigmaCongr (componentIndex p facet f)
    (fun _ => Equiv.refl _))).trans
    ((Equiv.sigmaAssoc (fun (_ : F) (c : FacetComponents p facet _) => Fin (length p c.val))).symm.trans
      ((Equiv.sigmaCongr (Equiv.sigmaFiberEquiv (componentFacet p facet))
        (fun _ => Equiv.refl _)).trans (enumeration p)))

lemma facetEnumeration_apply (f : F) (b : Fin (componentCount p facet f))
    (i : Fin (boundaryLength p facet f b)) :
    facetEnumeration p facet ⟨f,b,i⟩=entry p (componentIndex p facet f b).val i := rfl

include hfacet in
lemma facetEnumeration_facet (f : F) (b : Fin (componentCount p facet f))
    (i : Fin (boundaryLength p facet f b)) :
    facet (facetEnumeration p facet ⟨f,b,i⟩)=f := by
  exact (at_facet p facet hfacet (componentIndex p facet f b).val i).trans
    (componentIndex p facet f b).property

lemma facetEnumeration_next (f : F) (b : Fin (componentCount p facet f))
    (i : Fin (boundaryLength p facet f b)) :
    p (facetEnumeration p facet ⟨f,b,i⟩)=facetEnumeration p facet
      ⟨f,b,⟨(i.val+1) % boundaryLength p facet f b,Nat.mod_lt _ (boundaryLength_pos p facet f b)⟩⟩ :=
  at_next p _ i

end IntegralCharacterVarieties.FiniteCycles
namespace IntegralCharacterVarieties.SurfacePresentation
open scoped Classical
open OccurrenceIncidence

/-- Construct every boundary circle from the oriented corner involution. In particular no boundary-coverage or cyclic-closure premise is imposed on a new rank-reduction diagram. Facet labels may repeat, and closed facets have zero cycles. -/
def fromPorts {F S V : Type} [Finite S] {arity : S → ℕ}
    (A : PortAssembly F S V arity) (rank genus : F → ℕ)
    (h : ∀ s, rank (A.facet ⟨s,none⟩)=∑ j,rank (A.facet ⟨s,some j⟩)) : Diagram F S V arity where
  ports := A
  rank := rank
  seamRank := h
  genus := genus
  boundaryCount := FiniteCycles.componentCount A.vertexAssembly.corners.boundaryNext A.facet
  boundaryLength := FiniteCycles.boundaryLength A.vertexAssembly.corners.boundaryNext A.facet
  boundaryPositive := FiniteCycles.boundaryLength_pos A.vertexAssembly.corners.boundaryNext A.facet
  boundarySide := FiniteCycles.facetEnumeration A.vertexAssembly.corners.boundaryNext A.facet
  boundaryFacet := FiniteCycles.facetEnumeration_facet A.vertexAssembly.corners.boundaryNext A.facet
    A.vertexAssembly.corners.boundaryNext_facet
  boundaryNext := FiniteCycles.facetEnumeration_next A.vertexAssembly.corners.boundaryNext A.facet

/-- The constructor alters no facet labels, numerical ranks, seam ranks or handles. -/
lemma fromPorts_retains {F S V : Type} [Finite S] {arity : S → ℕ}
    (A : PortAssembly F S V arity) (rank genus : F → ℕ)
    (h : ∀ s, rank (A.facet ⟨s,none⟩)=∑ j,rank (A.facet ⟨s,some j⟩)) :
    (fromPorts A rank genus h).ports=A ∧ (fromPorts A rank genus h).rank=rank ∧
      (fromPorts A rank genus h).genus=genus := ⟨rfl,rfl,rfl⟩

/-- Strong occurrence-sensitive coverage, including all self-incidences. -/
lemma fromPorts_boundary_unique {F S V : Type} [Finite S] {arity : S → ℕ}
    (A : PortAssembly F S V arity) (rank genus : F → ℕ)
    (h : ∀ s, rank (A.facet ⟨s,none⟩)=∑ j,rank (A.facet ⟨s,some j⟩)) (a : Side S arity) :
    ∃! z, (fromPorts A rank genus h).boundarySide z=a :=
  (fromPorts A rank genus h).boundarySide.bijective.existsUnique a

end IntegralCharacterVarieties.SurfacePresentation
namespace IntegralCharacterVarieties.OccurrenceIncidence
open scoped Classical
variable {V : Type} (kind : V → VertexTable.Kind)

abbrev PortAt (b : Bool) := {p : LocalPort V kind // (kind p.1).table.endpoint p.2=b}

/-- A wiring joins whole ordered ports of equal arity with opposite endpoint orientations. No side-germ is allowed to migrate to another seam on its own. -/
structure PortWiring where
  wire : PortAt kind true ≃ PortAt kind false
  arity : ∀ p, (kind (wire p).val.1).arity (wire p).val.2=(kind p.val.1).arity p.val.2

namespace PortWiring
variable {kind} (W : PortWiring kind)
abbrev Seam (_W : PortWiring kind) := PortAt kind true

def seamArity (W : PortWiring kind) (s : W.Seam) : ℕ := (kind s.val.1).arity s.val.2

/-- Both ends of each newly assembled seam, with their original local ports. -/
def portAt : W.Seam × Bool → LocalPort V kind
  | (s,true) => s.val
  | (s,false) => (W.wire s).val

def endOf (p : LocalPort V kind) : W.Seam × Bool :=
  if h : (kind p.1).table.endpoint p.2=true then (⟨p,h⟩,true)
  else (W.wire.symm ⟨p,Bool.eq_false_iff.mpr h⟩,false)

lemma portAt_endOf (p : LocalPort V kind) : W.portAt (W.endOf p)=p := by
  unfold endOf
  split_ifs with h
  · rfl
  · change (W.wire (W.wire.symm _)).val=p
    rw [W.wire.apply_symm_apply]

lemma endOf_portAt (e : W.Seam × Bool) : W.endOf (W.portAt e)=e := by
  rcases e with ⟨s,b⟩
  cases b
  · dsimp only [portAt,endOf]
    rw [dite_eq_right (by simpa only [(W.wire s).property] using Bool.false_ne_true)]
    congr 1
    apply W.wire.injective
    rw [W.wire.apply_symm_apply]
  · dsimp only [portAt,endOf]
    rw [dite_eq_left s.property]

def attach : LocalPort V kind ≃ W.Seam × Bool where
  toFun := W.endOf
  invFun := W.portAt
  left_inv := W.portAt_endOf
  right_inv := W.endOf_portAt

lemma endpoint (p : LocalPort V kind) : (W.attach p).2=(kind p.1).table.endpoint p.2 := by
  change (W.endOf p).2=_
  unfold endOf
  split_ifs with h
  · exact h.symm
  · exact (Bool.eq_false_iff.mpr h).symm

lemma count (p : LocalPort V kind) : W.seamArity (W.attach p).1=(kind p.1).arity p.2 := by
  change W.seamArity (W.endOf p).1=_
  unfold endOf
  split_ifs with h
  · rfl
  · have hw := W.arity (W.wire.symm ⟨p,Bool.eq_false_iff.mpr h⟩)
    rw [W.wire.apply_symm_apply] at hw
    exact hw.symm

/-- The side belonging to one local germ after whole-port wiring. -/
def sideOf (x : LocalEnd V kind) : Side W.Seam W.seamArity :=
  ⟨(W.attach ⟨x.1,x.2.1⟩).1,x.2.2.map (fun j =>
    (W.count ⟨x.1,x.2.1⟩).symm ▸ (kind x.1).childEnumeration x.2.1 j)⟩

/-- Gluing constructor. -/
def assemble {F : Type} (facet : Side W.Seam W.seamArity → F)
    (h : ∀ x, facet (W.sideOf (localMate x))=facet (W.sideOf x)) :
    PortAssembly F W.Seam V W.seamArity where
  kind := kind
  attach := W.attach
  endpoint := W.endpoint
  count := W.count
  facet := facet
  facetContinuation := h

lemma assemble_facet {F : Type} (facet : Side W.Seam W.seamArity → F)
    (h : ∀ x, facet (W.sideOf (localMate x))=facet (W.sideOf x)) :
    (W.assemble facet h).facet=facet := rfl

instance finiteSeam [Finite V] : Finite W.Seam := inferInstance
end PortWiring
end IntegralCharacterVarieties.OccurrenceIncidence
namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical
open OccurrenceIncidence
variable {F S V : Type} {arity : S → ℕ} (D : Diagram F S V arity)

/-- Exactly the source normalization: delete zero facets/children and sew identity seams BEFORE closed factors are separated. -/
structure Proper : Prop where
  positive : ∀ f, 0 < D.rank f
  multiChild : ∀ s, 2 ≤ arity s

variable (h : D.Proper)
include h
lemma proper_child_lt (s : S) (j : Fin (arity s)) :
    D.rank (D.ports.facet ⟨s,some j⟩) < D.rank (D.ports.facet ⟨s,none⟩) := by
  rw [D.seamRank]
  let k : Fin (arity s) := if hj : j.val=0 then ⟨1,by have := h.multiChild s; omega⟩ else ⟨0,by omega⟩
  have hkj : k ≠ j := by
    intro he
    have hk := congrArg Fin.val he
    dsimp only [k] at hk
    split_ifs at hk with hj
    · simp only at hk
      omega
    · simp only at hk
      omega
  exact Finset.single_lt_sum (f := fun t => D.rank (D.ports.facet ⟨s,some t⟩))
    hkj (Finset.mem_univ j) (Finset.mem_univ k) (h.positive _)
    (fun _ _ _ => Nat.zero_le _)

/-- Every maximal-rank occurrence is a parent. Repeated occurrences of the same facet are not collapsed: this assertion is made separately for each side. -/
lemma maximal_side_parent {n : ℕ} (hn : ∀ f, D.rank f ≤ n) (a : Side S arity)
    (ha : D.rank (D.ports.facet a)=n) : a.2=none := by
  rcases a with ⟨s,j⟩
  cases j with
  | none => rfl
  | some j =>
    have hl := D.proper_child_lt h s j
    have hu := hn (D.ports.facet ⟨s,none⟩)
    omega

lemma maximal_boundary_parent {n : ℕ} (hn : ∀ f, D.rank f ≤ n) (f : F)
    (hf : D.rank f=n) (b : Fin (D.boundaryCount f)) (i : Fin (D.boundaryLength f b)) :
    (D.boundarySide ⟨f,b,i⟩).2=none :=
  D.maximal_side_parent h hn _ ((congrArg D.rank (D.boundaryFacet f b i)).trans hf)

lemma maximal_local_parent {n : ℕ} (hn : ∀ f, D.rank f ≤ n) (x : LocalEnd V D.ports.kind)
    (hx : D.rank (D.ports.facet (D.portSide ⟨x.1,x.2.1⟩ x.2.2))=n) : x.2.2=none := by
  have hh := D.maximal_side_parent h hn (D.portSide ⟨x.1,x.2.1⟩ x.2.2) hx
  exact Option.map_eq_none_iff.mp hh

/-- At the paired corner of a maximal side the other side is also a parent. Thus branch-child corners cannot occur on the maximal disk boundary. -/
lemma maximal_corner_parents {n : ℕ} (hn : ∀ f, D.rank f ≤ n) (x : LocalEnd V D.ports.kind)
    (hx : D.rank (D.ports.facet (D.portSide ⟨x.1,x.2.1⟩ x.2.2))=n) :
    x.2.2=none ∧ (localMate x).2.2=none := by
  refine ⟨D.maximal_local_parent h hn x hx, D.maximal_local_parent h hn (localMate x) ?_⟩
  rw [D.portFacet_corner x]
  exact hx

end IntegralCharacterVarieties.SurfacePresentation.Diagram
namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable
open scoped Classical

/-- Along a maximal oriented facet this is the incoming parent port. A branch parent at a split is paired to a CHILD, so cannot lie on such a facet. -/
def Kind.principalIn : (k : Kind) → k.table.Port
  | .passage _ _ => false
  | .splitting _ _ _ false => .before
  | .splitting _ _ _ true => .after

def Kind.principalOut : (k : Kind) → k.table.Port
  | .passage _ _ => true
  | .splitting _ _ _ false => .after
  | .splitting _ _ _ true => .before

lemma Kind.principal_endpoint (k : Kind) :
    k.table.endpoint k.principalIn=true ∧ k.table.endpoint k.principalOut=false := by
  cases k with
  | passage m t => exact ⟨rfl,rfl⟩
  | splitting a b c r => cases r <;> exact ⟨rfl,rfl⟩

lemma Kind.principal_mate (k : Kind) :
    k.table.mate ⟨k.principalIn,none⟩=⟨k.principalOut,none⟩ := by
  cases k with
  | passage m t => rfl
  | splitting a b c r => cases r <;> rfl

lemma Kind.principal_unique (k : Kind) (p : k.table.Port)
    (he : k.table.endpoint p=true) (hm : (k.table.mate ⟨p,none⟩).2=none) :
    p=k.principalIn := by
  cases k with
  | passage m t =>
    cases p
    · rfl
    · cases he
  | splitting a b c r =>
    cases r <;> cases p <;>
      simp_all [Kind.table,split,reverse,splitEndpoint,splitMate,Kind.principalIn]

end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable

namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical
open OccurrenceIncidence
variable {F S V : Type} {arity : S → ℕ} (D : Diagram F S V arity)

def localFinish (a : Side S arity) : LocalEnd V D.ports.kind := D.ports.realize.symm (finish a)
def localStart (a : Side S arity) : LocalEnd V D.ports.kind := D.ports.realize.symm (start a)

lemma realize_localFinish (a : Side S arity) : D.ports.realize (D.localFinish a)=finish a :=
  D.ports.realize.apply_symm_apply _
lemma realize_localStart (a : Side S arity) : D.ports.realize (D.localStart a)=start a :=
  D.ports.realize.apply_symm_apply _

lemma localFinish_mate (a : Side S arity) :
    localMate (D.localFinish a)=D.localStart (D.ports.vertexAssembly.corners.boundaryNext a) := by
  apply D.ports.realize.injective
  rw [D.realize_localStart]
  change D.ports.vertexAssembly.corners.mate (finish a)=_
  exact D.ports.vertexAssembly.corners.mate_finish a

lemma maximal_finish_ports (h : D.Proper) {n : ℕ} (hn : ∀ f, D.rank f ≤ n)
    (a : Side S arity) (ha : D.rank (D.ports.facet a)=n) :
    (D.localFinish a).2=⟨(D.ports.kind (D.localFinish a).1).principalIn,none⟩ := by
  have hp := D.maximal_corner_parents h hn (D.localFinish a) (by
    rw [D.portSide_eq,D.realize_localFinish]
    exact ha)
  have he : (D.ports.kind (D.localFinish a).1).table.endpoint (D.localFinish a).2.1=true := by
    rw [← D.ports.realize_endpoint,D.realize_localFinish]
    change positive a=true
    simp [positive,D.maximal_side_parent h hn a ha]
  rcases hx : D.localFinish a with ⟨v,p,c⟩
  rw [hx] at hp he
  rcases hp with ⟨hp,hq⟩
  dsimp only at hp
  subst c
  have hh := (D.ports.kind v).principal_unique p he hq
  subst p
  rfl

/-- Vertex visited after the named interval occurrence. -/
def eventVertex (f : F) (b : Fin (D.boundaryCount f)) (i : Fin (D.boundaryLength f b)) : V :=
  (D.localFinish (D.boundarySide ⟨f,b,i⟩)).1

def nextBoundaryIndex (f : F) (b : Fin (D.boundaryCount f)) (i : Fin (D.boundaryLength f b)) :
    Fin (D.boundaryLength f b) := ⟨(i.val+1)%D.boundaryLength f b,Nat.mod_lt _ (D.boundaryPositive f b)⟩

/-- Both principal parent germs of the event are the ORIGINAL boundary germs. The second equality includes the last-to-first corner of the disk exactly. -/
theorem maximal_event_germs (h : D.Proper) {n : ℕ} (hn : ∀ f, D.rank f ≤ n)
    (f : F) (hf : D.rank f=n) (b : Fin (D.boundaryCount f)) (i : Fin (D.boundaryLength f b)) :
    D.ports.realize ⟨D.eventVertex f b i,(D.ports.kind (D.eventVertex f b i)).principalIn,none⟩ =
      finish (D.boundarySide ⟨f,b,i⟩) ∧
    D.ports.realize ⟨D.eventVertex f b i,(D.ports.kind (D.eventVertex f b i)).principalOut,none⟩ =
      start (D.boundarySide ⟨f,b,D.nextBoundaryIndex f b i⟩) := by
  let a := D.boundarySide ⟨f,b,i⟩
  have ha : D.rank (D.ports.facet a)=n := (congrArg D.rank (D.boundaryFacet f b i)).trans hf
  have hp := D.maximal_finish_ports h hn a ha
  have hx : (⟨D.eventVertex f b i,(D.ports.kind (D.eventVertex f b i)).principalIn,none⟩ :
      LocalEnd V D.ports.kind)=D.localFinish a := by
    exact (congrArg (fun z => (⟨(D.localFinish a).1,z⟩ : LocalEnd V D.ports.kind)) hp.symm).trans
      (Sigma.eta _)
  refine ⟨by rw [hx,D.realize_localFinish],?_⟩
  have hm : localMate (D.localFinish a)=
      ⟨D.eventVertex f b i,(D.ports.kind (D.eventVertex f b i)).principalOut,none⟩ := by
    rw [← hx]
    change (⟨D.eventVertex f b i,
      (D.ports.kind (D.eventVertex f b i)).table.mate ⟨(D.ports.kind (D.eventVertex f b i)).principalIn,none⟩⟩ :
        LocalEnd V D.ports.kind)=_
    rw [VertexTable.Kind.principal_mate]
  rw [← hm,D.localFinish_mate,D.realize_localStart]
  exact congrArg start (D.boundaryNext f b i)

end IntegralCharacterVarieties.SurfacePresentation.Diagram
namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable
open scoped Classical

/-- Facet names are attached to EACH local germ, even when their values repeat. -/
structure Decoration (k : Kind) (F : Type) where
  color : (p : k.table.Port) × Option (k.table.Child p) → F
  corner : ∀ z, color (k.table.mate z)=color z

variable {F : Type}

def passageDecoration {m : ℕ} (t : Passage m) (parent : F) (child : Fin m → F) :
    Decoration (.passage m t) F where
  color z := match z with
    | ⟨_,none⟩ => parent
    | ⟨false,some j⟩ => child j
    | ⟨true,some j⟩ => child (t.permutation.symm j)
  corner z := by
    rcases z with ⟨b,c⟩
    cases b <;> cases c with
    | none => rfl
    | some c => first | exact rfl | exact congrArg child (t.permutation.symm_apply_apply c)

def splitColor {a b c : ℕ} (main big : F) (left : Fin a → F)
    (middle : Fin b → F) (right : Fin c → F) :
    (p : SplitPort) × Option (splitChild (Fin a) (Fin b) (Fin c) p) → F
  | ⟨.before,none⟩ => main
  | ⟨.after,none⟩ => main
  | ⟨.branch,none⟩ => big
  | ⟨.before,some (.inl j)⟩ => left j
  | ⟨.before,some (.inr (.inl _))⟩ => big
  | ⟨.before,some (.inr (.inr j))⟩ => right j
  | ⟨.after,some (.inl j)⟩ => left j
  | ⟨.after,some (.inr (.inl j))⟩ => middle j
  | ⟨.after,some (.inr (.inr j))⟩ => right j
  | ⟨.branch,some j⟩ => middle j

lemma splitColor_corner {a b c : ℕ} (main big : F) (left : Fin a → F)
    (middle : Fin b → F) (right : Fin c → F)
    (z : (p : SplitPort) × Option (splitChild (Fin a) (Fin b) (Fin c) p)) :
    splitColor main big left middle right (splitMate z)=splitColor main big left middle right z := by
  rcases z with ⟨p,c⟩
  cases p <;> cases c with
  | none => rfl
  | some c => first | exact rfl | (rcases c with a|b|c <;> rfl)

def splittingDecoration {a b c : ℕ} (rev : Bool) (main big : F) (left : Fin a → F)
    (middle : Fin b → F) (right : Fin c → F) : Decoration (.splitting a b c rev) F := by
  cases rev
  · exact ⟨splitColor main big left middle right,splitColor_corner main big left middle right⟩
  · exact ⟨splitColor main big left middle right,splitColor_corner main big left middle right⟩

/-- Replacing names uniformly preserves all corner incidences, so a local recipe may be used when several of its named old facets coincide globally. -/
def Decoration.map {k : Kind} {G : Type} (d : Decoration k F) (f : F → G) : Decoration k G where
  color x := f (d.color x)
  corner x := congrArg f (d.corner x)

end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable

end

end OAI

import OAI.AlgebraicGeometry.CharacterVarieties.Foundation.MatrixExpressions

namespace OAI

noncomputable section
open scoped Classical Matrix

namespace IntegralCharacterVarieties.OccurrenceIncidence

/-- A side is an occurrence, not a facet: `none` denotes the parent and `some j` the j-th ordered child. The same facet may appear arbitrarily often. -/
abbrev Side (S : Type*) (arity : S → ℕ) := (s : S) × Option (Fin (arity s))
abbrev Germ (S : Type*) (arity : S → ℕ) := Side S arity × Bool

/-- The positive boundary orientation follows the seam parameter on the parent and goes against it on every child. -/
def positive {S : Type*} {arity : S → ℕ} (a : Side S arity) : Bool := a.2.isNone

def start {S : Type*} {arity : S → ℕ} (a : Side S arity) : Germ S arity := (a,!(positive a))
def finish {S : Type*} {arity : S → ℕ} (a : Side S arity) : Germ S arity := (a,positive a)

/-- Frame-independent incidence data before imposing the allowed vertex tables. Facets and germs stay separate. Corner maps cannot accidentally identify two occurrences merely because they sit on the same facet. -/
structure Corners (F S : Type*) (arity : S → ℕ) where
  facet : Side S arity → F
  mate : Germ S arity → Germ S arity
  involutive : Function.Involutive mate
  sameFacet : ∀ g, facet (mate g).1=facet g.1
  orientation : ∀ g, (mate g).2=positive (mate g).1 ↔ g.2 ≠ positive g.1

namespace Corners
variable {F S : Type*} {arity : S → ℕ} (D : Corners F S arity)

lemma mate_finish (a : Side S arity) :
    D.mate (finish a)=start (D.mate (finish a)).1 := by
  apply Prod.ext
  · rfl
  apply Bool.eq_not_iff.mpr
  intro h
  have hh := (D.orientation (finish a)).mp h
  exact hh rfl

lemma mate_start (a : Side S arity) :
    D.mate (start a)=finish (D.mate (start a)).1 := by
  apply Prod.ext
  · rfl
  apply (D.orientation (start a)).mpr
  exact Bool.eq_not_iff.mp rfl

lemma mate_ne (g : Germ S arity) : D.mate g ≠ g := by
  intro he
  have hh := D.orientation g
  rw [he] at hh
  by_cases h : g.2=positive g.1
  · exact (hh.mp h) h
  · exact h (hh.mpr h)

/-- The next-side permutation of the oriented facet boundaries. All finite cycles, in particular self-incidences and one-side circles, are retained. -/
def boundaryNext : Equiv.Perm (Side S arity) where
  toFun a := (D.mate (finish a)).1
  invFun a := (D.mate (start a)).1
  left_inv a := by
    change (D.mate (start (D.mate (finish a)).1)).1=a
    rw [← D.mate_finish,D.involutive]
    rfl
  right_inv a := by
    change (D.mate (finish (D.mate (start a)).1)).1=a
    rw [← D.mate_start,D.involutive]
    rfl

@[simp] lemma boundaryNext_facet (a : Side S arity) :
    D.facet (D.boundaryNext a)=D.facet a := D.sameFacet (finish a)

@[simp] lemma boundaryPrev_facet (a : Side S arity) :
    D.facet (D.boundaryNext.symm a)=D.facet a := D.sameFacet (start a)

lemma boundaryNext_iterate_facet (a : Side S arity) (n : ℕ) :
    D.facet ((D.boundaryNext^[n]) a)=D.facet a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply',D.boundaryNext_facet,ih]

/-- Distinct side-germ occurrences never collapse under the boundary successor, even when all of their facets coincide. -/
theorem occurrence_preserved (a b : Side S arity) :
    D.boundaryNext a=D.boundaryNext b ↔ a=b := D.boundaryNext.injective.eq_iff

end Corners
end IntegralCharacterVarieties.OccurrenceIncidence
namespace IntegralCharacterVarieties.OccurrenceIncidence
open scoped Classical

/-- One local vertex table. Every endpoint port has its own full ordered side list. A mate is a pairing of occurrences, not an identification of facets. -/
structure VertexTable where
  Port : Type
  Child : Port → Type
  endpoint : Port → Bool
  mate : ((p : Port) × Option (Child p)) → ((p : Port) × Option (Child p))
  involutive : Function.Involutive mate
  orientation : ∀ s, (endpoint (mate s).1=(mate s).2.isNone) ↔
    endpoint s.1 ≠ s.2.isNone

namespace VertexTable
/-- A continuation or interchange has precisely two ports. -/
def passage {C : Type} (σ : Equiv.Perm C) : VertexTable where
  Port := Bool
  Child := fun _ => C
  endpoint := Bool.not
  mate := fun ⟨b,c⟩ => ⟨!b,if b then c.map σ.symm else c.map σ⟩
  involutive := by
    rintro ⟨b,c⟩
    cases b <;> cases c <;> simp
  orientation := by
    rintro ⟨b,c⟩
    cases b <;> cases c <;> simp

/-- Only these two passage permutations are allowed in a surface diagram. An arbitrary permutation is factored into several vertices, never one vertex. -/
inductive Passage (m : ℕ) where
  | continuation
  | interchange (i : Fin (m-1))

namespace Passage
variable {m : ℕ}
def permutation : Passage m → Equiv.Perm (Fin m)
  | .continuation => Equiv.refl _
  | .interchange i => Equiv.swap ⟨i.val,by omega⟩ ⟨i.val+1,by omega⟩

def table (t : Passage m) : VertexTable := passage t.permutation
end Passage

inductive SplitPort where | before | after | branch
  deriving DecidableEq

/-- Ordered child lists: prefix, the split block, suffix; and then prefix, its ordered subblocks, suffix. The third seam carries just those subblocks. -/
def splitChild (A B C : Type) : SplitPort → Type
  | .before => A ⊕ (Unit ⊕ C)
  | .after => A ⊕ (B ⊕ C)
  | .branch => B

/-- Germ matching at a split. In particular the child W and the parent W are different occurrences; each subblock is also used twice, not collapsed. -/
def splitMate {A B C : Type} : ((p : SplitPort) × Option (splitChild A B C p)) →
    ((p : SplitPort) × Option (splitChild A B C p))
  | ⟨.before,none⟩ => ⟨.after,none⟩
  | ⟨.after,none⟩ => ⟨.before,none⟩
  | ⟨.before,some (.inl a)⟩ => ⟨.after,some (.inl a)⟩
  | ⟨.after,some (.inl a)⟩ => ⟨.before,some (.inl a)⟩
  | ⟨.before,some (.inr (.inl _))⟩ => ⟨.branch,none⟩
  | ⟨.branch,none⟩ => ⟨.before,some (.inr (.inl ()))⟩
  | ⟨.before,some (.inr (.inr c))⟩ => ⟨.after,some (.inr (.inr c))⟩
  | ⟨.after,some (.inr (.inr c))⟩ => ⟨.before,some (.inr (.inr c))⟩
  | ⟨.after,some (.inr (.inl b))⟩ => ⟨.branch,some b⟩
  | ⟨.branch,some b⟩ => ⟨.after,some (.inr (.inl b))⟩

def splitEndpoint : SplitPort → Bool | .before => true | .after => false | .branch => true

lemma splitMate_involutive {A B C : Type} : Function.Involutive (splitMate (A:=A) (B:=B) (C:=C)) := by
  rintro ⟨p,c⟩
  cases p <;> cases c with
  | none => rfl
  | some c =>
    first | exact rfl | (rcases c with a|b|c <;> rfl)

lemma splitMate_orientation {A B C : Type} (s : (p : SplitPort) × Option (splitChild A B C p)) :
    (splitEndpoint (splitMate s).1=(splitMate s).2.isNone) ↔
      splitEndpoint s.1 ≠ s.2.isNone := by
  rcases s with ⟨p,c⟩
  cases p <;> cases c with
  | none => simp [splitEndpoint,splitMate,Option.isNone]
  | some c =>
    first | (solve | simp [splitEndpoint,splitMate,Option.isNone]) |
      (rcases c with a|b|c <;> simp [splitEndpoint,splitMate,Option.isNone])

/-- A split or its orientation-reversed merge, with all three port lists. -/
def split (A B C : Type) : VertexTable where
  Port := SplitPort
  Child := splitChild A B C
  endpoint := splitEndpoint
  mate := splitMate
  involutive := splitMate_involutive
  orientation := splitMate_orientation

/-- Reversal changes every seam endpoint, and nothing in the occurrence table. -/
def reverse (t : VertexTable) : VertexTable where
  Port := t.Port
  Child := t.Child
  endpoint p := !(t.endpoint p)
  mate := t.mate
  involutive := t.involutive
  orientation s := by
    have h := t.orientation s
    cases he : t.endpoint (t.mate s).1 <;>
      cases hp : (t.mate s).2.isNone <;>
      cases hf : t.endpoint s.1 <;>
      cases hq : s.2.isNone <;> simp_all

/-- Every local table is fixed-point free for occurrences, even when a facet is attached to several of the ports. -/
lemma mate_ne (t : VertexTable) (s : (p : t.Port) × Option (t.Child p)) : t.mate s ≠ s := by
  intro h
  have ho := t.orientation s
  rw [h] at ho
  by_cases e : t.endpoint s.1=s.2.isNone
  · exact ho.mp e e
  · exact e (ho.mpr e)

end VertexTable
end IntegralCharacterVarieties.OccurrenceIncidence
namespace IntegralCharacterVarieties.OccurrenceIncidence
open scoped Classical
namespace VertexTable

def splitPortEquiv : SplitPort ≃ Fin 3 where
  toFun | .before => 0 | .after => 1 | .branch => 2
  invFun i := if i=0 then .before else if i=1 then .after else .branch
  left_inv p := by cases p <;> rfl
  right_inv i := by fin_cases i <;> rfl

instance : Fintype SplitPort := Fintype.ofEquiv (Fin 3) splitPortEquiv.symm

/-- Exactly the allowed vertex list, including reversal of splitting. The nonnegative numbers include every zero block before normalization. -/
inductive Kind where
  | passage (m : ℕ) (t : Passage m)
  | splitting (a b c : ℕ) (rev : Bool)

def Kind.table : Kind → VertexTable
  | .passage _ t => t.table
  | .splitting a b c false => split (Fin a) (Fin b) (Fin c)
  | .splitting a b c true => (split (Fin a) (Fin b) (Fin c)).reverse

instance finitePort (k : Kind) : Finite k.table.Port := by
  rcases k with ⟨m,t⟩|⟨a,b,c,r⟩
  · change Finite Bool
    infer_instance
  · cases r <;> change Finite SplitPort <;> infer_instance

instance finiteChild (k : Kind) (p : k.table.Port) : Finite (k.table.Child p) := by
  rcases k with ⟨m,t⟩|⟨a,b,c,r⟩
  · change Finite (Fin m)
    infer_instance
  · cases r <;> cases p <;> dsimp [Kind.table,split,reverse,splitChild] <;> infer_instance
end VertexTable

/-- Local endpoint occurrences at permitted vertices. -/
abbrev LocalEnd (V : Type) (kind : V → VertexTable.Kind) :=
  (v : V) × (p : (kind v).table.Port) × Option ((kind v).table.Child p)

def localMate {V : Type} {kind : V → VertexTable.Kind} (x : LocalEnd V kind) : LocalEnd V kind :=
  ⟨x.1,(kind x.1).table.mate x.2⟩

lemma localMate_involutive {V : Type} {kind : V → VertexTable.Kind} :
    Function.Involutive (localMate (kind:=kind)) := by
  rintro ⟨v,p⟩
  change (⟨v,(kind v).table.mate ((kind v).table.mate p)⟩ : LocalEnd V kind)=⟨v,p⟩
  rw [(kind v).table.involutive]

/-- A finite incidence diagram is specified by a bijection from local ports to global side-germ occurrences. -/
structure VertexAssembly (F S V : Type) (arity : S → ℕ) where
  kind : V → VertexTable.Kind
  realize : LocalEnd V kind ≃ Germ S arity
  endpoint : ∀ x, (realize x).2=(kind x.1).table.endpoint x.2.1
  parent : ∀ x, positive (realize x).1=x.2.2.isNone
  facet : Side S arity → F
  facetContinuation : ∀ x, facet (realize (localMate x)).1=facet (realize x).1

namespace VertexAssembly
variable {F S V : Type} {arity : S → ℕ} (A : VertexAssembly F S V arity)

lemma localOrientation (x : LocalEnd V A.kind) :
    (A.realize (localMate x)).2=positive (A.realize (localMate x)).1 ↔
      (A.realize x).2 ≠ positive (A.realize x).1 := by
  rw [A.endpoint,A.parent,A.endpoint,A.parent]
  exact (A.kind x.1).table.orientation x.2

/-- The global corner involution is constructed from the source vertex tables. -/
def corners : Corners F S arity where
  facet := A.facet
  mate g := A.realize (localMate (A.realize.symm g))
  involutive g := by
    dsimp only
    rw [A.realize.symm_apply_apply,localMate_involutive (A.realize.symm g),
      A.realize.apply_symm_apply]
  sameFacet g := by
    simpa only [A.realize.apply_symm_apply] using A.facetContinuation (A.realize.symm g)
  orientation g := by
    simpa only [A.realize.apply_symm_apply] using A.localOrientation (A.realize.symm g)

/-- Every corner of the constructed diagram is one of the permitted local occurrences, even if all its adjacent sides share the same facet name. -/
lemma corner_local (g : Germ S arity) :
    A.realize.symm (A.corners.mate g)=localMate (A.realize.symm g) :=
  A.realize.symm_apply_apply _

lemma boundary_next_injective (a b : Side S arity) :
    A.corners.boundaryNext a=A.corners.boundaryNext b ↔ a=b :=
  A.corners.occurrence_preserved a b

instance finiteLocalEnd [Finite V] : Finite (LocalEnd V A.kind) := by
  infer_instance

end VertexAssembly
end IntegralCharacterVarieties.OccurrenceIncidence

namespace IntegralCharacterVarieties.OccurrenceIncidence
open scoped Classical
namespace VertexTable

def Kind.arity : (k : Kind) → k.table.Port → ℕ
  | .passage m _, _ => m
  | .splitting a _ c false, .before => a+(1+c)
  | .splitting a b c false, .after => a+(b+c)
  | .splitting _ b _ false, .branch => b
  | .splitting a _ c true, .before => a+(1+c)
  | .splitting a b c true, .after => a+(b+c)
  | .splitting _ b _ true, .branch => b

private def unitFin : Unit ≃ Fin 1 := Fintype.equivFinOfCardEq (by simp)
def beforeEnum (a c : ℕ) : (Fin a ⊕ (Unit ⊕ Fin c)) ≃ Fin (a+(1+c)) :=
  (Equiv.sumCongr (Equiv.refl _) ((Equiv.sumCongr unitFin (Equiv.refl _)).trans
    finSumFinEquiv)).trans finSumFinEquiv
def afterEnum (a b c : ℕ) : (Fin a ⊕ (Fin b ⊕ Fin c)) ≃ Fin (a+(b+c)) :=
  (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv

/-- The source order on each child list: prefix, split block/subblocks, suffix. This is not an arbitrary finite enumeration or an unconstrained germ bijection. -/
def Kind.childEnumeration : (k : Kind) → (p : k.table.Port) →
    k.table.Child p ≃ Fin (k.arity p)
  | .passage _ _, _ => Equiv.refl _
  | .splitting a _ c false, .before => beforeEnum a c
  | .splitting a b c false, .after => afterEnum a b c
  | .splitting _ _ _ false, .branch => Equiv.refl _
  | .splitting a _ c true, .before => beforeEnum a c
  | .splitting a b c true, .after => afterEnum a b c
  | .splitting _ _ _ true, .branch => Equiv.refl _
end VertexTable

abbrev LocalPort (V : Type) (kind : V → VertexTable.Kind) := (v : V) × (kind v).table.Port

/-- Whole ordered ports, rather than unrelated side germs, attach to seam endpoints. This is the finite incidence condition for surface diagrams. -/
structure PortAssembly (F S V : Type) (arity : S → ℕ) where
  kind : V → VertexTable.Kind
  attach : LocalPort V kind ≃ S × Bool
  endpoint : ∀ p, (attach p).2=(kind p.1).table.endpoint p.2
  count : ∀ p, arity (attach p).1=(kind p.1).arity p.2
  facet : Side S arity → F
  facetContinuation : ∀ x : LocalEnd V kind,
    let p : LocalPort V kind := ⟨x.1,x.2.1⟩
    let y := localMate x
    let q : LocalPort V kind := ⟨y.1,y.2.1⟩
    facet ⟨(attach q).1,y.2.2.map (fun z => (count q).symm ▸ ((kind q.1).childEnumeration q.2 z))⟩=
      facet ⟨(attach p).1,x.2.2.map (fun z => (count p).symm ▸ ((kind p.1).childEnumeration p.2 z))⟩

namespace PortAssembly
variable {F S V : Type} {arity : S → ℕ} (A : PortAssembly F S V arity)

def childEquiv (p : LocalPort V A.kind) : (A.kind p.1).table.Child p.2 ≃ Fin (arity (A.attach p).1) :=
  ((A.kind p.1).childEnumeration p.2).trans (finCongr (A.count p).symm)

private def localBundleEquiv : LocalEnd V A.kind ≃
    ((p : LocalPort V A.kind) × Option ((A.kind p.1).table.Child p.2)) where
  toFun x := ⟨⟨x.1,x.2.1⟩,x.2.2⟩
  invFun x := ⟨x.1.1,x.1.2,x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def bundleGermEquiv : ((e : S × Bool) × Option (Fin (arity e.1))) ≃ Germ S arity where
  toFun x := (⟨x.1.1,x.2⟩,x.1.2)
  invFun x := ⟨(x.1.1,x.2),x.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Every germ follows its own port, retaining all repeated facet uses. -/
def realize : LocalEnd V A.kind ≃ Germ S arity :=
  A.localBundleEquiv |>.trans
    (Equiv.sigmaCongr A.attach (fun p => Equiv.optionCongr (A.childEquiv p))) |>.trans bundleGermEquiv

lemma realize_apply (x : LocalEnd V A.kind) :
    A.realize x=(⟨(A.attach ⟨x.1,x.2.1⟩).1,x.2.2.map (A.childEquiv ⟨x.1,x.2.1⟩)⟩,
      (A.attach ⟨x.1,x.2.1⟩).2) := rfl

lemma realize_endpoint (x : LocalEnd V A.kind) :
    (A.realize x).2=(A.kind x.1).table.endpoint x.2.1 := A.endpoint ⟨x.1,x.2.1⟩

lemma realize_parent (x : LocalEnd V A.kind) :
    positive (A.realize x).1=x.2.2.isNone := by
  rw [realize_apply]
  cases x.2.2 <;> rfl

/-- The original corner construction can now be used WITHOUT accidentally scattering a seam's children between unrelated endpoints. -/
def vertexAssembly : VertexAssembly F S V arity where
  kind := A.kind
  realize := A.realize
  endpoint := A.realize_endpoint
  parent := A.realize_parent
  facet := A.facet
  facetContinuation x := by
    have he (p : LocalPort V A.kind) : (A.childEquiv p : _ → _) =
        (fun z => (A.count p).symm ▸ ((A.kind p.1).childEnumeration p.2 z)) := by
      funext z
      exact (show ∀ {n m : ℕ} (h : n=m) (i : Fin n), finCongr h i = h ▸ i from
        fun {n m} h i => by subst m; rfl) (A.count p).symm _
    simpa only [realize_apply,he] using A.facetContinuation x

/-- Port integrity: even the parent and every child of the same port lie at the same global seam endpoint. -/
theorem port_integrity (p : LocalPort V A.kind) (c : Option ((A.kind p.1).table.Child p.2)) :
    ((A.realize ⟨p.1,p.2,c⟩).1.1,(A.realize ⟨p.1,p.2,c⟩).2)=A.attach p := rfl
end PortAssembly
end IntegralCharacterVarieties.OccurrenceIncidence

end

end OAI

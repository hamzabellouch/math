import OAI.AlgebraicGeometry.CharacterVarieties.Cutting.AtomicGallery
import Mathlib.Logic.Equiv.Bool

namespace OAI

/-!
# Doubled bands and grafts of ordered whole-port assemblies.

This formalizes the band reconstruction for filtered surface local systems in
*Integral points on character varieties of curves*.
-/

namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable
open scoped Classical

/-- The orientation reverse is again one of the literal allowed vertices. -/
def Kind.mirror : Kind → Kind
  | .passage m t => .passage m t
  | .splitting a b c r => .splitting a b c (!r)

@[simp] theorem Kind.mirror_mirror (k : Kind) : k.mirror.mirror=k := by
  cases k with
  | passage m t => rfl
  | splitting a b c r => cases r <;> rfl

def Kind.mirrorPort (k : Kind) : k.table.Port ≃ k.mirror.table.Port := by
  cases k with
  | passage m t => exact Equiv.boolNot
  | splitting a b c r => cases r <;> exact Equiv.refl _

def Kind.mirrorChild (k : Kind) (p : k.table.Port) :
    k.table.Child p ≃ k.mirror.table.Child (k.mirrorPort p) := by
  cases k with
  | passage m t => exact Equiv.refl _
  | splitting a b c r => cases r <;> exact Equiv.refl _

def Kind.mirrorEnd (k : Kind) :
    ((p : k.table.Port) × Option (k.table.Child p)) ≃
      ((p : k.mirror.table.Port) × Option (k.mirror.table.Child p)) :=
  Equiv.sigmaCongr k.mirrorPort (fun p => Equiv.optionCongr (k.mirrorChild p))

@[simp] theorem Kind.mirror_endpoint (k : Kind) (p : k.table.Port) :
    k.mirror.table.endpoint (k.mirrorPort p) = !(k.table.endpoint p) := by
  cases k with
  | passage m t => cases p <;> rfl
  | splitting a b c r => cases r <;> cases p <;> rfl

lemma Passage.permutation_symm {m : ℕ} (t : Passage m) :
    t.permutation.symm=t.permutation := by
  cases t with
  | continuation => rfl
  | interchange i => exact Equiv.symm_swap _ _

/-- Reversal preserves every paired child occurrence, including repetitions. -/
lemma Kind.mirror_mate (k : Kind) (x : (p : k.table.Port) × Option (k.table.Child p)) :
    k.mirrorEnd (k.table.mate x) = k.mirror.table.mate (k.mirrorEnd x) := by
  cases k with
  | passage m t =>
    rcases x with ⟨p,c⟩
    cases p <;> cases c <;>
      simp [Kind.mirrorEnd,Kind.mirrorPort,Kind.mirrorChild,Kind.mirror,
        Kind.table,Passage.table,VertexTable.passage,Passage.permutation_symm,
        Equiv.sigmaCongr,Equiv.sigmaCongrLeft,Equiv.sigmaCongrRight] <;> rfl
  | splitting a b c r =>
    cases r <;> rcases x with ⟨p,z⟩ <;> cases p <;> cases z with
    | none => rfl
    | some z => first | rfl | (rcases z with q|q|q <;> rfl)


@[simp] theorem Kind.mirror_arity (k : Kind) (p : k.table.Port) :
    k.mirror.arity (k.mirrorPort p)=k.arity p := by
  cases k with
  | passage m t => rfl
  | splitting a b c r => cases r <;> cases p <;> rfl

lemma Kind.mirror_childEnumeration (k : Kind) (p : k.table.Port) (c : k.table.Child p) :
    k.mirror.childEnumeration (k.mirrorPort p) (k.mirrorChild p c)=
      finCongr (k.mirror_arity p).symm (k.childEnumeration p c) := by
  cases k with
  | passage m t => rfl
  | splitting a b c r => cases r <;> cases p <;> rfl

/-- The mirror uses the same color on the same literal occurrence. -/
def Decoration.mirror {F : Type} {k : Kind} (d : Decoration k F) : Decoration k.mirror F where
  color x := d.color (k.mirrorEnd.symm x)
  corner x := by
    have hm := k.mirror_mate (k.mirrorEnd.symm x)
    rw [k.mirrorEnd.apply_symm_apply] at hm
    rw [← hm,k.mirrorEnd.symm_apply_apply]
    exact d.corner _

@[simp] lemma Decoration.mirror_color {F : Type} {k : Kind} (d : Decoration k F)
    (x : (p : k.table.Port) × Option (k.table.Child p)) :
    d.mirror.color (k.mirrorEnd x)=d.color x := by
  simp [Decoration.mirror]

end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable
namespace IntegralCharacterVarieties.OccurrenceIncidence
open scoped Classical
open VertexTable

variable {V : Type} (kind : V → Kind)

def mirrorKind (v : V) : Kind := (kind v).mirror

def mirrorPortAt (b : Bool) : PortAt kind b ≃ PortAt (mirrorKind kind) (!b) where
  toFun p := ⟨⟨p.val.1,(kind p.val.1).mirrorPort p.val.2⟩,by
    change (kind p.val.1).mirror.table.endpoint ((kind p.val.1).mirrorPort p.val.2)=_
    rw [Kind.mirror_endpoint,p.property]⟩
  invFun p := ⟨⟨p.val.1,(kind p.val.1).mirrorPort.symm p.val.2⟩,by
    have h := (kind p.val.1).mirror_endpoint ((kind p.val.1).mirrorPort.symm p.val.2)
    erw [(kind p.val.1).mirrorPort.apply_symm_apply] at h
    have hp := p.property
    change (kind p.val.1).mirror.table.endpoint p.val.2 = !b at hp
    rw [hp] at h
    simpa only [Bool.not_not] using congrArg Bool.not h.symm⟩
  left_inv p := by apply Subtype.ext; dsimp; congr 1; exact (kind p.val.1).mirrorPort.symm_apply_apply _
  right_inv p := by apply Subtype.ext; dsimp; congr 1; exact (kind p.val.1).mirrorPort.apply_symm_apply _

@[simp] lemma mirrorPortAt_arity (b : Bool) (p : PortAt kind b) :
    (mirrorKind kind (mirrorPortAt kind b p).val.1).arity (mirrorPortAt kind b p).val.2=
      (kind p.val.1).arity p.val.2 := (kind p.val.1).mirror_arity p.val.2

variable {W : Type} (other : W → Kind)

def sumKind : V ⊕ W → Kind := Sum.elim kind other

/-- A disjoint union of vertex sets retains every whole ordered port. -/
def sumPortAt (b : Bool) : PortAt kind b ⊕ PortAt other b ≃ PortAt (sumKind kind other) b where
  toFun
    | .inl p => ⟨⟨.inl p.val.1,p.val.2⟩,p.property⟩
    | .inr p => ⟨⟨.inr p.val.1,p.val.2⟩,p.property⟩
  invFun p := match p.val.1,p.val.2,p.property with
    | .inl v,q,h => .inl ⟨⟨v,q⟩,h⟩
    | .inr w,q,h => .inr ⟨⟨w,q⟩,h⟩
  left_inv p := by cases p <;> rfl
  right_inv p := by rcases p with ⟨⟨v,q⟩,h⟩; cases v <;> rfl

namespace PortPatch
variable {kind other} {I A B : Type} (P : PortPatch kind I A B)

/-- Mirror all internal sewing, without losing any transverse branch port. -/
def mirror : PortPatch (mirrorKind kind) I B A where
  plus := P.minus.trans (mirrorPortAt kind false)
  minus := P.plus.trans (mirrorPortAt kind true)
  internalArity i := by
    change (mirrorKind kind (mirrorPortAt kind true (P.plus (.inl i))).val.1).arity
      (mirrorPortAt kind true (P.plus (.inl i))).val.2 =
      (mirrorKind kind (mirrorPortAt kind false (P.minus (.inl i))).val.1).arity
        (mirrorPortAt kind false (P.minus (.inl i))).val.2
    rw [mirrorPortAt_arity,mirrorPortAt_arity]
    exact (P.internalArity i).symm

/-- Split off ONE genuine short-end from an exhaustive interface; all other
ports remain explicitly enumerated, never silently thrown away. -/
noncomputable def markInterface {T : Type} (t : T) : Unit ⊕ {u : T // u ≠ t} ≃ T where
  toFun | .inl _ => t | .inr u => u.val
  invFun u := if h : u=t then .inl () else .inr ⟨u,h⟩
  left_inv u := by
    cases u with
    | inl u => cases u; simp
    | inr u => simp [u.property]
  right_inv u := by by_cases h : u=t <;> simp [h]

variable {J C E : Type}
/-- Index bookkeeping for the literal doubled patch. The first two summands
are the two longitudinal sewings; the last two are ALL transverse branches. -/
abbrev DoubleInternal (I A B : Type) := (I ⊕ I) ⊕ (A ⊕ B)

def doublePlusIndex : DoubleInternal I A B ⊕ Bool ≃
    (I ⊕ (Unit ⊕ A)) ⊕ (I ⊕ (Unit ⊕ B)) where
  toFun
    | .inl (.inl (.inl i)) => .inl (.inl i)
    | .inl (.inl (.inr i)) => .inr (.inl i)
    | .inl (.inr (.inl a)) => .inl (.inr (.inr a))
    | .inl (.inr (.inr b)) => .inr (.inr (.inr b))
    | .inr false => .inl (.inr (.inl ()))
    | .inr true => .inr (.inr (.inl ()))
  invFun
    | .inl (.inl i) => .inl (.inl (.inl i))
    | .inr (.inl i) => .inl (.inl (.inr i))
    | .inl (.inr (.inr a)) => .inl (.inr (.inl a))
    | .inr (.inr (.inr b)) => .inl (.inr (.inr b))
    | .inl (.inr (.inl _)) => .inr false
    | .inr (.inr (.inl _)) => .inr true
  left_inv x := by rcases x with ((i|i)|(a|b))|b <;> first | rfl | (cases b <;> rfl)
  right_inv x := by rcases x with (i|u|a)|(i|u|b) <;> rfl

def doubleMinusIndex : DoubleInternal I A B ⊕ Bool ≃
    (I ⊕ (Unit ⊕ B)) ⊕ (I ⊕ (Unit ⊕ A)) where
  toFun
    | .inl (.inl (.inl i)) => .inl (.inl i)
    | .inl (.inl (.inr i)) => .inr (.inl i)
    | .inl (.inr (.inl a)) => .inr (.inr (.inr a))
    | .inl (.inr (.inr b)) => .inl (.inr (.inr b))
    | .inr false => .inr (.inr (.inl ()))
    | .inr true => .inl (.inr (.inl ()))
  invFun
    | .inl (.inl i) => .inl (.inl (.inl i))
    | .inr (.inl i) => .inl (.inl (.inr i))
    | .inr (.inr (.inr a)) => .inl (.inr (.inl a))
    | .inl (.inr (.inr b)) => .inl (.inr (.inr b))
    | .inr (.inr (.inl _)) => .inr false
    | .inl (.inr (.inl _)) => .inr true
  left_inv x := by rcases x with ((i|i)|(a|b))|b <;> first | rfl | (cases b <;> rfl)
  right_inv x := by rcases x with (i|u|b)|(i|u|a) <;> rfl

/-- Double an open band and sew every non-short-end interface across the two
copies. Exactly four short ends remain. This is an exhaustive whole-port
construction, not merely a list of proposed endpoints. -/
noncomputable def double (a₀ : A) (b₀ : B) :
    PortPatch (sumKind kind (mirrorKind kind))
      (DoubleInternal I {a : A // a ≠ a₀} {b : B // b ≠ b₀}) Bool Bool := by
  let pa : I ⊕ (Unit ⊕ {a : A // a ≠ a₀}) ≃ PortAt kind true :=
    (Equiv.sumCongr (Equiv.refl I) (markInterface a₀)).trans P.plus
  let pb : I ⊕ (Unit ⊕ {b : B // b ≠ b₀}) ≃ PortAt kind false :=
    (Equiv.sumCongr (Equiv.refl I) (markInterface b₀)).trans P.minus
  let pl := (doublePlusIndex (I:=I) (A:={a : A // a ≠ a₀}) (B:={b : B // b ≠ b₀})).trans
    ((Equiv.sumCongr pa (pb.trans (mirrorPortAt kind false))).trans
      (sumPortAt kind (mirrorKind kind) true))
  let mi := (doubleMinusIndex (I:=I) (A:={a : A // a ≠ a₀}) (B:={b : B // b ≠ b₀})).trans
    ((Equiv.sumCongr pb (pa.trans (mirrorPortAt kind true))).trans
      (sumPortAt kind (mirrorKind kind) false))
  refine ⟨pl,mi,?_⟩
  intro i
  rcases i with (i|i)|(a|b)
  · exact P.internalArity i
  · change (kind (P.plus (.inl i)).val.1).mirror.arity
        ((kind (P.plus (.inl i)).val.1).mirrorPort (P.plus (.inl i)).val.2) =
      (kind (P.minus (.inl i)).val.1).mirror.arity
        ((kind (P.minus (.inl i)).val.1).mirrorPort (P.minus (.inl i)).val.2)
    rw [Kind.mirror_arity,Kind.mirror_arity]
    exact (P.internalArity i).symm
  · exact (kind (P.plus (.inr a.val)).val.1).mirror_arity _
  · exact ((kind (P.minus (.inr b.val)).val.1).mirror_arity _).symm

@[simp] lemma double_plus_short (a₀ : A) (b₀ : B) (b : Bool) :
    (P.double a₀ b₀).plus (.inr b) =
      if b then sumPortAt kind (mirrorKind kind) true (.inr (mirrorPortAt kind false (P.minus (.inr b₀))))
      else sumPortAt kind (mirrorKind kind) true (.inl (P.plus (.inr a₀))) := by
  cases b <;> rfl

@[simp] lemma double_minus_short (a₀ : A) (b₀ : B) (b : Bool) :
    (P.double a₀ b₀).minus (.inr b) =
      if b then sumPortAt kind (mirrorKind kind) false (.inl (P.minus (.inr b₀)))
      else sumPortAt kind (mirrorKind kind) false (.inr (mirrorPortAt kind true (P.plus (.inr a₀)))) := by
  cases b <;> rfl

/-- Identifying matching short ends supplies an honest closed occurrence
assembly; the external matching is itself equal-arity, as required. -/
noncomputable def doubledWiring (a₀ : A) (b₀ : B) : PortWiring (sumKind kind (mirrorKind kind)) :=
  (P.double a₀ b₀).complete (Equiv.refl Bool) (by
    intro b
    cases b
    · exact (kind (P.plus (.inr a₀)).val.1).mirror_arity _
    · exact ((kind (P.minus (.inr b₀)).val.1).mirror_arity _).symm)


end PortPatch
end IntegralCharacterVarieties.OccurrenceIncidence
namespace IntegralCharacterVarieties.OccurrenceIncidence
open scoped Classical
open VertexTable
variable {V F : Type} {kind : V → Kind} (W : PortWiring kind)
    (d : (v : V) → Decoration (kind v) F)

/-- Literal ordered color matching for a whole seam. Repeated names retain
separate coordinates; child reindexing is forced by the seam's arity equality. -/
def PortWiring.ColorMatch : Prop := ∀ (p : W.Seam) (i : Option (Fin (W.seamArity p))),
    (d p.val.1).portColor p.val.2 i =
      (d (W.wire p).val.1).portColor (W.wire p).val.2
        (i.map (finCongr (W.arity p).symm))

noncomputable def PortWiring.seamColor : Side W.Seam W.seamArity → F
  | ⟨p,i⟩ => (d p.val.1).portColor p.val.2 i

lemma portColor_some_congr (p q : LocalPort V kind) (hp : p=q)
    (i : Fin ((kind p.1).arity p.2)) (j : Fin ((kind q.1).arity q.2))
    (hij : i.val=j.val) : (d p.1).portColor p.2 (some i) =
      (d q.1).portColor q.2 (some j) := by
  subst q
  have hi : i=j := Fin.ext hij
  subst j
  rfl

lemma val_transport {a b : ℕ} (h : a=b) (x : Fin a) :
    ((h ▸ x) : Fin b).val=x.val := by cases h; rfl

lemma PortWiring.seamColor_atPort (h : W.ColorMatch d) (p : LocalPort V kind)
    (c : Option ((kind p.1).table.Child p.2)) :
    W.seamColor d (W.sideOf ⟨p.1,p.2,c⟩)=(d p.1).color ⟨p.2,c⟩ := by
  obtain ⟨⟨s,b⟩,rfl⟩ := W.attach.symm.surjective p
  cases b
  · change Option ((kind (W.wire s).val.1).table.Child (W.wire s).val.2) at c
    change W.seamColor d (W.sideOf ⟨(W.wire s).val.1,(W.wire s).val.2,c⟩)=(d (W.wire s).val.1).color ⟨(W.wire s).val.2,c⟩
    have he : W.endOf (W.wire s).val=(s,false) := W.endOf_portAt (s,false)
    cases c with
    | none =>
      have hh := h s none
      change (d s.val.1).color ⟨s.val.2,none⟩ =
        (d (W.wire s).val.1).color ⟨(W.wire s).val.2,none⟩ at hh
      dsimp only [PortWiring.sideOf,PortWiring.seamColor,PortWiring.attach,
        Decoration.portColor,Option.map_none,PortWiring.seamArity,Equiv.coe_fn_mk]
      erw [he]
      exact hh
    | some c =>
      have hh := h s (some (finCongr (W.arity s) ((kind (W.wire s).val.1).childEnumeration
        (W.wire s).val.2 c)))
      change (d s.val.1).portColor s.val.2
          (some (finCongr (W.arity s) ((kind (W.wire s).val.1).childEnumeration (W.wire s).val.2 c))) =
        (d (W.wire s).val.1).portColor (W.wire s).val.2
          (some (finCongr (W.arity s).symm (finCongr (W.arity s)
            ((kind (W.wire s).val.1).childEnumeration (W.wire s).val.2 c)))) at hh
      have hi : finCongr (W.arity s).symm (finCongr (W.arity s)
            ((kind (W.wire s).val.1).childEnumeration (W.wire s).val.2 c)) =
          (kind (W.wire s).val.1).childEnumeration (W.wire s).val.2 c := Fin.ext rfl
      rw [hi,Decoration.portColor_child] at hh
      apply Eq.trans _ hh
      apply portColor_some_congr d _ _
        (congrArg (fun z : W.Seam × Bool => z.1.val) he)
      exact val_transport _ _
  · change Option ((kind s.val.1).table.Child s.val.2) at c
    change W.seamColor d (W.sideOf ⟨s.val.1,s.val.2,c⟩)=(d s.val.1).color ⟨s.val.2,c⟩
    have he : W.endOf s.val=(s,true) := W.endOf_portAt (s,true)
    cases c with
    | none =>
      dsimp only [PortWiring.seamColor,PortWiring.sideOf,Option.map_none,
        PortWiring.attach,Decoration.portColor,Option.map_none,PortWiring.seamArity,Equiv.coe_fn_mk]
      erw [he]
    | some c =>
      apply Eq.trans _ ((d s.val.1).portColor_child s.val.2 c)
      apply portColor_some_congr d _ _
        (congrArg (fun z : W.Seam × Bool => z.1.val) he)
      exact val_transport _ _

lemma PortWiring.seamColor_sideOf (h : W.ColorMatch d) (x : LocalEnd V kind) :
    W.seamColor d (W.sideOf x)=(d x.1).color x.2 :=
  W.seamColor_atPort d h ⟨x.1,x.2.1⟩ x.2.2

/-- Local decorations with proved complete seam matching produce an actual
allowed occurrence assembly, not only rank/port endpoint lists. -/
noncomputable def PortWiring.colored (h : W.ColorMatch d) : PortAssembly F W.Seam V W.seamArity :=
  W.assemble (W.seamColor d) (by
    intro x
    rw [W.seamColor_sideOf d h,W.seamColor_sideOf d h]
    exact (d x.1).corner x.2)

end IntegralCharacterVarieties.OccurrenceIncidence
namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable
open scoped Classical
variable {F : Type} {k : Kind}

noncomputable def Decoration.signature (d : Decoration k F) (p : k.table.Port) : F × List F :=
  (d.portColor p none,d.children p)

lemma Decoration.mirror_portColor (d : Decoration k F) (p : k.table.Port)
    (i : Option (Fin (k.arity p))) :
    d.mirror.portColor (k.mirrorPort p) (i.map (finCongr (k.mirror_arity p).symm))=
      d.portColor p i := by
  cases k with
  | passage m t => cases p <;> cases i <;> rfl
  | splitting a b c r => cases r <;> cases p <;> cases i <;> rfl

@[simp] lemma Decoration.mirror_signature (d : Decoration k F) (p : k.table.Port) :
    d.mirror.signature (k.mirrorPort p)=d.signature p := by
  cases k with
  | passage m t => cases p <;> rfl
  | splitting a b c r => cases r <;> cases p <;> rfl

end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable

namespace IntegralCharacterVarieties.OccurrenceIncidence
open scoped Classical
open VertexTable
variable {V F : Type} {kind : V → Kind} (d : (v : V) → Decoration (kind v) F)

noncomputable def portSignature (p : LocalPort V kind) : F × List F :=
  (d p.1).signature p.2

lemma PortWiring.colorMatch_of_signature (W : PortWiring kind)
    (h : ∀ p,portSignature d p.val=portSignature d (W.wire p).val) : W.ColorMatch d := by
  intro p i
  have hh := h p
  cases i with
  | none => exact congrArg Prod.fst hh
  | some i => exact children_ext _ _ _ _ (congrArg Prod.snd hh) (W.arity p).symm i

variable {I A B : Type} (P : PortPatch kind I A B)

/-- Complete ordered names on each internal whole seam, before closing the
four short-end interfaces. -/
def PortPatch.SignatureMatch : Prop := ∀ i,
  portSignature d (P.plus (.inl i)).val=portSignature d (P.minus (.inl i)).val

lemma PortPatch.complete_colorMatch (e : A ≃ B)
    (ha : ∀ a,(kind (P.minus (.inr (e a))).val.1).arity (P.minus (.inr (e a))).val.2=
      (kind (P.plus (.inr a)).val.1).arity (P.plus (.inr a)).val.2)
    (hi : P.SignatureMatch d)
    (he : ∀ a,portSignature d (P.plus (.inr a)).val=portSignature d (P.minus (.inr (e a))).val) :
    (P.complete e ha).ColorMatch d := by
  apply PortWiring.colorMatch_of_signature
  intro p
  obtain ⟨z,rfl⟩ := P.plus.surjective p
  cases z with
  | inl i => rw [P.complete_internal]; exact hi i
  | inr a => rw [P.complete_external]; exact he a

noncomputable def doubleDecoration : (v : V ⊕ V) → Decoration (sumKind kind (mirrorKind kind) v) F
  | .inl v => d v
  | .inr v => (d v).mirror

@[simp] lemma doubleSignature_left (p : LocalPort V kind) :
    portSignature (doubleDecoration d) ⟨.inl p.1,p.2⟩=portSignature d p := rfl
@[simp] lemma doubleSignature_right (p : LocalPort V kind) :
    portSignature (doubleDecoration d) ⟨.inr p.1,(kind p.1).mirrorPort p.2⟩=portSignature d p :=
  (d p.1).mirror_signature p.2

lemma PortPatch.double_signatureMatch (h : P.SignatureMatch d) (a₀ : A) (b₀ : B) :
    (P.double a₀ b₀).SignatureMatch (doubleDecoration d) := by
  intro i
  rcases i with (i|i)|(a|b)
  · exact h i
  · change (d (P.minus (.inl i)).val.1).mirror.signature
        ((kind (P.minus (.inl i)).val.1).mirrorPort (P.minus (.inl i)).val.2)=
      (d (P.plus (.inl i)).val.1).mirror.signature
        ((kind (P.plus (.inl i)).val.1).mirrorPort (P.plus (.inl i)).val.2)
    simp only [Decoration.mirror_signature]
    exact (h i).symm
  · exact ((d (P.plus (.inr a.val)).val.1).mirror_signature _).symm
  · exact (d (P.minus (.inr b.val)).val.1).mirror_signature _

lemma PortPatch.doubledWiring_colorMatch (h : P.SignatureMatch d) (a₀ : A) (b₀ : B) :
    (P.doubledWiring a₀ b₀).ColorMatch (doubleDecoration d) := by
  apply PortPatch.complete_colorMatch
  · exact P.double_signatureMatch d h a₀ b₀
  · intro b
    cases b
    · exact ((d (P.plus (.inr a₀)).val.1).mirror_signature _).symm
    · exact (d (P.minus (.inr b₀)).val.1).mirror_signature _

end IntegralCharacterVarieties.OccurrenceIncidence
namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable
open scoped Classical
variable {F : Type}

lemma Decoration.signature_eq_of_colors {k l : Kind} (d : Decoration k F) (e : Decoration l F)
    (p : k.table.Port) (q : l.table.Port) (ha : k.arity p=l.arity q)
    (h : ∀ i, d.portColor p i=e.portColor q (i.map (finCongr ha))) :
    d.signature p=e.signature q := by
  apply Prod.ext (h none)
  change List.ofFn (fun i => d.portColor p (some i))=List.ofFn (fun i => e.portColor q (some i))
  rw [List.ofFn_congr ha]
  congr 1
  funext i
  have hi := h (some (finCongr ha.symm i))
  have hh : finCongr ha (finCongr ha.symm i)=i := Fin.ext rfl
  change d.portColor p (some (finCongr ha.symm i))=
    e.portColor q (some (finCongr ha (finCongr ha.symm i))) at hi
  rw [hh] at hi
  exact hi

namespace RealizedBand
variable {parent : F} {a b : List F} (B : RealizedBand parent a b)

lemma patch_signatureMatch : B.patch.SignatureMatch B.decoration := by
  intro i
  change (B.decoration i.succ).signature (B.kind i.succ).input=
    (B.decoration i.castSucc).signature (B.kind i.castSucc).output
  exact (Decoration.signature_eq_of_colors _ _ _ _ (B.arity_match i) (B.color_match i)).symm

noncomputable def shortFirst :=
  (⟨VariableGallery.input B.kind 0,VariableGallery.first_exposed B.kind⟩ :
    {p : PortAt B.kind true // p∉Set.range (VariableGallery.internalPlus B.kind)})
noncomputable def shortLast :=
  (⟨VariableGallery.output B.kind (Fin.last B.length),VariableGallery.last_exposed B.kind⟩ :
    {p : PortAt B.kind false // p∉Set.range (VariableGallery.internalMinus B.kind)})

noncomputable def doublePatch := B.patch.double B.shortFirst B.shortLast
noncomputable def doubleWiring := B.patch.doubledWiring B.shortFirst B.shortLast

lemma double_colorMatch : B.doubleWiring.ColorMatch (doubleDecoration B.decoration) :=
  B.patch.doubledWiring_colorMatch B.decoration B.patch_signatureMatch B.shortFirst B.shortLast

/-- All longitudinal and transverse whole seams are present, with precisely
matching original ordered color occurrences. No independent child-germ
matching is used. Short ends here are closed against their mirror copies;
splicing them into the old exterior remains a separate necessary operation. -/
noncomputable def doubleAssembly : PortAssembly F B.doubleWiring.Seam
    (Fin (B.length+1) ⊕ Fin (B.length+1)) B.doubleWiring.seamArity :=
  B.doubleWiring.colored (doubleDecoration B.decoration) B.double_colorMatch

@[simp] lemma doubleAssembly_color (x : LocalEnd (Fin (B.length+1) ⊕ Fin (B.length+1))
    (sumKind B.kind (mirrorKind B.kind))) :
    B.doubleAssembly.facet (B.doubleWiring.sideOf x)=
      (doubleDecoration B.decoration x.1).color x.2 :=
  B.doubleWiring.seamColor_sideOf _ B.double_colorMatch x

end RealizedBand
end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable
namespace IntegralCharacterVarieties.OccurrenceIncidence
open scoped Classical
open VertexTable
namespace PortAssembly
variable {F S V : Type} {arity : S → ℕ} (A : PortAssembly F S V arity)

/-- Enumerate the genuine ends of the old whole seams. -/
def portAt (b : Bool) : S ≃ PortAt A.kind b where
  toFun s := ⟨A.attach.symm (s,b),by rw [← A.endpoint]; simp⟩
  invFun p := (A.attach p.val).1
  left_inv s := by simp
  right_inv p := by
    apply Subtype.ext
    change A.attach.symm ((A.attach p.val).1,b)=p.val
    have he : ((A.attach p.val).1,b)=A.attach p.val :=
      Prod.ext rfl ((A.endpoint p.val).trans p.property).symm
    rw [he]
    exact A.attach.symm_apply_apply p.val

@[simp] lemma attach_portAt (s : S) (b : Bool) :
    A.attach (A.portAt b s).val=(s,b) := A.attach.apply_symm_apply _

@[simp] lemma portAt_arity (s : S) (b : Bool) :
    (A.kind (A.portAt b s).val.1).arity (A.portAt b s).val.2=arity s := by
  have h := A.count (A.portAt b s).val
  rw [A.attach_portAt] at h
  exact h.symm

/-- Decoration extracted from the actual old incidence, not chosen colors. -/
noncomputable def decoration (v : V) : Decoration (A.kind v) F where
  color x := A.facet (A.realize ⟨v,x⟩).1
  corner x := A.vertexAssembly.facetContinuation ⟨v,x⟩

lemma decoration_portColor (p : LocalPort V A.kind)
    (i : Option (Fin ((A.kind p.1).arity p.2))) :
    (A.decoration p.1).portColor p.2 i=
      A.facet ⟨(A.attach p).1,i.map (finCongr (A.count p).symm)⟩ := by
  cases i with
  | none => rfl
  | some i =>
    change A.facet ⟨(A.attach p).1,some (finCongr (A.count p).symm
      ((A.kind p.1).childEnumeration p.2 ((A.kind p.1).childEnumeration p.2 |>.symm <| i)))⟩=_
    rw [Equiv.apply_symm_apply]
    rfl

noncomputable def seamSignature (s : S) : F × List F :=
  (A.facet ⟨s,none⟩,List.ofFn (fun i => A.facet ⟨s,some i⟩))

lemma decoration_signature (p : LocalPort V A.kind) :
    portSignature A.decoration p=A.seamSignature (A.attach p).1 := by
  apply Prod.ext
  · exact A.decoration_portColor p none
  · change List.ofFn (fun i => (A.decoration p.1).portColor p.2 (some i))=_
    simp_rw [A.decoration_portColor]
    rw [List.ofFn_congr (A.count p).symm]
    rfl

@[simp] lemma portAt_signature (s : S) (b : Bool) :
    portSignature A.decoration (A.portAt b s).val=A.seamSignature s := by
  rw [A.decoration_signature,A.attach_portAt]

end PortAssembly
end IntegralCharacterVarieties.OccurrenceIncidence
namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable
open scoped Classical
variable {F : Type} {k l : Kind}
lemma Decoration.arity_of_signature (d : Decoration k F) (e : Decoration l F)
    {p : k.table.Port} {q : l.table.Port} (h : d.signature p=e.signature q) :
    k.arity p=l.arity q := by
  have hh := congrArg (fun z : F × List F => z.2.length) h
  simpa [Decoration.signature,Decoration.children] using hh
end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable

namespace IntegralCharacterVarieties.OccurrenceIncidence
open scoped Classical
open VertexTable
variable {F S V W I : Type} {arity : S → ℕ}
    (A : PortAssembly F S V arity) {kind : W → Kind}
    (P : PortPatch kind I Bool Bool) (d : (w : W) → Decoration (kind w) F)

noncomputable def graftDecoration : (v : V ⊕ W) → Decoration (sumKind A.kind kind v) F
  | .inl v => A.decoration v
  | .inr w => d w

noncomputable def graftPlus : S ⊕ (I ⊕ Bool) ≃ PortAt (sumKind A.kind kind) true :=
  (Equiv.sumCongr (A.portAt true) P.plus).trans (sumPortAt A.kind kind true)
noncomputable def graftMinus : S ⊕ (I ⊕ Bool) ≃ PortAt (sumKind A.kind kind) false :=
  (Equiv.sumCongr (A.portAt false) P.minus).trans (sumPortAt A.kind kind false)

/-- The SAME seam handle cut has exactly this three-cycle, not identity
closure: the outer ends lengthen its old boundary, and the mirror gallery
self-closes as the new inner boundary. -/
noncomputable def graftCycle (q : S) : Equiv.Perm (S ⊕ (I ⊕ Bool)) :=
  Equiv.swap (.inl q) (.inr (.inr false)) * Equiv.swap (.inl q) (.inr (.inr true))

@[simp] lemma graftCycle_q (q : S) : graftCycle (I:=I) q (.inl q)=.inr (.inr true) := by
  simp [graftCycle,Equiv.Perm.mul_apply,Equiv.swap_apply_def]
@[simp] lemma graftCycle_false (q : S) : graftCycle (I:=I) q (.inr (.inr false))=.inl q := by
  simp [graftCycle,Equiv.Perm.mul_apply,Equiv.swap_apply_def]
@[simp] lemma graftCycle_true (q : S) : graftCycle (I:=I) q (.inr (.inr true))=.inr (.inr false) := by
  simp [graftCycle,Equiv.Perm.mul_apply]
@[simp] lemma graftCycle_internal (q : S) (i : I) :
    graftCycle q (.inr (.inl i))=.inr (.inl i) := by
  simp [graftCycle,Equiv.Perm.mul_apply,Equiv.swap_apply_def]
lemma graftCycle_old (q s : S) (h : s≠q) : graftCycle (I:=I) q (.inl s)=.inl s := by
  simp [graftCycle,Equiv.Perm.mul_apply,Equiv.swap_apply_def,h]

lemma graft_signature (q : S) (hi : P.SignatureMatch d)
    (hp : ∀ b,portSignature d (P.plus (.inr b)).val=A.seamSignature q)
    (hm : ∀ b,portSignature d (P.minus (.inr b)).val=A.seamSignature q)
    (z : S ⊕ (I ⊕ Bool)) :
    portSignature (graftDecoration A d) (graftPlus A P z).val=
      portSignature (graftDecoration A d) (graftMinus A P (graftCycle q z)).val := by
  rcases z with s|(i|b)
  · by_cases hs : s=q
    · subst s
      rw [graftCycle_q]
      change portSignature A.decoration (A.portAt true q).val=portSignature d (P.minus (.inr true)).val
      rw [A.portAt_signature,hm]
    · rw [graftCycle_old q s hs]
      change portSignature A.decoration (A.portAt true s).val=portSignature A.decoration (A.portAt false s).val
      rw [A.portAt_signature,A.portAt_signature]
  · rw [graftCycle_internal]
    exact hi i
  · cases b
    · rw [graftCycle_false]
      change portSignature d (P.plus (.inr false)).val=portSignature A.decoration (A.portAt false q).val
      rw [hp,A.portAt_signature]
    · rw [graftCycle_true]
      exact (hp true).trans (hm false).symm

/-- Literal whole-port inverse-band wiring on the disjoint union of the old
vertices and ALL band vertices. -/
noncomputable def graftWiring (q : S) (hi : P.SignatureMatch d)
    (hp : ∀ b,portSignature d (P.plus (.inr b)).val=A.seamSignature q)
    (hm : ∀ b,portSignature d (P.minus (.inr b)).val=A.seamSignature q) :
    PortWiring (sumKind A.kind kind) where
  wire := (graftPlus A P).symm |>.trans (graftCycle q) |>.trans (graftMinus A P)
  arity p := by
    obtain ⟨z,rfl⟩ := (graftPlus A P).surjective p
    have he : (((graftPlus A P).symm.trans (graftCycle q)).trans (graftMinus A P))
        (graftPlus A P z)=graftMinus A P (graftCycle q z) := by simp
    exact (congrArg (fun p : PortAt (sumKind A.kind kind) false =>
      (sumKind A.kind kind p.val.1).arity p.val.2) he).trans
      (Decoration.arity_of_signature _ _ (graft_signature A P d q hi hp hm z)).symm

lemma graftWiring_colorMatch (q : S) (hi : P.SignatureMatch d)
    (hp : ∀ b,portSignature d (P.plus (.inr b)).val=A.seamSignature q)
    (hm : ∀ b,portSignature d (P.minus (.inr b)).val=A.seamSignature q) :
    (graftWiring A P d q hi hp hm).ColorMatch (graftDecoration A d) := by
  apply PortWiring.colorMatch_of_signature
  intro p
  obtain ⟨z,rfl⟩ := (graftPlus A P).surjective p
  change portSignature _ _=portSignature _ ((graftMinus A P) (graftCycle q ((graftPlus A P).symm ((graftPlus A P) z)))).val
  rw [Equiv.symm_apply_apply]
  exact graft_signature A P d q hi hp hm z

noncomputable def graftAssembly (q : S) (hi : P.SignatureMatch d)
    (hp : ∀ b,portSignature d (P.plus (.inr b)).val=A.seamSignature q)
    (hm : ∀ b,portSignature d (P.minus (.inr b)).val=A.seamSignature q) :=
  (graftWiring A P d q hi hp hm).colored (graftDecoration A d)
    (graftWiring_colorMatch A P d q hi hp hm)

end IntegralCharacterVarieties.OccurrenceIncidence
namespace IntegralCharacterVarieties.OccurrenceIncidence.VertexTable
open scoped Classical
variable {F G : Type}

@[simp] lemma Decoration.map_portColor {k : Kind} (d : Decoration k F) (f : F → G)
    (p : k.table.Port) (i : Option (Fin (k.arity p))) :
    (d.map f).portColor p i=f (d.portColor p i) := rfl
@[simp] lemma Decoration.map_children {k : Kind} (d : Decoration k F) (f : F → G)
    (p : k.table.Port) : (d.map f).children p=(d.children p).map f := by
  simp only [Decoration.children,List.map_ofFn]
  rfl

namespace RealizedBand
variable {parent : F} {a b : List F} (B : RealizedBand parent a b)

def map (f : F → G) : RealizedBand (f parent) (a.map f) (b.map f) where
  length := B.length
  kind := B.kind
  decoration v := (B.decoration v).map f
  arity_match := B.arity_match
  color_match j i := congrArg f (B.color_match j i)
  input_parent := congrArg f B.input_parent
  output_parent := congrArg f B.output_parent
  input_children := by rw [Decoration.map_children,B.input_children]
  output_children := by rw [Decoration.map_children,B.output_children]

lemma first_signature : portSignature B.decoration (B.patch.plus (.inr B.shortFirst)).val=(parent,a) := by
  exact Prod.ext B.input_parent B.input_children
lemma last_signature : portSignature B.decoration (B.patch.minus (.inr B.shortLast)).val=(parent,b) := by
  exact Prod.ext B.output_parent B.output_children

lemma double_signature_plus (i : Bool) :
    portSignature (doubleDecoration B.decoration) (B.doublePatch.plus (.inr i)).val=
      (parent,if i then b else a) := by
  cases i
  · exact B.first_signature
  · exact ((B.decoration (Fin.last B.length)).mirror_signature _).trans B.last_signature
lemma double_signature_minus (i : Bool) :
    portSignature (doubleDecoration B.decoration) (B.doublePatch.minus (.inr i)).val=
      (parent,if i then b else a) := by
  cases i
  · exact ((B.decoration 0).mirror_signature _).trans B.first_signature
  · exact B.last_signature
end RealizedBand
end IntegralCharacterVarieties.OccurrenceIncidence.VertexTable

namespace IntegralCharacterVarieties.OccurrenceIncidence
open scoped Classical
open VertexTable
namespace PortAssembly
variable {F G S V : Type} {arity : S → ℕ} (A : PortAssembly F S V arity)

def mapFacet (f : F → G) : PortAssembly G S V arity where
  kind := A.kind
  attach := A.attach
  count := A.count
  endpoint := A.endpoint
  facet s := f (A.facet s)
  facetContinuation x := congrArg f (A.facetContinuation x)

noncomputable def seamChildren (q : S) : List F := List.ofFn (fun i => A.facet ⟨q,some i⟩)

/-- A actual gallery at the two old ends, including genuine transverse seams,
is spliced by the same-q inverse-cut three-cycle. The endpoint lists are those
of the OLD seam, so each original child occurrence survives in its own slot. -/
noncomputable def graftBand (q : S)
    (B : RealizedBand (A.facet ⟨q,none⟩) (A.seamChildren q) (A.seamChildren q)) :=
  graftAssembly A B.doublePatch (doubleDecoration B.decoration) q
    (B.patch.double_signatureMatch B.decoration B.patch_signatureMatch B.shortFirst B.shortLast)
    (fun i => by rw [B.double_signature_plus]; cases i <;> rfl)
    (fun i => by rw [B.double_signature_minus]; cases i <;> rfl)

end PortAssembly
end IntegralCharacterVarieties.OccurrenceIncidence
namespace IntegralCharacterVarieties.OccurrenceIncidence
open scoped Classical
open VertexTable TwoFlagBand
namespace PortAssembly
variable {F S V : Type} {arity : S → ℕ} (A : PortAssembly F S V arity) (q : S)

abbrev BandFacet (_A : PortAssembly F S V arity) (q : S) :=
  F ⊕ (Fin (arity q) × Fin (arity q))

/-- Old row and column grades attach to their own ordered old occurrence;
only common-graded cells are new facets. Equal old facet names are allowed. -/
def bandColor : Option (Secondary (arity q) (arity q)) → A.BandFacet q
  | none => .inl (A.facet ⟨q,none⟩)
  | some (.row i) => .inl (A.facet ⟨q,some i⟩)
  | some (.col j) => .inl (A.facet ⟨q,some j⟩)
  | some (.cell i j) => .inr (i,j)

lemma bandColor_parent_iff (h : ∀ i,A.facet ⟨q,some i⟩≠A.facet ⟨q,none⟩)
    (f : Option (Secondary (arity q) (arity q))) :
    A.bandColor q f=.inl (A.facet ⟨q,none⟩) ↔ f=none := by
  cases f with
  | none => simp only [bandColor]
  | some f =>
    cases f with
    | row i => simp [bandColor,h i]
    | col j => simp [bandColor,h j]
    | cell i j => simp [bandColor]

variable {r : ℕ} (d : RankShape (arity q) (arity q) r)

/-- This is the very same obtained weighted atomic gallery, not a replacement
chosen from its endpoints or ranks. -/
noncomputable def namedAtomicBand : RealizedBand
    ((A.mapFacet (Sum.inl : F → A.BandFacet q)).facet ⟨q,none⟩)
    ((A.mapFacet (Sum.inl : F → A.BandFacet q)).seamChildren q)
    ((A.mapFacet (Sum.inl : F → A.BandFacet q)).seamChildren q) := by
  have hr : (((List.ofFn (Secondary.row : Fin (arity q) → Secondary (arity q) (arity q))).map some).map
      (A.bandColor q))=(A.mapFacet (Sum.inl : F → A.BandFacet q)).seamChildren q := by
    simp only [List.map_ofFn]
    rfl
  have hc : (((List.ofFn (Secondary.col : Fin (arity q) → Secondary (arity q) (arity q))).map some).map
      (A.bandColor q))=(A.mapFacet (Sum.inl : F → A.BandFacet q)).seamChildren q := by
    simp only [List.map_ofFn]
    rfl
  exact { d.atomicBand.map (A.bandColor q) with
    input_children := (d.atomicBand.map (A.bandColor q)).input_children.trans hr
    output_children := (d.atomicBand.map (A.bandColor q)).output_children.trans hc }

noncomputable def atomicBandGraft :=
  (A.mapFacet (Sum.inl : F → A.BandFacet q)).graftBand q (A.namedAtomicBand q d)

lemma namedAtomicBand_parent_germs
    (h : ∀ i,A.facet ⟨q,some i⟩≠A.facet ⟨q,none⟩)
    (v : Fin (d.atomicBand.length+1)) (z) :
    ((A.namedAtomicBand q d).decoration v).color z=.inl (A.facet ⟨q,none⟩) ↔
      z=⟨(d.atomicBand.kind v).input,none⟩ ∨ z=⟨(d.atomicBand.kind v).output,none⟩ := by
  change A.bandColor q ((d.atomicBand.decoration v).color z)=_ ↔ _
  rw [A.bandColor_parent_iff q h]
  obtain ⟨s,hs⟩ := d.atomicBand_fresh v
  rw [hs]
  exact (d.atomicBand.kind v).fresh_color_none s z

end PortAssembly
end IntegralCharacterVarieties.OccurrenceIncidence

namespace IntegralCharacterVarieties.OccurrenceIncidence
open scoped Classical
open VertexTable
namespace PortWiring
variable {V F : Type} {kind : V → Kind} (W : PortWiring kind)

lemma sideOf_positive_parent (p : W.Seam) :
    W.sideOf ⟨p.val.1,p.val.2,none⟩=⟨p,none⟩ := by
  apply sideNumber_injective
  rw [W.sideOf_number]
  have h := W.endOf_portAt (p,true)
  change W.endOf p.val=(p,true) at h
  rw [h]
  rfl

lemma sideOf_negative_parent (p : PortAt kind false) :
    W.sideOf ⟨p.val.1,p.val.2,none⟩=⟨W.wire.symm p,none⟩ := by
  apply sideNumber_injective
  rw [W.sideOf_number]
  have h := W.endOf_portAt (W.wire.symm p,false)
  change W.endOf (W.wire (W.wire.symm p)).val=(W.wire.symm p,false) at h
  rw [Equiv.apply_symm_apply] at h
  rw [h]
  rfl

lemma parent_next (d : (v : V) → Decoration (kind v) F) (hd : W.ColorMatch d)
    (p : W.Seam) (u : PortAt kind false)
    (hm : localMate (⟨p.val.1,p.val.2,none⟩ : LocalEnd V kind)=⟨u.val.1,u.val.2,none⟩) :
    (W.colored d hd).vertexAssembly.corners.boundaryNext ⟨p,none⟩=
      ⟨W.wire.symm u,none⟩ := by
  rw [← W.sideOf_positive_parent p]
  change (W.assemble _ _).vertexAssembly.corners.boundaryNext _=_
  rw [W.boundaryNext_local _ _ _ (by exact p.property),hm,W.sideOf_negative_parent]
end PortWiring

variable {F S V W I : Type} {arity : S → ℕ} (A : PortAssembly F S V arity)
    {kind : W → Kind} (P : PortPatch kind I Bool Bool) (d : (w : W) → Decoration (kind w) F)
variable (q : S) (hi : P.SignatureMatch d)
    (hp : ∀ b,portSignature d (P.plus (.inr b)).val=A.seamSignature q)
    (hm : ∀ b,portSignature d (P.minus (.inr b)).val=A.seamSignature q)

lemma graft_wire_plus (z : S ⊕ (I ⊕ Bool)) :
    (graftWiring A P d q hi hp hm).wire (graftPlus A P z)=
      graftMinus A P (graftCycle q z) := by
  change graftMinus A P (graftCycle q ((graftPlus A P).symm (graftPlus A P z)))=_
  rw [Equiv.symm_apply_apply]

lemma graft_wire_symm (z : S ⊕ (I ⊕ Bool)) :
    (graftWiring A P d q hi hp hm).wire.symm (graftMinus A P (graftCycle q z))=
      graftPlus A P z := by
  rw [← graft_wire_plus A P d q hi hp hm,Equiv.symm_apply_apply]

namespace PortPatch
variable {U J C E : Type} {k : U → Kind} (Q : PortPatch k J C E) (a : C) (b : E)
@[simp] lemma double_plus_original (j : J) :
    (Q.double a b).plus (.inl (.inl (.inl j)))=
      sumPortAt k (mirrorKind k) true (.inl (Q.plus (.inl j))) := rfl
@[simp] lemma double_minus_original (j : J) :
    (Q.double a b).minus (.inl (.inl (.inl j)))=
      sumPortAt k (mirrorKind k) false (.inl (Q.minus (.inl j))) := rfl
@[simp] lemma double_plus_mirror (j : J) :
    (Q.double a b).plus (.inl (.inl (.inr j)))=
      sumPortAt k (mirrorKind k) true (.inr (mirrorPortAt k false (Q.minus (.inl j)))) := rfl
@[simp] lemma double_minus_mirror (j : J) :
    (Q.double a b).minus (.inl (.inl (.inr j)))=
      sumPortAt k (mirrorKind k) false (.inr (mirrorPortAt k true (Q.plus (.inl j)))) := rfl
end PortPatch
end IntegralCharacterVarieties.OccurrenceIncidence
namespace IntegralCharacterVarieties.OccurrenceIncidence
open scoped Classical
open VertexTable
namespace BandGraft
variable {F S V : Type} {arity : S → ℕ} (A : PortAssembly F S V arity) (q : S)
    (B : RealizedBand (A.facet ⟨q,none⟩) (A.seamChildren q) (A.seamChildren q))

abbrev kind := sumKind A.kind (sumKind B.kind (mirrorKind B.kind))
noncomputable abbrev wiring := graftWiring A B.doublePatch (doubleDecoration B.decoration) q
    (B.patch.double_signatureMatch B.decoration B.patch_signatureMatch B.shortFirst B.shortLast)
    (fun i => by rw [B.double_signature_plus]; cases i <;> rfl)
    (fun i => by rw [B.double_signature_minus]; cases i <;> rfl)

noncomputable def oldPort (s : S) (b : Bool) : PortAt (kind A q B) b :=
  sumPortAt A.kind (sumKind B.kind (mirrorKind B.kind)) b (.inl (A.portAt b s))
noncomputable def originalPort (v : Fin (B.length+1)) (b : Bool) : PortAt (kind A q B) b :=
  sumPortAt A.kind (sumKind B.kind (mirrorKind B.kind)) b (.inr
    (sumPortAt B.kind (mirrorKind B.kind) b (.inl
      (if h : b=true then h ▸ VariableGallery.input B.kind v
        else (Bool.eq_false_iff.mpr h) ▸ VariableGallery.output B.kind v))))
noncomputable def mirrorInput (v : Fin (B.length+1)) : PortAt (kind A q B) false :=
  sumPortAt A.kind (sumKind B.kind (mirrorKind B.kind)) false (.inr
    (sumPortAt B.kind (mirrorKind B.kind) false (.inr
      (mirrorPortAt B.kind true (VariableGallery.input B.kind v)))))
noncomputable def mirrorOutput (v : Fin (B.length+1)) : PortAt (kind A q B) true :=
  sumPortAt A.kind (sumKind B.kind (mirrorKind B.kind)) true (.inr
    (sumPortAt B.kind (mirrorKind B.kind) true (.inr
      (mirrorPortAt B.kind false (VariableGallery.output B.kind v)))))

lemma original_corner (v : Fin (B.length+1)) :
    localMate (⟨(originalPort A q B v true).val.1,(originalPort A q B v true).val.2,none⟩ :
      LocalEnd _ (kind A q B))=
    ⟨(originalPort A q B v false).val.1,(originalPort A q B v false).val.2,none⟩ := by
  change (⟨.inr (.inl v),(B.kind v).table.mate ⟨(B.kind v).input,none⟩⟩ : LocalEnd _ (kind A q B))=_
  rw [Kind.principal_corner]
  rfl

lemma mirror_corner (v : Fin (B.length+1)) :
    localMate (⟨(mirrorOutput A q B v).val.1,(mirrorOutput A q B v).val.2,none⟩ :
      LocalEnd _ (kind A q B))=
    ⟨(mirrorInput A q B v).val.1,(mirrorInput A q B v).val.2,none⟩ := by
  have hi := (B.kind v).table.involutive ⟨(B.kind v).input,none⟩
  rw [Kind.principal_corner] at hi
  have hm := (B.kind v).mirror_mate ⟨(B.kind v).output,none⟩
  rw [hi] at hm
  exact congrArg (fun z => (⟨.inr (.inr v),z⟩ : LocalEnd _ (kind A q B))) hm.symm

lemma wire_original (j : Fin B.length) :
    (wiring A q B).wire (originalPort A q B j.succ true)=
      originalPort A q B j.castSucc false := by
  have h := graft_wire_plus A B.doublePatch (doubleDecoration B.decoration) q
    (B.patch.double_signatureMatch B.decoration B.patch_signatureMatch B.shortFirst B.shortLast)
    (fun i => by rw [B.double_signature_plus]; cases i <;> rfl)
    (fun i => by rw [B.double_signature_minus]; cases i <;> rfl)
    (.inr (.inl (.inl (.inl j))))
  rw [graftCycle_internal] at h
  exact h

lemma wire_mirror (j : Fin B.length) :
    (wiring A q B).wire (mirrorOutput A q B j.castSucc)=
      mirrorInput A q B j.succ := by
  have h := graft_wire_plus A B.doublePatch (doubleDecoration B.decoration) q
    (B.patch.double_signatureMatch B.decoration B.patch_signatureMatch B.shortFirst B.shortLast)
    (fun i => by rw [B.double_signature_plus]; cases i <;> rfl)
    (fun i => by rw [B.double_signature_minus]; cases i <;> rfl)
    (.inr (.inl (.inl (.inr j))))
  rw [graftCycle_internal] at h
  exact h

lemma wire_first : (wiring A q B).wire (originalPort A q B 0 true)=oldPort A q B q false := by
  have h := graft_wire_plus A B.doublePatch (doubleDecoration B.decoration) q
    (B.patch.double_signatureMatch B.decoration B.patch_signatureMatch B.shortFirst B.shortLast)
    (fun i => by rw [B.double_signature_plus]; cases i <;> rfl)
    (fun i => by rw [B.double_signature_minus]; cases i <;> rfl) (.inr (.inr false))
  rw [graftCycle_false] at h
  exact h

lemma wire_last : (wiring A q B).wire (oldPort A q B q true)=
    originalPort A q B (Fin.last B.length) false := by
  have h := graft_wire_plus A B.doublePatch (doubleDecoration B.decoration) q
    (B.patch.double_signatureMatch B.decoration B.patch_signatureMatch B.shortFirst B.shortLast)
    (fun i => by rw [B.double_signature_plus]; cases i <;> rfl)
    (fun i => by rw [B.double_signature_minus]; cases i <;> rfl) (.inl q)
  rw [graftCycle_q] at h
  exact h

lemma wire_mirror_wrap : (wiring A q B).wire (mirrorOutput A q B (Fin.last B.length))=
    mirrorInput A q B 0 := by
  have h := graft_wire_plus A B.doublePatch (doubleDecoration B.decoration) q
    (B.patch.double_signatureMatch B.decoration B.patch_signatureMatch B.shortFirst B.shortLast)
    (fun i => by rw [B.double_signature_plus]; cases i <;> rfl)
    (fun i => by rw [B.double_signature_minus]; cases i <;> rfl) (.inr (.inr true))
  rw [graftCycle_true] at h
  exact h

lemma wire_old (s : S) (hs : s≠q) :
    (wiring A q B).wire (oldPort A q B s true)=oldPort A q B s false := by
  have h := graft_wire_plus A B.doublePatch (doubleDecoration B.decoration) q
    (B.patch.double_signatureMatch B.decoration B.patch_signatureMatch B.shortFirst B.shortLast)
    (fun i => by rw [B.double_signature_plus]; cases i <;> rfl)
    (fun i => by rw [B.double_signature_minus]; cases i <;> rfl) (.inl s)
  rwa [graftCycle_old q s hs] at h

end BandGraft
end IntegralCharacterVarieties.OccurrenceIncidence
namespace IntegralCharacterVarieties.OccurrenceIncidence
open scoped Classical
open VertexTable
namespace BandGraft
variable {F S V : Type} {arity : S → ℕ} (A : PortAssembly F S V arity) (q : S)
    (B : RealizedBand (A.facet ⟨q,none⟩) (A.seamChildren q) (A.seamChildren q))

noncomputable abbrev decoration := graftDecoration A (doubleDecoration B.decoration)
noncomputable abbrev colorMatch := graftWiring_colorMatch A B.doublePatch (doubleDecoration B.decoration) q
    (B.patch.double_signatureMatch B.decoration B.patch_signatureMatch B.shortFirst B.shortLast)
    (fun i => by rw [B.double_signature_plus]; cases i <;> rfl)
    (fun i => by rw [B.double_signature_minus]; cases i <;> rfl)
noncomputable abbrev next := (A.graftBand q B).vertexAssembly.corners.boundaryNext
noncomputable def oldSide (s : S) : Side (wiring A q B).Seam (wiring A q B).seamArity :=
  ⟨oldPort A q B s true,none⟩
noncomputable def originalSide (v : Fin (B.length+1)) : Side (wiring A q B).Seam (wiring A q B).seamArity :=
  ⟨originalPort A q B v true,none⟩
noncomputable def mirrorSide (v : Fin (B.length+1)) : Side (wiring A q B).Seam (wiring A q B).seamArity :=
  ⟨mirrorOutput A q B v,none⟩

lemma next_original (j : Fin B.length) :
    next A q B (originalSide A q B j.castSucc)=originalSide A q B j.succ := by
  have h := (wiring A q B).parent_next (decoration A q B) (colorMatch A q B)
    (originalPort A q B j.castSucc true) (originalPort A q B j.castSucc false)
    (original_corner A q B j.castSucc)
  rw [← wire_original A q B j,Equiv.symm_apply_apply] at h
  exact h

lemma next_original_last : next A q B (originalSide A q B (Fin.last B.length))=oldSide A q B q := by
  have h := (wiring A q B).parent_next (decoration A q B) (colorMatch A q B)
    (originalPort A q B (Fin.last B.length) true) (originalPort A q B (Fin.last B.length) false)
    (original_corner A q B (Fin.last B.length))
  rw [← wire_last A q B,Equiv.symm_apply_apply] at h
  exact h

lemma next_mirror (j : Fin B.length) :
    next A q B (mirrorSide A q B j.succ)=mirrorSide A q B j.castSucc := by
  have h := (wiring A q B).parent_next (decoration A q B) (colorMatch A q B)
    (mirrorOutput A q B j.succ) (mirrorInput A q B j.succ) (mirror_corner A q B j.succ)
  rw [← wire_mirror A q B j,Equiv.symm_apply_apply] at h
  exact h

lemma next_mirror_zero : next A q B (mirrorSide A q B 0)=mirrorSide A q B (Fin.last B.length) := by
  have h := (wiring A q B).parent_next (decoration A q B) (colorMatch A q B)
    (mirrorOutput A q B 0) (mirrorInput A q B 0) (mirror_corner A q B 0)
  rw [← wire_mirror_wrap A q B,Equiv.symm_apply_apply] at h
  exact h

end BandGraft
namespace PortAssembly
variable {F S V : Type} {arity : S → ℕ} (A : PortAssembly F S V arity)
lemma realize_portAt_parent (s : S) (b : Bool) :
    A.realize ⟨(A.portAt b s).val.1,(A.portAt b s).val.2,none⟩=(⟨s,none⟩,b) := by
  rw [A.realize_apply]
  change ((⟨(A.attach (A.portAt b s).val).1,none⟩ : Side S arity),
    (A.attach (A.portAt b s).val).2)=_
  rw [A.attach_portAt]

lemma parent_corner_of_next (s t : S)
    (h : A.vertexAssembly.corners.boundaryNext ⟨s,none⟩=⟨t,none⟩) :
    localMate (⟨(A.portAt true s).val.1,(A.portAt true s).val.2,none⟩ : LocalEnd V A.kind)=
      ⟨(A.portAt false t).val.1,(A.portAt false t).val.2,none⟩ := by
  have hm := A.vertexAssembly.corners.mate_finish (⟨s,none⟩ : Side S arity)
  change A.vertexAssembly.corners.mate (finish ⟨s,none⟩)=
    start (A.vertexAssembly.corners.boundaryNext ⟨s,none⟩) at hm
  rw [h] at hm
  apply A.realize.injective
  rw [A.realize_portAt_parent]
  have he : A.realize.symm (finish (⟨s,none⟩ : Side S arity))=
      ⟨(A.portAt true s).val.1,(A.portAt true s).val.2,none⟩ := by
    apply A.realize.injective
    rw [A.realize.apply_symm_apply,A.realize_portAt_parent]
    rfl
  change (A.realize (localMate (A.realize.symm (finish ⟨s,none⟩))))=_ at hm
  rw [he] at hm
  exact hm
end PortAssembly

namespace BandGraft
variable {F S V : Type} {arity : S → ℕ} (A : PortAssembly F S V arity) (q : S)
    (B : RealizedBand (A.facet ⟨q,none⟩) (A.seamChildren q) (A.seamChildren q))
lemma old_corner (s t : S)
    (h : A.vertexAssembly.corners.boundaryNext ⟨s,none⟩=⟨t,none⟩) :
    localMate (⟨(oldPort A q B s true).val.1,(oldPort A q B s true).val.2,none⟩ :
      LocalEnd _ (kind A q B))=
    ⟨(oldPort A q B t false).val.1,(oldPort A q B t false).val.2,none⟩ := by
  exact congrArg (fun x : LocalEnd V A.kind => (⟨.inl x.1,x.2⟩ : LocalEnd _ (kind A q B)))
    (A.parent_corner_of_next s t h)

lemma next_old_not_cut (s t : S) (ht : t≠q)
    (h : A.vertexAssembly.corners.boundaryNext ⟨s,none⟩=⟨t,none⟩) :
    next A q B (oldSide A q B s)=oldSide A q B t := by
  have he := (wiring A q B).parent_next (decoration A q B) (colorMatch A q B)
    (oldPort A q B s true) (oldPort A q B t false) (old_corner A q B s t h)
  rw [← wire_old A q B t ht,Equiv.symm_apply_apply] at he
  exact he

lemma next_old_cut (s : S)
    (h : A.vertexAssembly.corners.boundaryNext ⟨s,none⟩=⟨q,none⟩) :
    next A q B (oldSide A q B s)=originalSide A q B 0 := by
  have he := (wiring A q B).parent_next (decoration A q B) (colorMatch A q B)
    (oldPort A q B s true) (oldPort A q B q false) (old_corner A q B s q h)
  rw [← wire_first A q B,Equiv.symm_apply_apply] at he
  exact he
end BandGraft
end IntegralCharacterVarieties.OccurrenceIncidence
namespace IntegralCharacterVarieties.OccurrenceIncidence
open scoped Classical
open VertexTable
namespace PortWiring
variable {V F : Type} {kind : V → Kind} (W : PortWiring kind)

/-- Every side has its literal representative at a positive WHOLE port. -/
lemma positive_side_exists (a : Side W.Seam W.seamArity) :
    ∃ x : LocalEnd V kind, (kind x.1).table.endpoint x.2.1=true ∧ W.sideOf x=a := by
  rcases a with ⟨p,c⟩
  refine ⟨⟨p.val.1,p.val.2,c.map ((kind p.val.1).childEnumeration p.val.2).symm⟩,?_,?_⟩
  · exact p.property
  · apply sideNumber_injective
    rw [W.sideOf_number]
    have he := W.endOf_portAt (p,true)
    change W.endOf p.val=(p,true) at he
    rw [he]
    cases c with
    | none => rfl
    | some c =>
      change Fin ((kind p.val.1).arity p.val.2) at c
      change (p,some (((kind p.val.1).childEnumeration p.val.2)
        (((kind p.val.1).childEnumeration p.val.2).symm c)).val)=(p,some c.val)
      rw [Equiv.apply_symm_apply]
end PortWiring

namespace VertexTable.RealizedBand
variable {F : Type} {p : F} {a b : List F} (B : RealizedBand p a b)
lemma parent_input (v : Fin (B.length+1)) :
    (B.decoration v).portColor (B.kind v).input none=p := by
  refine Fin.induction B.input_parent (fun j ih => ?_) v
  have hc := (B.decoration j.castSucc).corner ⟨(B.kind j.castSucc).input,none⟩
  rw [Kind.principal_corner] at hc
  exact (B.color_match j none).symm.trans (hc.trans ih)
lemma parent_output (v : Fin (B.length+1)) :
    (B.decoration v).portColor (B.kind v).output none=p := by
  have hc := (B.decoration v).corner ⟨(B.kind v).input,none⟩
  rw [Kind.principal_corner] at hc
  exact hc.trans (B.parent_input v)
end VertexTable.RealizedBand

namespace BandGraft
variable {F S V : Type} {arity : S → ℕ} (A : PortAssembly F S V arity) (q : S)
    (B : RealizedBand (A.facet ⟨q,none⟩) (A.seamChildren q) (A.seamChildren q))
lemma oldSide_color (s : S) : (A.graftBand q B).facet (oldSide A q B s)=A.facet ⟨s,none⟩ := by
  change (A.decoration (A.portAt true s).val.1).portColor (A.portAt true s).val.2 none=_
  rw [A.decoration_portColor]
  change A.facet ⟨(A.attach (A.portAt true s).val).1,none⟩=_
  rw [A.attach_portAt]
lemma originalSide_color (v : Fin (B.length+1)) :
    (A.graftBand q B).facet (originalSide A q B v)=A.facet ⟨q,none⟩ := B.parent_input v
lemma mirrorSide_color (v : Fin (B.length+1)) :
    (A.graftBand q B).facet (mirrorSide A q B v)=A.facet ⟨q,none⟩ :=
  ((B.decoration v).mirror_color ⟨(B.kind v).output,none⟩).trans (B.parent_output v)
end BandGraft
end IntegralCharacterVarieties.OccurrenceIncidence
namespace IntegralCharacterVarieties.OccurrenceIncidence
open scoped Classical
open VertexTable
namespace PortAssembly
variable {F S V : Type} {arity : S → ℕ} (A : PortAssembly F S V arity) (f : F)
lemma no_child_parent_local (h : ∀ s i,A.facet ⟨s,some i⟩≠f)
    (x : LocalEnd V A.kind) (hx : (A.decoration x.1).color x.2=f) : x.2.2=none := by
  have hs : (A.realize x).1.2=none := by
    by_contra hn
    obtain ⟨i,hi⟩ := Option.ne_none_iff_exists'.mp hn
    have hh := h (A.realize x).1.1 i
    apply hh
    change A.facet (A.realize x).1=f at hx
    have hz : (A.realize x).1=⟨(A.realize x).1.1,some i⟩ := by
      exact congrArg (Sigma.mk (A.realize x).1.1) hi
    rwa [hz] at hx
  change x.2.2.map (A.childEquiv ⟨x.1,x.2.1⟩)=none at hs
  exact Option.map_eq_none_iff.mp hs
end PortAssembly

namespace BandGraft
variable {F S V : Type} {arity : S → ℕ} (A : PortAssembly F S V arity) (q : S)
    (B : RealizedBand (A.facet ⟨q,none⟩) (A.seamChildren q) (A.seamChildren q))

/-- Exhaustion for the ACTUAL graft, derived from local tables. This does not
infer a band witness from its endpoint lists. Every old parent occurrence and
every original/mirror principal corner is retained as its literal side. -/
theorem parent_exhaustive
    (hold : ∀ s i,A.facet ⟨s,some i⟩≠A.facet ⟨q,none⟩)
    (hband : ∀ v z,(B.decoration v).color z=A.facet ⟨q,none⟩ ↔
      z=⟨(B.kind v).input,none⟩ ∨ z=⟨(B.kind v).output,none⟩)
    (a : Side (wiring A q B).Seam (wiring A q B).seamArity)
    (ha : (A.graftBand q B).facet a=A.facet ⟨q,none⟩) :
    (∃ s,A.facet ⟨s,none⟩=A.facet ⟨q,none⟩ ∧ a=oldSide A q B s) ∨
    (∃ v,a=originalSide A q B v) ∨ (∃ v,a=mirrorSide A q B v) := by
  obtain ⟨⟨v,p,c⟩,he,rfl⟩ := (wiring A q B).positive_side_exists a
  have hc : (decoration A q B v).color ⟨p,c⟩=A.facet ⟨q,none⟩ := by
    exact ((wiring A q B).seamColor_sideOf (decoration A q B) (colorMatch A q B) _).symm.trans ha
  rcases v with v|v|v
  · have hn := A.no_child_parent_local (A.facet ⟨q,none⟩) hold ⟨v,p,c⟩ hc
    change c=none at hn
    subst c
    let u : PortAt A.kind true := ⟨⟨v,p⟩,he⟩
    obtain ⟨s,hs⟩ := (A.portAt true).surjective u
    let z : (wiring A q B).Seam := sumPortAt A.kind (sumKind B.kind (mirrorKind B.kind)) true (.inl u)
    have hz : z=oldPort A q B s true := congrArg
      (fun u => sumPortAt A.kind (sumKind B.kind (mirrorKind B.kind)) true (.inl u)) hs.symm
    have hside : (wiring A q B).sideOf ⟨.inl v,p,none⟩=oldSide A q B s :=
      ((wiring A q B).sideOf_positive_parent z).trans
        (congrArg (fun u => (⟨u,none⟩ : Side (wiring A q B).Seam (wiring A q B).seamArity)) hz)
    refine Or.inl ⟨s,?_,hside⟩
    exact (oldSide_color A q B s).symm.trans
      ((congrArg (A.graftBand q B).facet hside).symm.trans ha)
  · obtain hg|hg := (hband v ⟨p,c⟩).mp hc
    · right; left; refine ⟨v,?_⟩
      exact (congrArg (fun z : (p : (B.kind v).table.Port) × Option ((B.kind v).table.Child p) =>
        (wiring A q B).sideOf (⟨.inr (.inl v),z⟩ : LocalEnd _ (kind A q B))) hg).trans
        ((wiring A q B).sideOf_positive_parent (originalPort A q B v true))
    · have hh := congrArg (fun z : (p : (B.kind v).table.Port) × Option ((B.kind v).table.Child p) =>
        (B.kind v).table.endpoint z.1) hg
      rw [Kind.output_endpoint] at hh
      exact Bool.noConfusion (he.symm.trans hh)
  · have hh : (B.decoration v).color ((B.kind v).mirrorEnd.symm ⟨p,c⟩)=A.facet ⟨q,none⟩ := hc
    obtain hg|hg := (hband v _).mp hh
    · have hz := congrArg (B.kind v).mirrorEnd hg
      rw [Equiv.apply_symm_apply] at hz
      have heq := congrArg (fun z : (p : (B.kind v).mirror.table.Port) ×
        Option ((B.kind v).mirror.table.Child p) => (B.kind v).mirror.table.endpoint z.1) hz
      change (B.kind v).mirror.table.endpoint p=
        (B.kind v).mirror.table.endpoint ((B.kind v).mirrorPort (B.kind v).input) at heq
      rw [Kind.mirror_endpoint,Kind.input_endpoint] at heq
      exact Bool.noConfusion (he.symm.trans heq)
    · have hz := congrArg (B.kind v).mirrorEnd hg
      rw [Equiv.apply_symm_apply] at hz
      right; right; refine ⟨v,?_⟩
      exact (congrArg (fun z : (p : (B.kind v).mirror.table.Port) × Option ((B.kind v).mirror.table.Child p) =>
        (wiring A q B).sideOf (⟨.inr (.inr v),z⟩ : LocalEnd _ (kind A q B))) hz).trans
        ((wiring A q B).sideOf_positive_parent (mirrorOutput A q B v))
end BandGraft
end IntegralCharacterVarieties.OccurrenceIncidence
namespace IntegralCharacterVarieties.OccurrenceIncidence
open scoped Classical
open VertexTable TwoFlagBand
namespace PortAssembly
variable {F S V : Type} {arity : S → ℕ} (A : PortAssembly F S V arity) (q : S)
variable {r : ℕ} (d : RankShape (arity q) (arity q) r)

/-- Parent exhaustion for the SAME produced named atomic graft. Both hypotheses
of the general assembly theorem are discharged from the actual old incidence
and actual weighted gallery; no independent cyclic template is substituted. -/
theorem atomicBandGraft_parent_exhaustive
    (hold : ∀ s i,A.facet ⟨s,some i⟩≠A.facet ⟨q,none⟩)
    (a : Side (BandGraft.wiring (A.mapFacet (Sum.inl : F → A.BandFacet q)) q (A.namedAtomicBand q d)).Seam
      (BandGraft.wiring (A.mapFacet (Sum.inl : F → A.BandFacet q)) q (A.namedAtomicBand q d)).seamArity)
    (ha : (A.atomicBandGraft q d).facet a=.inl (A.facet ⟨q,none⟩)) :
    (∃ s,A.facet ⟨s,none⟩=A.facet ⟨q,none⟩ ∧
      a=BandGraft.oldSide (A.mapFacet (Sum.inl : F → A.BandFacet q)) q (A.namedAtomicBand q d) s) ∨
    (∃ v,a=BandGraft.originalSide (A.mapFacet (Sum.inl : F → A.BandFacet q)) q (A.namedAtomicBand q d) v) ∨
    (∃ v,a=BandGraft.mirrorSide (A.mapFacet (Sum.inl : F → A.BandFacet q)) q (A.namedAtomicBand q d) v) := by
  let A' := A.mapFacet (Sum.inl : F → A.BandFacet q)
  have hh : ∀ s i,A'.facet ⟨s,some i⟩≠A'.facet ⟨q,none⟩ := by
    intro s i h
    exact hold s i (Sum.inl.inj h)
  have hg := BandGraft.parent_exhaustive A' q (A.namedAtomicBand q d) hh
    (A.namedAtomicBand_parent_germs q d (hold q)) a ha
  rcases hg with ⟨s,hs,ha⟩|h|h
  · exact Or.inl ⟨s,Sum.inl.inj hs,ha⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
end PortAssembly
end IntegralCharacterVarieties.OccurrenceIncidence

namespace IntegralCharacterVarieties.SurfacePresentation.Diagram
open scoped Classical
open OccurrenceIncidence TwoFlagBand
variable {F S V : Type} {arity : S → ℕ} (D : Diagram F S V arity) (q : S)

/-- The global no-parent-child fact used above follows from the exact
normalized maximal-rank hypotheses of the manuscript reduction. -/
theorem maximal_no_child_parent (h : D.Proper)
    (hn : ∀ f,D.rank f≤D.rank (D.ports.facet ⟨q,none⟩)) :
    ∀ s i,D.ports.facet ⟨s,some i⟩≠D.ports.facet ⟨q,none⟩ := by
  intro s i he
  have hl := D.proper_child_lt h s i
  have hu := hn (D.ports.facet ⟨s,none⟩)
  rw [he] at hl
  omega
end IntegralCharacterVarieties.SurfacePresentation.Diagram

end OAI

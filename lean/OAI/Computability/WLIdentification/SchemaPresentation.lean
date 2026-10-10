import OAI.Computability.WLIdentification.TypedCases

namespace OAI

namespace WLIdentification
namespace FinitePresentation
open WordExpressions
attribute [local instance] Classical.propDecidable Classical.decEq

structure SchemaRealizer {P E : Word → Type} (PP : Presented P) (EP : Presented E)
    (r : Word → ℕ) (rp : NatPoly (fun S : Fin 1 → Word => r (S 0)))
    (S : ∀ w, ComparisonSchemas (r w) (P w) (E w)) where
  pointIndex : Number PP (fun w p => (S w).pointIndex p)
  edgeIndex : Number EP (fun w e => (S w).edgeIndex e)
  dimension : Number PP (fun w p => (S w).dimension p)
  source : Map EP PP (fun w => (S w).source)
  target : Map EP PP (fun w => (S w).target)
  domain : Test (EP.prod ((Presented.fin r rp).prod Presented.bool)) (fun w x => decide (x.2.2∈(S w).domain x.1 x.2.1))
  mapping : Word → ℕ → ℕ → ℕ → ℕ
  mapping_eq : ∀ w e i (a : {a // a∈(S w).domain e i}), mapping w (EP.code w e) i.val (NaturalCode.bool a.val)=NaturalCode.bool ((S w).mapping e i a)
  mapping_poly : NatPoly (fun X : Fin 4 → Word => mapping (X 0) (X 1).length (X 2).length (X 3).length)
  left : Number (EP.prod (Presented.bit.prod Presented.bit)) (fun w x => ((S w).left x.1 (vectorTwo _ x.2)).val)
  right : Number (EP.prod (Presented.bit.prod Presented.bit)) (fun w x => ((S w).right x.1 (vectorTwo _ x.2)).val)

namespace SchemaRealizer
variable {P E : Word → Type} {PP : Presented P} {EP : Presented E}
    {r : Word → ℕ} {rp : NatPoly (fun X : Fin 1 → Word => r (X 0))}
    {S : ∀ w, ComparisonSchemas (r w) (P w) (E w)} (F : SchemaRealizer PP EP r rp S)
    (n : Word → ℕ) (np : NatPoly (fun X : Fin 1 → Word => n (X 0)))

abbrev internalP (_F : SchemaRealizer PP EP r rp S) := PP.sum (EP.prod (Presented.fin (fun w => n w+1) (NatPoly.succ np)))
abbrev linkP (_F : SchemaRealizer PP EP r rp S) := EP.sum ((EP.prod (Presented.fin n np)).sum EP)

noncomputable def internalIndex : Number (F.internalP n np) (fun w t => ((S w).layout (n w)).typeIndex t) := by
  let e : Number (EP.prod (Presented.fin (fun w => n w+1) (NatPoly.succ np))) (fun w x => Nat.pair ((S w).edgeIndex x.1) x.2.val) :=
    (F.edgeIndex.comp (Map.fst _ _)).pair (Number.code (Presented.fin (fun w => n w+1) (NatPoly.succ np)) |>.comp (Map.snd _ _))
  exact (Number.sumCases ((Number.const PP 2).mul F.pointIndex)
    (((Number.const _ 2).mul e).add (Number.const _ 1))).congr (by intro w t; cases t <;> rfl)

noncomputable def linkIndex : Number (F.linkP n np) (fun w e => ((S w).layout (n w)).linkIndex e) := by
  let e : Number (EP.prod (Presented.fin n np)) (fun w x => Nat.pair ((S w).edgeIndex x.1) x.2.val) :=
    (F.edgeIndex.comp (Map.fst _ _)).pair (Number.code (Presented.fin n np) |>.comp (Map.snd _ _))
  let q := Number.sumCases ((Number.const _ 2).mul e) (((Number.const EP 2).mul F.edgeIndex).add (Number.const EP 1))
  exact (Number.sumCases ((Number.const EP 2).mul F.edgeIndex)
    (((Number.const _ 2).mul q).add (Number.const _ 1))).congr (by intro w t; cases t with
      | inl e => rfl
      | inr e => cases e <;> rfl)

noncomputable def internalDimension : Number (F.internalP n np) (fun w t => ((S w).layout (n w)).dimension t) :=
  (Number.sumCases F.dimension (Number.const _ 1)).congr (by intro w t; cases t <;> rfl)

def wireCode (_F : SchemaRealizer PP EP r rp S) (l : ℕ) :=
  if l%2=0 then l/2 else if (l/2)%2=0 then (Nat.unpair ((l/2)/2)).1 else (l/2)/2

theorem wireCode_eq (w : Word) (l : (S w).Link (n w)) : F.wireCode ((F.linkP n np).code w l)=EP.code w ((S w).wire (n w) l) := by
  cases l with
  | inl e => change F.wireCode (2*EP.code w e)=EP.code w e; simp [wireCode]
  | inr l => cases l with
    | inl p =>
      change F.wireCode (2*(2*Nat.pair (EP.code w p.1) p.2.val)+1)=_
      simp [wireCode,AffineRealizer.odd_half]
      rfl
    | inr e =>
      change F.wireCode (2*(2*EP.code w e+1)+1)=_
      simp [wireCode,AffineRealizer.odd_half]
      rfl

def firstEval (w : Word) (l : ℕ) :=
  if l%2=0 then 2*F.source.eval w (l/2)
  else if (l/2)%2=0 then 2*(l/2/2)+1 else 2*Nat.pair (l/2/2) (n w)+1

def secondEval (w : Word) (l : ℕ) :=
  if l%2=0 then 2*Nat.pair (l/2) 0+1
  else if (l/2)%2=0 then 2*Nat.pair (Nat.unpair (l/2/2)).1 ((Nat.unpair (l/2/2)).2+1)+1
  else 2*F.target.eval w (l/2/2)

noncomputable def first : Map (F.linkP n np) (F.internalP n np) (fun w => ((S w).layout (n w)).first) where
  eval := F.firstEval n
  correct w l := by
    cases l with
    | inl e =>
      change F.firstEval n w (2*EP.code w e)=2*PP.code w ((S w).source e)
      simp [firstEval,F.source.correct]
    | inr l => cases l with
      | inl p =>
        change F.firstEval n w (2*(2*Nat.pair (EP.code w p.1) p.2.val)+1)=2*Nat.pair (EP.code w p.1) p.2.val+1
        simp [firstEval,AffineRealizer.odd_half]
      | inr e =>
        change F.firstEval n w (2*(2*EP.code w e+1)+1)=2*Nat.pair (EP.code w e) (n w)+1
        simp [firstEval,AffineRealizer.odd_half]
  poly := by
    unfold firstEval
    apply NatPoly.iteProp (by word_poly)
    · exact NatPoly.mul (NatPoly.const 2) (F.source.eval_poly (Poly.var 0) (by word_poly))
    · apply NatPoly.iteProp (by word_poly) (by word_poly)
      exact NatPoly.add (NatPoly.mul (NatPoly.const 2) (NatPoly.pair (by word_poly) (np.rename (fun _ => 0)))) (NatPoly.const 1)

noncomputable def second : Map (F.linkP n np) (F.internalP n np) (fun w => ((S w).layout (n w)).second) where
  eval := F.secondEval
  correct w l := by
    cases l with
    | inl e =>
      change F.secondEval w (2*EP.code w e)=2*Nat.pair (EP.code w e) 0+1
      simp [secondEval]
    | inr l => cases l with
      | inl p =>
        change F.secondEval w (2*(2*Nat.pair (EP.code w p.1) p.2.val)+1)=2*Nat.pair (EP.code w p.1) (p.2.val+1)+1
        simp [secondEval,AffineRealizer.odd_half]
      | inr e =>
        change F.secondEval w (2*(2*EP.code w e+1)+1)=2*PP.code w ((S w).target e)
        simp [secondEval,AffineRealizer.odd_half,F.target.correct]
  poly := by
    unfold secondEval
    apply NatPoly.iteProp (by word_poly) (by word_poly)
    apply NatPoly.iteProp (by word_poly) (by word_poly)
    exact NatPoly.mul (NatPoly.const 2) (F.target.eval_poly (Poly.var 0) (by word_poly))

end SchemaRealizer
end FinitePresentation

namespace FinitePresentation.SchemaRealizer
open WordExpressions
attribute [local instance] Classical.propDecidable Classical.decEq
variable {P E : Word → Type} {PP : Presented P} {EP : Presented E}
    {r : Word → ℕ} {rp : NatPoly (fun X : Fin 1 → Word => r (X 0))}
    {S : ∀ w, ComparisonSchemas (r w) (P w) (E w)} (F : SchemaRealizer PP EP r rp S)
    (n : Word → ℕ) (np : NatPoly (fun X : Fin 1 → Word => n (X 0)))

noncomputable def labels : Test ((F.internalP n np).prod ((Presented.fin r rp).prod Presented.bool))
    (fun w x => decide (x.2.2∈((S w).layout (n w)).labels x.1 x.2.1)) where
  eval w i := if (Nat.unpair i).1%2=0 then true
    else F.domain.eval w (Nat.pair (Nat.unpair ((Nat.unpair i).1/2)).1 (Nat.unpair i).2)
  correct w x := by
    simp only [Presented.prod_code,Nat.unpair_pair]
    rcases x with ⟨t,i,a⟩
    cases t with
    | inl p =>
      simp only [internalP,Presented.sum_inl_code,Presented.fin_code,Presented.bool_code]
      change (if (2*PP.code w p)%2=0 then true else _)=_
      simp only [Nat.mul_mod_right,ite_true,ComparisonSchemas.layout,ComparisonSchemas.layoutLabels,Finset.mem_univ,decide_true]
    | inr p =>
      simp only [internalP,Presented.sum_inr_code,Presented.prod_code,Presented.fin_code,Presented.bool_code]
      change (if (2*Nat.pair (EP.code w p.1) p.2.val+1)%2=0 then true else _)=_
      simp only [show (2*Nat.pair (EP.code w p.1) p.2.val+1)%2≠0 by omega,ite_false,AffineRealizer.odd_half,Nat.unpair_pair]
      exact F.domain.correct w (p.1,i,a)
  poly := BoolPoly.iteProp (by word_poly) (BoolPoly.const true)
    (F.domain.eval_poly (Poly.var 0) (by word_poly))

noncomputable def matching : Test ((F.linkP n np).prod ((Presented.fin r rp).prod Presented.bool))
    (fun w x => decide (x.2.2∈((S w).layout (n w)).matchLabels x.1 x.2.1)) where
  eval w i := F.domain.eval w (Nat.pair (F.wireCode (Nat.unpair i).1) (Nat.unpair i).2)
  correct w x := by
    simp only [Presented.prod_code,Nat.unpair_pair]
    change F.domain.eval w (Nat.pair (F.wireCode ((F.linkP n np).code w x.1))
      (Nat.pair x.2.1.val (NaturalCode.bool x.2.2)))=_
    rw [F.wireCode_eq n np]
    exact F.domain.correct w ((S w).wire (n w) x.1,x.2.1,x.2.2)
  poly := F.domain.eval_poly (Poly.var 0) (NatPoly.pair (by unfold wireCode; apply NatPoly.iteProp (by word_poly) (by word_poly); exact NatPoly.iteProp (by word_poly) (by word_poly) (by word_poly)) (by word_poly))

def secondLabelEval (w : Word) (l i a : ℕ) :=
  if l%2=0 then a else if (l/2)%2=0 then a else F.mapping w (l/2/2) i a

theorem secondLabelEval_eq (w : Word) (e : (S w).Link (n w)) (i : Fin (r w))
    (a : (((S w).layout (n w)).Match e i)) :
    F.secondLabelEval w ((F.linkP n np).code w e) i.val (NaturalCode.bool a.val)=
      NaturalCode.bool (((S w).layout (n w)).secondLabel e i a).val := by
  cases e with
  | inl e =>
    change F.secondLabelEval w (2*EP.code w e) i.val (NaturalCode.bool a.val)=NaturalCode.bool a.val
    simp [secondLabelEval]
  | inr e => cases e with
    | inl p =>
      change F.secondLabelEval w (2*(2*Nat.pair (EP.code w p.1) p.2.val)+1) i.val (NaturalCode.bool a.val)=NaturalCode.bool a.val
      simp [secondLabelEval,AffineRealizer.odd_half]
    | inr e =>
      change F.secondLabelEval w (2*(2*EP.code w e+1)+1) i.val (NaturalCode.bool a.val)=NaturalCode.bool ((S w).mapping e i a)
      simp only [secondLabelEval,show (2*(2*EP.code w e+1)+1)%2≠0 by omega,ite_false,AffineRealizer.odd_half,
        show (2*EP.code w e+1)%2≠0 by omega]
      exact F.mapping_eq w e i a

theorem mapping_poly_of {k} {w : (Fin k → Word) → Word} {e i a : (Fin k → Word) → ℕ}
    (hw : Poly w) (he : NatPoly e) (hi : NatPoly i) (ha : NatPoly a) :
    NatPoly (fun X => F.mapping (w X) (e X) (i X) (a X)) := by
  have h := F.mapping_poly.subst (g := ![w,fun X => unary (e X),fun X => unary (i X),fun X => unary (a X)])
    (by intro j; fin_cases j; exacts [hw,he,hi,ha])
  change NatPoly (fun X => F.mapping (w X) (unary (e X)).length (unary (i X)).length (unary (a X)).length) at h
  simpa only [unary,List.length_replicate] using h

noncomputable def firstForm : Number ((F.linkP n np).prod (Presented.bit.prod Presented.bit))
    (fun w x => (((S w).layout (n w)).firstForm x.1 (vectorTwo _ x.2)).val) where
  eval w i := if (Nat.unpair i).1%2=0 then F.left.eval w (Nat.pair ((Nat.unpair i).1/2) (Nat.unpair i).2)
    else (Nat.unpair (Nat.unpair i).2).1
  correct w x := by
    simp only [Presented.prod_code,Presented.bit_code,Nat.unpair_pair]
    rcases x with ⟨l,a,b⟩
    cases l with
    | inl e =>
      simp only [linkP,Presented.sum_inl_code]
      change (if (2*EP.code w e)%2=0 then F.left.eval w (Nat.pair ((2*EP.code w e)/2) (Nat.pair a.val b.val)) else _)=_
      simp only [Nat.mul_mod_right,ite_true,Nat.mul_div_cancel_left _ (by omega : 0<2)]
      exact F.left.correct w (e,a,b)
    | inr l => cases l with
      | inl p =>
        simp only [linkP,Presented.sum_inl_code,Presented.sum_inr_code,Presented.prod_code,Presented.fin_code]
        change (if (2*(2*Nat.pair (EP.code w p.1) p.2.val)+1)%2=0 then _ else a.val)=_
        simp only [show ∀ z : ℕ, (2*z+1)%2≠0 by omega,ite_false]
        rfl
      | inr e =>
        simp only [linkP,Presented.sum_inr_code]
        change (if (2*(2*EP.code w e+1)+1)%2=0 then _ else a.val)=_
        simp only [show ∀ z : ℕ, (2*z+1)%2≠0 by omega,ite_false]
        rfl
  poly := NatPoly.iteProp (by word_poly) (F.left.eval_poly (Poly.var 0) (by word_poly)) (by word_poly)

noncomputable def secondForm : Number ((F.linkP n np).prod (Presented.bit.prod Presented.bit))
    (fun w x => (((S w).layout (n w)).secondForm x.1 (vectorTwo _ x.2)).val) where
  eval w i := if (Nat.unpair i).1%2=0 then (Nat.unpair (Nat.unpair i).2).1
    else if ((Nat.unpair i).1/2)%2=0 then (Nat.unpair (Nat.unpair i).2).1
    else F.right.eval w (Nat.pair ((Nat.unpair i).1/2/2) (Nat.unpair i).2)
  correct w x := by
    simp only [Presented.prod_code,Presented.bit_code,Nat.unpair_pair]
    rcases x with ⟨l,a,b⟩
    cases l with
    | inl e =>
      simp only [linkP,Presented.sum_inl_code]
      change (if (2*EP.code w e)%2=0 then a.val else _)=_
      simp only [Nat.mul_mod_right,ite_true]
      rfl
    | inr l => cases l with
      | inl p =>
        simp only [linkP,Presented.sum_inl_code,Presented.sum_inr_code,Presented.prod_code,Presented.fin_code]
        change (if (2*(2*Nat.pair (EP.code w p.1) p.2.val)+1)%2=0 then a.val else if ((2*(2*Nat.pair (EP.code w p.1) p.2.val)+1)/2)%2=0 then a.val else _)=_
        simp only [show ∀ z : ℕ, (2*z+1)%2≠0 by omega,ite_false,AffineRealizer.odd_half,Nat.mul_mod_right,ite_true]
        rfl
      | inr e =>
        simp only [linkP,Presented.sum_inr_code]
        change (if (2*(2*EP.code w e+1)+1)%2=0 then a.val else if ((2*(2*EP.code w e+1)+1)/2)%2=0 then a.val else _)=_
        simp only [show (2*(2*EP.code w e+1)+1)%2≠0 by omega,ite_false,AffineRealizer.odd_half,
          show (2*EP.code w e+1)%2≠0 by omega]
        exact F.right.correct w (e,a,b)
  poly := NatPoly.iteProp (by word_poly) (by word_poly)
    (NatPoly.iteProp (by word_poly) (by word_poly) (F.right.eval_poly (Poly.var 0) (by word_poly)))

noncomputable def ring : RingRealizer (F.internalP n np) (F.linkP n np) r rp (fun w => (S w).layout (n w)) where
  typeIndex := F.internalIndex n np
  linkIndex := F.linkIndex n np
  dimension := F.internalDimension n np
  labels := F.labels n np
  matching := F.matching n np
  first := F.first n np
  second := F.second n np
  firstLabel := fun _ _ _ a => a
  secondLabel := F.secondLabelEval
  firstLabel_eq w e i a := by cases e with
    | inl e => rfl
    | inr e => cases e <;> rfl
  secondLabel_eq := F.secondLabelEval_eq n np
  firstLabel_poly := NatPoly.var 3
  secondLabel_poly := by
    unfold secondLabelEval
    exact NatPoly.iteProp (by word_poly) (NatPoly.var 3)
      (NatPoly.iteProp (by word_poly) (NatPoly.var 3) (F.mapping_poly_of (Poly.var 0) (by word_poly) (NatPoly.var 2) (NatPoly.var 3)))
  firstForm := F.firstForm n np
  secondForm := F.secondForm n np

end FinitePresentation.SchemaRealizer
end WLIdentification

end OAI

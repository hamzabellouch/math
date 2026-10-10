import OAI.Computability.WLIdentification.TypedArithmetic

namespace OAI

namespace WLIdentification
namespace FinitePresentation
open WordExpressions
attribute [local instance] Classical.propDecidable Classical.decEq

def vectorTwo (d : ℕ) (x : Bit × Bit) (j : Fin d) : Bit := if j.val=0 then x.1 else x.2

structure RingRealizer {T L : Word → Type} (TP : Presented T) (LP : Presented L)
    (r : Word → ℕ) (rp : NatPoly (fun S : Fin 1 → Word => r (S 0)))
    (R : ∀ w, RingLayout (r w) (T w) (L w)) where
  typeIndex : Number TP (fun w t => (R w).typeIndex t)
  linkIndex : Number LP (fun w e => (R w).linkIndex e)
  dimension : Number TP (fun w t => (R w).dimension t)
  labels : Test (TP.prod ((Presented.fin r rp).prod Presented.bool)) (fun w x => decide (x.2.2∈(R w).labels x.1 x.2.1))
  matching : Test (LP.prod ((Presented.fin r rp).prod Presented.bool)) (fun w x => decide (x.2.2∈(R w).matchLabels x.1 x.2.1))
  first : Map LP TP (fun w => (R w).first)
  second : Map LP TP (fun w => (R w).second)
  firstLabel : Word → ℕ → ℕ → ℕ → ℕ
  secondLabel : Word → ℕ → ℕ → ℕ → ℕ
  firstLabel_eq : ∀ w e i (a : (R w).Match e i), firstLabel w (LP.code w e) i.val (NaturalCode.bool a.val)=NaturalCode.bool ((R w).firstLabel e i a).val
  secondLabel_eq : ∀ w e i (a : (R w).Match e i), secondLabel w (LP.code w e) i.val (NaturalCode.bool a.val)=NaturalCode.bool ((R w).secondLabel e i a).val
  firstLabel_poly : NatPoly (fun S : Fin 4 → Word => firstLabel (S 0) (S 1).length (S 2).length (S 3).length)
  secondLabel_poly : NatPoly (fun S : Fin 4 → Word => secondLabel (S 0) (S 1).length (S 2).length (S 3).length)
  firstForm : Number (LP.prod (Presented.bit.prod Presented.bit)) (fun w x => ((R w).firstForm x.1 (vectorTwo _ x.2)).val)
  secondForm : Number (LP.prod (Presented.bit.prod Presented.bit)) (fun w x => ((R w).secondForm x.1 (vectorTwo _ x.2)).val)

namespace RingRealizer
variable {T L : Word → Type} {TP : Presented T} {LP : Presented L}
    {r : Word → ℕ} {rp : NatPoly (fun S : Fin 1 → Word => r (S 0))}
    {R : ∀ w, RingLayout (r w) (T w) (L w)} (F : RingRealizer TP LP r rp R)

abbrev rowP (_F : RingRealizer TP LP r rp R) := Presented.fin r rp
abbrev hBase := TP.prod (F.rowP.prod (Presented.bool.prod Presented.bool))
abbrev vBase := LP.prod (F.rowP.prod Presented.bool)
abbrev sBase := LP.prod (F.rowP.prod (Presented.bool.prod Presented.bool))

def nextRow (_F : RingRealizer TP LP r rp R) (w : Word) (i : ℕ) := if i+1<r w then i+1 else 0

theorem nextRow_eq (w : Word) (i : Fin (r w)) : F.nextRow w i.val=(finRotate (r w) i).val := by
  simp only [nextRow, CycleRows.rotate_val]

theorem nextRow_poly {n} {w : (Fin n → Word) → Word} {i : (Fin n → Word) → ℕ}
    (hw : Poly w) (hi : NatPoly i) : NatPoly (fun S => F.nextRow (w S) (i S)) := by
  unfold nextRow
  exact NatPoly.iteProp (NatPoly.lt (NatPoly.succ hi) (F.rowP.bound_poly_of hw)) (NatPoly.succ hi) (NatPoly.const 0)

def hAllowed (_F : RingRealizer TP LP r rp R) (w : Word) (h : T w × (Fin (r w) × (Bool × Bool))) : Prop :=
  h.2.2.1∈(R w).labels h.1 h.2.1 ∧ h.2.2.2∈(R w).labels h.1 (finRotate (r w) h.2.1)

def sAllowed (_F : RingRealizer TP LP r rp R) (w : Word) (h : L w × (Fin (r w) × (Bool × Bool))) : Prop :=
  h.2.2.1∈(R w).matchLabels h.1 h.2.1 ∧ h.2.2.2∈(R w).matchLabels h.1 (finRotate (r w) h.2.1)

@[simp] theorem hBase_code (w : Word) (x : T w × (Fin (r w) × (Bool × Bool))) :
    F.hBase.code w x=Nat.pair (TP.code w x.1) (Nat.pair x.2.1.val (Nat.pair (NaturalCode.bool x.2.2.1) (NaturalCode.bool x.2.2.2))) := rfl
@[simp] theorem sBase_code (w : Word) (x : L w × (Fin (r w) × (Bool × Bool))) :
    F.sBase.code w x=Nat.pair (LP.code w x.1) (Nat.pair x.2.1.val (Nat.pair (NaturalCode.bool x.2.2.1) (NaturalCode.bool x.2.2.2))) := rfl

def labelsPair (H : Test (TP.prod (F.rowP.prod Presented.bool)) (fun w x => decide (x.2.2∈(R w).labels x.1 x.2.1))) :
    Test F.hBase (fun w x => decide (F.hAllowed w x)) where
  eval w i := H.eval w (Nat.pair (Nat.unpair i).1 (Nat.pair (Nat.unpair (Nat.unpair i).2).1 (Nat.unpair (Nat.unpair (Nat.unpair i).2).2).1)) &&
    H.eval w (Nat.pair (Nat.unpair i).1 (Nat.pair (F.nextRow w (Nat.unpair (Nat.unpair i).2).1) (Nat.unpair (Nat.unpair (Nat.unpair i).2).2).2))
  correct w x := by
    simp only [F.hBase_code, Nat.unpair_pair, F.nextRow_eq]
    rw [show H.eval w (Nat.pair (TP.code w x.1) (Nat.pair x.2.1.val (NaturalCode.bool x.2.2.1)))=decide (x.2.2.1∈(R w).labels x.1 x.2.1) from H.correct w (x.1,x.2.1,x.2.2.1)]
    rw [show H.eval w (Nat.pair (TP.code w x.1) (Nat.pair (finRotate (r w) x.2.1).val (NaturalCode.bool x.2.2.2)))=decide (x.2.2.2∈(R w).labels x.1 (finRotate (r w) x.2.1)) from H.correct w (x.1,finRotate (r w) x.2.1,x.2.2.2)]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true,decide_eq_true_eq]
    rfl
  poly := BoolPoly.and (H.eval_poly (Poly.var 0)
    (NatPoly.pair (NatPoly.unpair_fst (NatPoly.var 1)) (NatPoly.pair
      (NatPoly.unpair_fst (NatPoly.unpair_snd (NatPoly.var 1)))
      (NatPoly.unpair_fst (NatPoly.unpair_snd (NatPoly.unpair_snd (NatPoly.var 1)))))))
    (H.eval_poly (Poly.var 0) (NatPoly.pair (NatPoly.unpair_fst (NatPoly.var 1))
      (NatPoly.pair (F.nextRow_poly (Poly.var 0) (NatPoly.unpair_fst (NatPoly.unpair_snd (NatPoly.var 1))))
      (NatPoly.unpair_snd (NatPoly.unpair_snd (NatPoly.unpair_snd (NatPoly.var 1)))))))

noncomputable def hEquiv (w : Word) : (R w).HName ≃ {h // F.hAllowed w h} where
  toFun h := ⟨(h.1,h.2.1,h.2.2.1.val,h.2.2.2.val),h.2.2.1.property,h.2.2.2.property⟩
  invFun h := ⟨h.val.1,h.val.2.1,⟨h.val.2.2.1,h.property.1⟩,⟨h.val.2.2.2,h.property.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def hP : Presented (fun w => (R w).HName) :=
  (F.hBase.restrict F.hAllowed (F.labelsPair F.labels)).retype F.hEquiv

@[simp] theorem hP_code (w : Word) (h : (R w).HName) : F.hP.code w h=
    Nat.pair (TP.code w h.1) (Nat.pair h.2.1.val (Nat.pair (NaturalCode.bool h.2.2.1.val) (NaturalCode.bool h.2.2.2.val))) := rfl

def matchingPair (H : Test (LP.prod (F.rowP.prod Presented.bool)) (fun w x => decide (x.2.2∈(R w).matchLabels x.1 x.2.1))) :
    Test F.sBase (fun w x => decide (F.sAllowed w x)) where
  eval w i := H.eval w (Nat.pair (Nat.unpair i).1 (Nat.pair (Nat.unpair (Nat.unpair i).2).1 (Nat.unpair (Nat.unpair (Nat.unpair i).2).2).1)) &&
    H.eval w (Nat.pair (Nat.unpair i).1 (Nat.pair (F.nextRow w (Nat.unpair (Nat.unpair i).2).1) (Nat.unpair (Nat.unpair (Nat.unpair i).2).2).2))
  correct w x := by
    simp only [F.sBase_code, Nat.unpair_pair, F.nextRow_eq]
    rw [show H.eval w (Nat.pair (LP.code w x.1) (Nat.pair x.2.1.val (NaturalCode.bool x.2.2.1)))=decide (x.2.2.1∈(R w).matchLabels x.1 x.2.1) from H.correct w (x.1,x.2.1,x.2.2.1)]
    rw [show H.eval w (Nat.pair (LP.code w x.1) (Nat.pair (finRotate (r w) x.2.1).val (NaturalCode.bool x.2.2.2)))=decide (x.2.2.2∈(R w).matchLabels x.1 (finRotate (r w) x.2.1)) from H.correct w (x.1,finRotate (r w) x.2.1,x.2.2.2)]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.and_eq_true,decide_eq_true_eq]
    rfl
  poly := BoolPoly.and (H.eval_poly (Poly.var 0)
    (NatPoly.pair (NatPoly.unpair_fst (NatPoly.var 1)) (NatPoly.pair
      (NatPoly.unpair_fst (NatPoly.unpair_snd (NatPoly.var 1)))
      (NatPoly.unpair_fst (NatPoly.unpair_snd (NatPoly.unpair_snd (NatPoly.var 1)))))))
    (H.eval_poly (Poly.var 0) (NatPoly.pair (NatPoly.unpair_fst (NatPoly.var 1))
      (NatPoly.pair (F.nextRow_poly (Poly.var 0) (NatPoly.unpair_fst (NatPoly.unpair_snd (NatPoly.var 1))))
      (NatPoly.unpair_snd (NatPoly.unpair_snd (NatPoly.unpair_snd (NatPoly.var 1)))))))

noncomputable def sEquiv (w : Word) : (R w).Square ≃ {h // F.sAllowed w h} where
  toFun h := ⟨(h.1,h.2.1,h.2.2.1.val,h.2.2.2.val),h.2.2.1.property,h.2.2.2.property⟩
  invFun h := ⟨h.val.1,h.val.2.1,⟨h.val.2.2.1,h.property.1⟩,⟨h.val.2.2.2,h.property.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def sP : Presented (fun w => (R w).Square) :=
  (F.sBase.restrict F.sAllowed (F.matchingPair F.matching)).retype F.sEquiv

@[simp] theorem sP_code (w : Word) (h : (R w).Square) : F.sP.code w h=
    Nat.pair (LP.code w h.1) (Nat.pair h.2.1.val (Nat.pair (NaturalCode.bool h.2.2.1.val) (NaturalCode.bool h.2.2.2.val))) := rfl

noncomputable def vEquiv (w : Word) : (R w).VName ≃ {h : L w × (Fin (r w) × Bool) // h.2.2∈(R w).matchLabels h.1 h.2.1} where
  toFun h := ⟨(h.1,h.2.1,h.2.2.val),h.2.2.property⟩
  invFun h := ⟨h.val.1,h.val.2.1,⟨h.val.2.2,h.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def vP : Presented (fun w => (R w).VName) :=
  (F.vBase.restrict (fun w h => h.2.2∈(R w).matchLabels h.1 h.2.1) F.matching).retype (vEquiv (R := R))

@[simp] theorem vP_code (w : Word) (h : (R w).VName) : F.vP.code w h=
    Nat.pair (LP.code w h.1) (Nat.pair h.2.1.val (NaturalCode.bool h.2.2.val)) := rfl

noncomputable def hDim : Number F.hP (fun w x => (R w).dimension x.1) where
  eval w i := F.dimension.eval w (Nat.unpair i).1
  correct w x := by rw [F.hP_code,Nat.unpair_pair]; exact F.dimension.correct w x.1
  poly := F.dimension.eval_poly (Poly.var 0) (by word_poly)

noncomputable def cP : Presented (fun w => (R w).Coordinate) := (F.hP.finSigma F.hDim).sum F.vP
noncomputable def bP : Presented (fun w => (R w).Block) := F.hP.sum F.sP

@[simp] theorem cP_inl (w : Word) (h : Σ h : (R w).HName, Fin ((R w).dimension h.1)) :
    F.cP.code w (.inl h)=2*Nat.pair (F.hP.code w h.1) h.2.val := rfl
@[simp] theorem cP_inr (w : Word) (v : (R w).VName) : F.cP.code w (.inr v)=2*F.vP.code w v+1 := rfl
@[simp] theorem bP_inl (w : Word) (h : (R w).HName) : F.bP.code w (.inl h)=2*F.hP.code w h := rfl
@[simp] theorem bP_inr (w : Word) (b : (R w).Square) : F.bP.code w (.inr b)=2*F.sP.code w b+1 := rfl

end RingRealizer
end FinitePresentation

end WLIdentification

end OAI

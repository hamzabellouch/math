import OAI.Computability.WLIdentification.RingMembership

namespace OAI

namespace WLIdentification
namespace FinitePresentation.RingRealizer
open WordExpressions
attribute [local instance] Classical.propDecidable Classical.decEq
variable {T L : Word → Type} {TP : Presented T} {LP : Presented L}
    {r : Word → ℕ} {rp : NatPoly (fun S : Fin 1 → Word => r (S 0))}
    {R : ∀ w, RingLayout (r w) (T w) (L w)} (F : RingRealizer TP LP r rp R)

noncomputable def readH (w : Word) (b v h j : ℕ) : ℕ := F.localData.read w b v (2*Nat.pair h j)
noncomputable def readV (w : Word) (b v c : ℕ) : ℕ := F.localData.read w b v (2*c+1)

theorem readH_cast (w : Word) (b v h j : ℕ) : ((F.readH w b v h j : ℕ) : Bit).val=F.readH w b v h j := by
  simp only [readH,Locals.read,NumericKernel.digit,ZMod.val_natCast,Nat.mod_mod]

theorem leftVector (w : Word) (b : (R w).Square) (v : F.localData.Value w (.inr b)) :
    vectorTwo ((R w).dimension ((R w).first b.1))
      ((F.readH w (F.bP.code w (.inr b)) (F.localData.valueCode w (.inr b) v) (F.hP.code w ((R w).leftH b)) 0 : Bit),
       (F.readH w (F.bP.code w (.inr b)) (F.localData.valueCode w (.inr b) v) (F.hP.code w ((R w).leftH b)) 1 : Bit)) =
      fun j => v ⟨.inl ⟨(R w).leftH b,j⟩,(R w).left_mem b j⟩ := by
  funext j
  apply ZMod.val_injective 2
  have hj : j.val=0 ∨ j.val=1 := by
    have hd := (R w).dimension_bound ((R w).first b.1)
    have hi := j.isLt
    rcases hd with hd|hd <;> omega
  have hh := F.localData.read_value w (.inr b) v ⟨.inl ⟨(R w).leftH b,j⟩,(R w).left_mem b j⟩
  change F.readH w (F.bP.code w (.inr b)) (F.localData.valueCode w (.inr b) v) (F.hP.code w ((R w).leftH b)) j.val=_ at hh
  rcases hj with hj|hj <;> simp only [vectorTwo,hj,reduceIte,Nat.one_ne_zero,F.readH_cast] <;> simpa only [hj] using hh

theorem rightVector (w : Word) (b : (R w).Square) (v : F.localData.Value w (.inr b)) :
    vectorTwo ((R w).dimension ((R w).second b.1))
      ((F.readH w (F.bP.code w (.inr b)) (F.localData.valueCode w (.inr b) v) (F.hP.code w ((R w).rightH b)) 0 : Bit),
       (F.readH w (F.bP.code w (.inr b)) (F.localData.valueCode w (.inr b) v) (F.hP.code w ((R w).rightH b)) 1 : Bit)) =
      fun j => v ⟨.inl ⟨(R w).rightH b,j⟩,(R w).right_mem b j⟩ := by
  funext j
  apply ZMod.val_injective 2
  have hj : j.val=0 ∨ j.val=1 := by
    have hd := (R w).dimension_bound ((R w).second b.1)
    have hi := j.isLt
    rcases hd with hd|hd <;> omega
  have hh := F.localData.read_value w (.inr b) v ⟨.inl ⟨(R w).rightH b,j⟩,(R w).right_mem b j⟩
  change F.readH w (F.bP.code w (.inr b)) (F.localData.valueCode w (.inr b) v) (F.hP.code w ((R w).rightH b)) j.val=_ at hh
  rcases hj with hj|hj <;> simp only [vectorTwo,hj,reduceIte,Nat.one_ne_zero,F.readH_cast] <;> simpa only [hj] using hh

noncomputable def firstTerm (w : Word) (b v : ℕ) := F.firstForm.eval w (Nat.pair (Nat.unpair b).1
  (Nat.pair (F.readH w (2*b+1) v (F.leftCode w b) 0) (F.readH w (2*b+1) v (F.leftCode w b) 1)))
noncomputable def secondTerm (w : Word) (b v : ℕ) := F.secondForm.eval w (Nat.pair (Nat.unpair b).1
  (Nat.pair (F.readH w (2*b+1) v (F.rightCode w b) 0) (F.readH w (2*b+1) v (F.rightCode w b) 1)))

theorem firstTerm_eq (w : Word) (b : (R w).Square) (v : F.localData.Value w (.inr b)) :
    F.firstTerm w (F.sP.code w b) (F.localData.valueCode w (.inr b) v)=
      ((R w).firstForm b.1 (fun j => v ⟨.inl ⟨(R w).leftH b,j⟩,(R w).left_mem b j⟩)).val := by
  let a := F.readH w (F.bP.code w (.inr b)) (F.localData.valueCode w (.inr b) v) (F.hP.code w ((R w).leftH b)) 0
  let c := F.readH w (F.bP.code w (.inr b)) (F.localData.valueCode w (.inr b) v) (F.hP.code w ((R w).leftH b)) 1
  have h := F.firstForm.correct w (b.1,(a : Bit),(c : Bit))
  change F.firstForm.eval w (Nat.pair (LP.code w b.1) (Nat.pair (a : Bit).val (c : Bit).val))=_ at h
  simp only [a,c,F.readH_cast] at h
  rw [F.leftVector] at h
  unfold firstTerm
  rw [F.leftCode_eq]
  have he : (Nat.unpair (F.sP.code w b)).1=LP.code w b.1 := by rw [F.sP_code,Nat.unpair_pair]
  rw [he]
  exact h

theorem secondTerm_eq (w : Word) (b : (R w).Square) (v : F.localData.Value w (.inr b)) :
    F.secondTerm w (F.sP.code w b) (F.localData.valueCode w (.inr b) v)=
      ((R w).secondForm b.1 (fun j => v ⟨.inl ⟨(R w).rightH b,j⟩,(R w).right_mem b j⟩)).val := by
  let a := F.readH w (F.bP.code w (.inr b)) (F.localData.valueCode w (.inr b) v) (F.hP.code w ((R w).rightH b)) 0
  let c := F.readH w (F.bP.code w (.inr b)) (F.localData.valueCode w (.inr b) v) (F.hP.code w ((R w).rightH b)) 1
  have h := F.secondForm.correct w (b.1,(a : Bit),(c : Bit))
  change F.secondForm.eval w (Nat.pair (LP.code w b.1) (Nat.pair (a : Bit).val (c : Bit).val))=_ at h
  simp only [a,c,F.readH_cast] at h
  rw [F.rightVector] at h
  unfold secondTerm
  rw [F.rightCode_eq]
  have he : (Nat.unpair (F.sP.code w b)).1=LP.code w b.1 := by rw [F.sP_code,Nat.unpair_pair]
  rw [he]
  exact h

noncomputable def formEval (w : Word) (b v : ℕ) : ℕ :=
  (F.firstTerm w b v + F.secondTerm w b v + F.readV w (2*b+1) v (F.topCode b) +
    F.readV w (2*b+1) v (F.bottomCode w b))%2

theorem formEval_eq (w : Word) (b : (R w).Square) (v : F.localData.Value w (.inr b)) :
    F.formEval w (F.sP.code w b) (F.localData.valueCode w (.inr b) v)=((R w).squareForm b v).val := by
  rw [formEval,F.firstTerm_eq,F.secondTerm_eq,F.topCode_eq,F.bottomCode_eq]
  have ht := F.localData.read_value w (.inr b) v ⟨.inr ((R w).topV b),(R w).top_mem b⟩
  have hb := F.localData.read_value w (.inr b) v ⟨.inr ((R w).bottomV b),(R w).bottom_mem b⟩
  change F.readV w (2*F.sP.code w b+1) (F.localData.valueCode w (.inr b) v) (F.vP.code w ((R w).topV b))=_ at ht
  change F.readV w (2*F.sP.code w b+1) (F.localData.valueCode w (.inr b) v) (F.vP.code w ((R w).bottomV b))=_ at hb
  rw [ht,hb]
  have h := congrArg ZMod.val ((R w).squareForm_apply b v)
  dsimp only [localData, Locals.Value, RingLayout.leftH, RingLayout.rightH] at *
  simpa only [ZMod.val_add,Nat.add_mod_mod,Nat.mod_add_mod] using h.symm

theorem readH_poly {n} {w : (Fin n → Word) → Word} {b v h j : (Fin n → Word) → ℕ}
    (hw : Poly w) (hb : NatPoly b) (hv : NatPoly v) (hh : NatPoly h) (hj : NatPoly j) :
    NatPoly (fun S => F.readH (w S) (b S) (v S) (h S) (j S)) :=
  F.localData.read_poly hw hb hv (NatPoly.mul (NatPoly.const 2) (NatPoly.pair hh hj))
theorem readV_poly {n} {w : (Fin n → Word) → Word} {b v h : (Fin n → Word) → ℕ}
    (hw : Poly w) (hb : NatPoly b) (hv : NatPoly v) (hh : NatPoly h) :
    NatPoly (fun S => F.readV (w S) (b S) (v S) (h S)) :=
  F.localData.read_poly hw hb hv (NatPoly.add (NatPoly.mul (NatPoly.const 2) hh) (NatPoly.const 1))

theorem firstTerm_poly {n} {w : (Fin n → Word) → Word} {b v : (Fin n → Word) → ℕ}
    (hw : Poly w) (hb : NatPoly b) (hv : NatPoly v) : NatPoly (fun S => F.firstTerm (w S) (b S) (v S)) :=
  F.firstForm.eval_poly hw (NatPoly.pair (NatPoly.unpair_fst hb) (NatPoly.pair
    (F.readH_poly hw (NatPoly.add (NatPoly.mul (NatPoly.const 2) hb) (NatPoly.const 1)) hv (F.leftCode_poly hw hb) (NatPoly.const 0))
    (F.readH_poly hw (NatPoly.add (NatPoly.mul (NatPoly.const 2) hb) (NatPoly.const 1)) hv (F.leftCode_poly hw hb) (NatPoly.const 1))))
theorem secondTerm_poly {n} {w : (Fin n → Word) → Word} {b v : (Fin n → Word) → ℕ}
    (hw : Poly w) (hb : NatPoly b) (hv : NatPoly v) : NatPoly (fun S => F.secondTerm (w S) (b S) (v S)) :=
  F.secondForm.eval_poly hw (NatPoly.pair (NatPoly.unpair_fst hb) (NatPoly.pair
    (F.readH_poly hw (NatPoly.add (NatPoly.mul (NatPoly.const 2) hb) (NatPoly.const 1)) hv (F.rightCode_poly hw hb) (NatPoly.const 0))
    (F.readH_poly hw (NatPoly.add (NatPoly.mul (NatPoly.const 2) hb) (NatPoly.const 1)) hv (F.rightCode_poly hw hb) (NatPoly.const 1))))

theorem formEval_poly {n} {w : (Fin n → Word) → Word} {b v : (Fin n → Word) → ℕ}
    (hw : Poly w) (hb : NatPoly b) (hv : NatPoly v) : NatPoly (fun S => F.formEval (w S) (b S) (v S)) := by
  unfold formEval
  apply NatPoly.mod _ (NatPoly.const 2)
  apply NatPoly.add
  · apply NatPoly.add (NatPoly.add (F.firstTerm_poly hw hb hv) (F.secondTerm_poly hw hb hv))
    apply F.readV_poly hw (NatPoly.add (NatPoly.mul (NatPoly.const 2) hb) (NatPoly.const 1)) hv
    exact NatPoly.pair (NatPoly.unpair_fst hb) (NatPoly.pair (NatPoly.unpair_fst (NatPoly.unpair_snd hb))
      (NatPoly.unpair_fst (NatPoly.unpair_snd (NatPoly.unpair_snd hb))))
  · apply F.readV_poly hw (NatPoly.add (NatPoly.mul (NatPoly.const 2) hb) (NatPoly.const 1)) hv
    exact NatPoly.pair (NatPoly.unpair_fst hb) (NatPoly.pair
      (F.nextRow_poly hw (NatPoly.unpair_fst (NatPoly.unpair_snd hb)))
      (NatPoly.unpair_snd (NatPoly.unpair_snd (NatPoly.unpair_snd hb))))

variable [∀ w,Fintype (T w)] [∀ w,Fintype (L w)]
    (hr : ∀ w, 2≤r w)

noncomputable def legal : Test F.localData.values (fun w x => decide (((R w).affine (hr w)).Legal 0 x.1 x.2)) where
  eval w i := if (Nat.unpair i).1%2=0 then true else decide (F.formEval w ((Nat.unpair i).1/2) (Nat.unpair i).2=0)
  correct w x := by
    rcases x with ⟨b,v⟩
    have hc : F.localData.values.code w ⟨b,v⟩=Nat.pair (F.bP.code w b) (F.localData.valueCode w b v) := rfl
    change (if (Nat.unpair (F.localData.values.code w ⟨b,v⟩)).1%2=0 then true else decide (F.formEval w ((Nat.unpair (F.localData.values.code w ⟨b,v⟩)).1/2) (Nat.unpair (F.localData.values.code w ⟨b,v⟩)).2=0))=_
    rw [hc,Nat.unpair_pair]
    cases b with
    | inl h =>
      rw [F.bP_inl]
      simp only [Nat.mul_mod_right,ite_true]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq, true_iff]
      intro hf
      change false=true at hf
      contradiction
    | inr b =>
      rw [F.bP_inr]
      simp only [show (2*F.sP.code w b+1)%2≠0 by omega,ite_false,AffineRealizer.odd_half,F.formEval_eq]
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      change ((R w).squareForm b v).val=0 ↔ (true=true → (R w).squareForm b v=0)
      constructor
      · intro h _
        exact ZMod.val_injective 2 h
      · intro h
        exact congrArg ZMod.val (h rfl)
  poly := BoolPoly.iteProp (NatPoly.eqtest (NatPoly.mod (NatPoly.unpair_fst (NatPoly.var 1)) (NatPoly.const 2)) (NatPoly.const 0))
    (BoolPoly.const true) (NatPoly.eqtest (F.formEval_poly (Poly.var 0)
      (NatPoly.div (NatPoly.unpair_fst (NatPoly.var 1)) (NatPoly.const 2)) (NatPoly.unpair_snd (NatPoly.var 1))) (NatPoly.const 0))

noncomputable def affine : AffineRealizer F.cP F.bP (fun w => (R w).affine (hr w)) where
  size w b := (R w).coordinates_card b
  member := F.member
  legal := F.legal hr
  color := F.colors

end FinitePresentation.RingRealizer
end WLIdentification

end OAI

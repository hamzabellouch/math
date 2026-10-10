import OAI.Computability.WLIdentification.RingPresentation

namespace OAI

namespace WLIdentification
namespace FinitePresentation.RingRealizer
open WordExpressions
attribute [local instance] Classical.propDecidable Classical.decEq
variable {T L : Word → Type} {TP : Presented T} {LP : Presented L}
    {r : Word → ℕ} {rp : NatPoly (fun S : Fin 1 → Word => r (S 0))}
    {R : ∀ w, RingLayout (r w) (T w) (L w)} (F : RingRealizer TP LP r rp R)

theorem firstLabel_poly_of {n} {w : (Fin n → Word) → Word} {e i a : (Fin n → Word) → ℕ}
    (hw : Poly w) (he : NatPoly e) (hi : NatPoly i) (ha : NatPoly a) :
    NatPoly (fun S => F.firstLabel (w S) (e S) (i S) (a S)) := by
  have h := F.firstLabel_poly.subst (g := ![w,fun S => unary (e S),fun S => unary (i S),fun S => unary (a S)])
    (by intro j; fin_cases j; exacts [hw,he,hi,ha])
  change NatPoly (fun S => F.firstLabel (w S) (unary (e S)).length (unary (i S)).length (unary (a S)).length) at h
  simpa only [unary, List.length_replicate] using h

theorem secondLabel_poly_of {n} {w : (Fin n → Word) → Word} {e i a : (Fin n → Word) → ℕ}
    (hw : Poly w) (he : NatPoly e) (hi : NatPoly i) (ha : NatPoly a) :
    NatPoly (fun S => F.secondLabel (w S) (e S) (i S) (a S)) := by
  have h := F.secondLabel_poly.subst (g := ![w,fun S => unary (e S),fun S => unary (i S),fun S => unary (a S)])
    (by intro j; fin_cases j; exacts [hw,he,hi,ha])
  change NatPoly (fun S => F.secondLabel (w S) (unary (e S)).length (unary (i S)).length (unary (a S)).length) at h
  simpa only [unary, List.length_replicate] using h

def leftCode (w : Word) (b : ℕ) : ℕ :=
  Nat.pair (F.first.eval w (Nat.unpair b).1) (Nat.pair (Nat.unpair (Nat.unpair b).2).1
    (Nat.pair (F.firstLabel w (Nat.unpair b).1 (Nat.unpair (Nat.unpair b).2).1 (Nat.unpair (Nat.unpair (Nat.unpair b).2).2).1)
      (F.firstLabel w (Nat.unpair b).1 (F.nextRow w (Nat.unpair (Nat.unpair b).2).1) (Nat.unpair (Nat.unpair (Nat.unpair b).2).2).2)))

def rightCode (w : Word) (b : ℕ) : ℕ :=
  Nat.pair (F.second.eval w (Nat.unpair b).1) (Nat.pair (Nat.unpair (Nat.unpair b).2).1
    (Nat.pair (F.secondLabel w (Nat.unpair b).1 (Nat.unpair (Nat.unpair b).2).1 (Nat.unpair (Nat.unpair (Nat.unpair b).2).2).1)
      (F.secondLabel w (Nat.unpair b).1 (F.nextRow w (Nat.unpair (Nat.unpair b).2).1) (Nat.unpair (Nat.unpair (Nat.unpair b).2).2).2)))

def topCode (_F : RingRealizer TP LP r rp R) (b : ℕ) : ℕ :=
  Nat.pair (Nat.unpair b).1 (Nat.pair (Nat.unpair (Nat.unpair b).2).1 (Nat.unpair (Nat.unpair (Nat.unpair b).2).2).1)
def bottomCode (w : Word) (b : ℕ) : ℕ :=
  Nat.pair (Nat.unpair b).1 (Nat.pair (F.nextRow w (Nat.unpair (Nat.unpair b).2).1) (Nat.unpair (Nat.unpair (Nat.unpair b).2).2).2)

theorem leftCode_eq (w : Word) (b : (R w).Square) : F.leftCode w (F.sP.code w b)=F.hP.code w ((R w).leftH b) := by
  simp only [leftCode,F.sP_code,Nat.unpair_pair,F.nextRow_eq,F.firstLabel_eq]
  rw [F.first.correct]
  rfl

theorem rightCode_eq (w : Word) (b : (R w).Square) : F.rightCode w (F.sP.code w b)=F.hP.code w ((R w).rightH b) := by
  simp only [rightCode,F.sP_code,Nat.unpair_pair,F.nextRow_eq,F.secondLabel_eq]
  rw [F.second.correct]
  rfl

theorem topCode_eq (w : Word) (b : (R w).Square) : F.topCode (F.sP.code w b)=F.vP.code w ((R w).topV b) := by
  simp only [topCode,F.sP_code,Nat.unpair_pair]
  rfl

theorem bottomCode_eq (w : Word) (b : (R w).Square) : F.bottomCode w (F.sP.code w b)=F.vP.code w ((R w).bottomV b) := by
  simp only [bottomCode,F.sP_code,Nat.unpair_pair,F.nextRow_eq]
  rfl

theorem leftCode_poly {n} {w : (Fin n → Word) → Word} {b : (Fin n → Word) → ℕ}
    (hw : Poly w) (hb : NatPoly b) : NatPoly (fun S => F.leftCode (w S) (b S)) := by
  unfold leftCode
  apply NatPoly.pair (F.first.eval_poly hw (NatPoly.unpair_fst hb))
  apply NatPoly.pair (NatPoly.unpair_fst (NatPoly.unpair_snd hb))
  apply NatPoly.pair
  · exact F.firstLabel_poly_of hw (NatPoly.unpair_fst hb) (NatPoly.unpair_fst (NatPoly.unpair_snd hb))
      (NatPoly.unpair_fst (NatPoly.unpair_snd (NatPoly.unpair_snd hb)))
  · exact F.firstLabel_poly_of hw (NatPoly.unpair_fst hb) (F.nextRow_poly hw (NatPoly.unpair_fst (NatPoly.unpair_snd hb)))
      (NatPoly.unpair_snd (NatPoly.unpair_snd (NatPoly.unpair_snd hb)))

theorem rightCode_poly {n} {w : (Fin n → Word) → Word} {b : (Fin n → Word) → ℕ}
    (hw : Poly w) (hb : NatPoly b) : NatPoly (fun S => F.rightCode (w S) (b S)) := by
  unfold rightCode
  apply NatPoly.pair (F.second.eval_poly hw (NatPoly.unpair_fst hb))
  apply NatPoly.pair (NatPoly.unpair_fst (NatPoly.unpair_snd hb))
  apply NatPoly.pair
  · exact F.secondLabel_poly_of hw (NatPoly.unpair_fst hb) (NatPoly.unpair_fst (NatPoly.unpair_snd hb))
      (NatPoly.unpair_fst (NatPoly.unpair_snd (NatPoly.unpair_snd hb)))
  · exact F.secondLabel_poly_of hw (NatPoly.unpair_fst hb) (F.nextRow_poly hw (NatPoly.unpair_fst (NatPoly.unpair_snd hb)))
      (NatPoly.unpair_snd (NatPoly.unpair_snd (NatPoly.unpair_snd hb)))

variable [∀ w, Fintype (T w)] [∀ w, Fintype (L w)]
noncomputable def hIndex : Number F.hP (fun w x => (R w).hIndex x) where
  eval w i := Nat.pair (F.typeIndex.eval w (Nat.unpair i).1) (Nat.unpair i).2
  correct w x := by rw [F.hP_code,Nat.unpair_pair,F.typeIndex.correct]; rfl
  poly := NatPoly.pair (F.typeIndex.eval_poly (Poly.var 0) (by word_poly)) (by word_poly)
noncomputable def vIndex : Number F.vP (fun w x => (R w).vIndex x) where
  eval w i := Nat.pair (F.linkIndex.eval w (Nat.unpair i).1) (Nat.unpair i).2
  correct w x := by rw [F.vP_code,Nat.unpair_pair,F.linkIndex.correct]; rfl
  poly := NatPoly.pair (F.linkIndex.eval_poly (Poly.var 0) (by word_poly)) (by word_poly)
noncomputable def sIndex : Number F.sP (fun w x => (R w).squareIndex x) where
  eval w i := Nat.pair (F.linkIndex.eval w (Nat.unpair i).1) (Nat.unpair i).2
  correct w x := by rw [F.sP_code,Nat.unpair_pair,F.linkIndex.correct]; rfl
  poly := NatPoly.pair (F.linkIndex.eval_poly (Poly.var 0) (by word_poly)) (by word_poly)

noncomputable def hcIndex : Number (F.hP.finSigma F.hDim) (fun w x => Nat.pair ((R w).hIndex x.1) x.2.val) where
  eval w i := Nat.pair (F.hIndex.eval w (Nat.unpair i).1) (Nat.unpair i).2
  correct w x := by
    change Nat.pair (F.hIndex.eval w (Nat.unpair (Nat.pair _ _)).1) (Nat.unpair (Nat.pair _ _)).2=_
    rw [Nat.unpair_pair,F.hIndex.correct]
    rfl
  poly := NatPoly.pair (F.hIndex.eval_poly (Poly.var 0) (by word_poly)) (by word_poly)

noncomputable def colors : Number (F.cP.sum F.bP) (fun w x => (R w).colorIndex x) := by
  let hc := (Number.const (F.hP.finSigma F.hDim) 2).mul F.hcIndex
  let vc := ((Number.const F.vP 2).mul F.vIndex).add (Number.const F.vP 1)
  let bc := Number.sumCases ((Number.const F.hP 2).mul F.hIndex) (((Number.const F.sP 2).mul F.sIndex).add (Number.const F.sP 1))
  exact (Number.sumCases ((Number.const F.cP 2).mul (Number.sumCases hc vc))
    (((Number.const F.bP 2).mul bc).add (Number.const F.bP 1))).congr (by intro w x; cases x with
      | inl c => cases c <;> rfl
      | inr b => cases b <;> rfl)

end FinitePresentation.RingRealizer
end WLIdentification

end OAI

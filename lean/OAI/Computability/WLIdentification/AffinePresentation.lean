import OAI.Computability.WLIdentification.LeafPresentation

namespace OAI

namespace WLIdentification
namespace FinitePresentation
open WordExpressions

noncomputable def Presented.bit : Presented (fun _ => Bit) :=
  (Presented.fin (fun _ => 2) (NatPoly.const 2)).retype (fun _ => (ZMod.finEquiv 2).toEquiv.symm)

@[simp] theorem Presented.bit_code (w : Word) (x : Bit) : Presented.bit.code w x=x.val := rfl

variable {C B : Word → Type} [∀ w, Fintype (C w)] [∀ w, DecidableEq (C w)]
    (CP : Presented C) (BP : Presented B) (D : ∀ w, AffineBlocks (C w) (B w))

def affineLocals (size : ∀ w b, ((D w).coordinates b).card≤5)
    (member : Test (BP.prod CP) (fun w p => decide (p.2∈(D w).coordinates p.1))) : Locals CP BP :=
  ⟨fun w => (D w).coordinates, size, member⟩

attribute [local instance] Classical.propDecidable

structure AffineRealizer where
  size : ∀ w b, ((D w).coordinates b).card≤5
  member : Test (BP.prod CP) (fun w p => decide (p.2∈(D w).coordinates p.1))
  legal : Test (affineLocals CP BP D size member).values (fun w v => decide ((D w).Legal 0 v.1 v.2))
  color : Number (CP.sum BP) (fun w x => (D w).colorIndex x)

namespace AffineRealizer
variable {CP BP D} (F : AffineRealizer CP BP D)

abbrev localData : Locals CP BP := affineLocals CP BP D F.size F.member

noncomputable def legalEquiv (w : Word) :
    (Σ b, {v // (D w).Legal 0 b v}) ≃ {v : Σ b, (D w).Local b // (D w).Legal 0 v.1 v.2} where
  toFun v := ⟨⟨v.1,v.2.val⟩,v.2.property⟩
  invFun v := ⟨v.val.1,⟨v.val.2,v.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def legalPoints : Presented (fun w => Σ b, {v // (D w).Legal 0 b v}) :=
  (F.localData.values.restrict (fun w v => (D w).Legal 0 v.1 v.2) F.legal).retype (legalEquiv (D := D))

noncomputable def vertices : Presented (fun w => (D w).Vertex 0) :=
  (CP.prod Presented.bit).sum F.legalPoints

@[simp] theorem legalPoints_code (w : Word) (v : Σ b, {x // (D w).Legal 0 b x}) :
    F.legalPoints.code w v = Nat.pair (BP.code w v.1) (F.localData.valueCode w v.1 v.2.val) := rfl

@[simp] theorem vertices_code_inl (w : Word) (x : C w × Bit) :
    F.vertices.code w (.inl x) = 2*Nat.pair (CP.code w x.1) x.2.val := rfl

@[simp] theorem vertices_code_inr (w : Word) (x : Σ b, {v // (D w).Legal 0 b v}) :
    F.vertices.code w (.inr x) = 2*Nat.pair (BP.code w x.1) (F.localData.valueCode w x.1 x.2.val)+1 := rfl

def cross (w : Word) (i j : ℕ) : Bool :=
  F.member.eval w (Nat.pair (Nat.unpair j).1 (Nat.unpair i).1) &&
    decide (F.localData.read w (Nat.unpair j).1 (Nat.unpair j).2 (Nat.unpair i).1=(Nat.unpair i).2)

theorem cross_correct (w : Word) (p : C w × Bit) (v : Σ b, {x // (D w).Legal 0 b x}) :
    F.cross w ((CP.prod Presented.bit).code w p) (F.legalPoints.code w v)=true ↔
    ∃ h : p.1∈(D w).coordinates v.1, v.2.val ⟨p.1,h⟩=p.2 := by
  change F.cross w (Nat.pair (CP.code w p.1) p.2.val) (Nat.pair (BP.code w v.1) (F.localData.valueCode w v.1 v.2.val))=true ↔ _
  simp only [cross, Nat.unpair_pair]
  have hm := F.member.correct w (v.1,p.1)
  change F.member.eval w (Nat.pair (BP.code w v.1) (CP.code w p.1))=decide (p.1∈(D w).coordinates v.1) at hm
  rw [hm, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
  constructor
  · rintro ⟨h,he⟩
    refine ⟨h,?_⟩
    rw [F.localData.read_value w v.1 v.2.val ⟨p.1,h⟩] at he
    exact ZMod.val_injective 2 he
  · rintro ⟨h,he⟩
    refine ⟨h,?_⟩
    rw [F.localData.read_value w v.1 v.2.val ⟨p.1,h⟩]
    exact congrArg ZMod.val he

theorem cross_poly {n} {w : (Fin n → Word) → Word} {i j : (Fin n → Word) → ℕ}
    (hw : Poly w) (hi : NatPoly i) (hj : NatPoly j) : BoolPoly (fun S => F.cross (w S) (i S) (j S)) := by
  apply BoolPoly.and
  · exact F.member.eval_poly hw (NatPoly.pair (NatPoly.unpair_fst hj) (NatPoly.unpair_fst hi))
  · exact NatPoly.eqtest (F.localData.read_poly hw (NatPoly.unpair_fst hj) (NatPoly.unpair_snd hj)
      (NatPoly.unpair_fst hi)) (NatPoly.unpair_snd hi)

@[simp] theorem odd_half (n : ℕ) : (2*n+1)/2=n := by omega

def adjacent (w : Word) (i j : ℕ) : Bool :=
  if i%2=0 then if j%2=0 then false else F.cross w (i/2) (j/2)
  else if j%2=0 then F.cross w (j/2) (i/2) else false

noncomputable def base : PresentedGraph F.vertices (fun w => (D w).baseGraph 0) where
  adjacent := F.adjacent
  adjacent_iff w x y := by
    cases x with
    | inl x => cases y with
      | inl y =>
        change F.adjacent w (2*(CP.prod Presented.bit).code w x) (2*(CP.prod Presented.bit).code w y)=true ↔ False
        simp [adjacent]
      | inr y =>
        change F.adjacent w (2*(CP.prod Presented.bit).code w x) (2*F.legalPoints.code w y+1)=true ↔ _
        simpa [AffineBlocks.baseGraph, adjacent, odd_half] using F.cross_correct w x y
    | inr x => cases y with
      | inl y =>
        change F.adjacent w (2*F.legalPoints.code w x+1) (2*(CP.prod Presented.bit).code w y)=true ↔ _
        simpa [AffineBlocks.baseGraph, adjacent, odd_half] using F.cross_correct w y x
      | inr y =>
        change F.adjacent w (2*F.legalPoints.code w x+1) (2*F.legalPoints.code w y+1)=true ↔ False
        simp [adjacent]
  adjacent_poly := by
    unfold adjacent
    apply BoolPoly.iteProp (by word_poly)
    · apply BoolPoly.iteProp (by word_poly) (BoolPoly.const false)
      apply F.cross_poly <;> word_poly
    · apply BoolPoly.iteProp (by word_poly) _ (BoolPoly.const false)
      apply F.cross_poly <;> word_poly

variable [∀ w, Fintype (B w)]

noncomputable def colors : Number F.vertices (fun w x => (D w).colorNat x) where
  eval w i := F.color.eval w (if i%2=0 then 2*(Nat.unpair (i/2)).1 else 2*(Nat.unpair (i/2)).1+1)+1
  correct w x := by
    cases x with
    | inl x =>
      change F.color.eval w (if (F.vertices.code w (.inl x))%2=0 then 2*(Nat.unpair ((F.vertices.code w (.inl x))/2)).1 else 2*(Nat.unpair ((F.vertices.code w (.inl x))/2)).1+1)+1=(D w).colorIndex (.inl x.1)+1
      rw [F.vertices_code_inl]
      simp only [Nat.mul_mod_right, Nat.mul_div_cancel_left _ (by omega : 0<2), Nat.unpair_pair]
      exact congrArg (fun n => n+1) (F.color.correct w (.inl x.1))
    | inr x =>
      change F.color.eval w (if (F.vertices.code w (.inr x))%2=0 then 2*(Nat.unpair ((F.vertices.code w (.inr x))/2)).1 else 2*(Nat.unpair ((F.vertices.code w (.inr x))/2)).1+1)+1=(D w).colorIndex (.inr x.1)+1
      rw [F.vertices_code_inr]
      simp only [show (2*Nat.pair (BP.code w x.1) (F.localData.valueCode w x.1 x.2.val)+1)%2≠0 by omega, ite_false,
        show (2*Nat.pair (BP.code w x.1) (F.localData.valueCode w x.1 x.2.val)+1)/2=Nat.pair (BP.code w x.1) (F.localData.valueCode w x.1 x.2.val) by omega, Nat.unpair_pair]
      exact congrArg (fun n => n+1) (F.color.correct w (.inr x.1))
  poly := NatPoly.succ (F.color.eval_poly (Poly.var 0) (by apply NatPoly.iteProp <;> word_poly))

noncomputable def uncolored := F.base.tagged F.colors

theorem uncolored_isomorphic (w : Word) : Isomorphic (F.uncolored.graph w) ((D w).graph 0) :=
  F.uncolored.graph_isomorphic w

end AffineRealizer
end FinitePresentation

end WLIdentification

end OAI

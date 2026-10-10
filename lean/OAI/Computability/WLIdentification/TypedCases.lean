import OAI.Computability.WLIdentification.RingLegality

namespace OAI

namespace WLIdentification
namespace FinitePresentation
open WordExpressions
variable {A B C D : Word → Type}
namespace Presented
@[simp] theorem prod_code (P : Presented A) (Q : Presented B) (w : Word) (x : A w × B w) :
    (P.prod Q).code w x=Nat.pair (P.code w x.1) (Q.code w x.2) := rfl
@[simp] theorem sum_inl_code (P : Presented A) (Q : Presented B) (w : Word) (x : A w) :
    (P.sum Q).code w (.inl x)=2*P.code w x := rfl
@[simp] theorem sum_inr_code (P : Presented A) (Q : Presented B) (w : Word) (x : B w) :
    (P.sum Q).code w (.inr x)=2*Q.code w x+1 := rfl
@[simp] theorem retype_code (P : Presented A) (e : ∀ w,B w≃A w) (w : Word) (x : B w) :
    (P.retype e).code w x=P.code w (e w x) := rfl
@[simp] theorem fin_code (d : Word → ℕ) (h) (w : Word) (i : Fin (d w)) :
    (Presented.fin d h).code w i=i.val := rfl
@[simp] theorem bool_code (w : Word) (a : Bool) : Presented.bool.code w a=NaturalCode.bool a := rfl
end Presented
namespace Number
variable {P : Presented A} {Q : Presented B} {R : Presented C}

def sumFst {f : ∀ w,A w × C w → ℕ} {g : ∀ w,B w × C w → ℕ}
    (F : Number (P.prod R) f) (G : Number (Q.prod R) g) :
    Number ((P.sum Q).prod R) (fun w x => x.1.elim (fun a => f w (a,x.2)) (fun b => g w (b,x.2))) where
  eval w i := if (Nat.unpair i).1%2=0 then F.eval w (Nat.pair ((Nat.unpair i).1/2) (Nat.unpair i).2)
    else G.eval w (Nat.pair ((Nat.unpair i).1/2) (Nat.unpair i).2)
  correct w x := by
    rcases x with ⟨x,y⟩
    cases x <;> simp only [Presented.prod_code,Presented.sum_inl_code,Presented.sum_inr_code,Nat.unpair_pair]
    · simpa using F.correct w (_,y)
    · simpa [AffineRealizer.odd_half] using G.correct w (_,y)
  poly := NatPoly.iteProp (by word_poly)
    (F.eval_poly (Poly.var 0) (by word_poly)) (G.eval_poly (Poly.var 0) (by word_poly))

def retypeFst {f : ∀ w,A w × C w → ℕ} (F : Number (P.prod R) f) (e : ∀ w,B w ≃ A w) :
    Number ((P.retype e).prod R) (fun w x => f w (e w x.1,x.2)) where
  eval := F.eval
  correct w x := F.correct w (e w x.1,x.2)
  poly := F.poly

end Number
namespace Test
variable {P : Presented A} {Q : Presented B} {R : Presented C}

def sumFst {f : ∀ w,A w × C w → Bool} {g : ∀ w,B w × C w → Bool}
    (F : Test (P.prod R) f) (G : Test (Q.prod R) g) :
    Test ((P.sum Q).prod R) (fun w x => x.1.elim (fun a => f w (a,x.2)) (fun b => g w (b,x.2))) where
  eval w i := if (Nat.unpair i).1%2=0 then F.eval w (Nat.pair ((Nat.unpair i).1/2) (Nat.unpair i).2)
    else G.eval w (Nat.pair ((Nat.unpair i).1/2) (Nat.unpair i).2)
  correct w x := by
    rcases x with ⟨x,y⟩
    cases x <;> simp only [Presented.prod_code,Presented.sum_inl_code,Presented.sum_inr_code,Nat.unpair_pair]
    · simpa using F.correct w (_,y)
    · simpa [AffineRealizer.odd_half] using G.correct w (_,y)
  poly := BoolPoly.iteProp (by word_poly)
    (F.eval_poly (Poly.var 0) (by word_poly)) (G.eval_poly (Poly.var 0) (by word_poly))

def retype {f : ∀ w,A w → Bool} (F : Test P f) (e : ∀ w,B w ≃ A w) :
    Test (P.retype e) (fun w x => f w (e w x)) := F.comp (Map.retype P e)

def retypeFst {f : ∀ w,A w × C w → Bool} (F : Test (P.prod R) f) (e : ∀ w,B w ≃ A w) :
    Test ((P.retype e).prod R) (fun w x => f w (e w x.1,x.2)) where
  eval := F.eval
  correct w x := F.correct w (e w x.1,x.2)
  poly := F.poly

end Test
end FinitePresentation
end WLIdentification

end OAI

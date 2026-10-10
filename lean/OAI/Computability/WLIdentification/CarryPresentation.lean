import OAI.Computability.WLIdentification.ProductPresentation

namespace OAI

namespace WLIdentification
namespace FinitePresentation
open WordExpressions
attribute [local instance] Classical.propDecidable Classical.decEq
namespace Presented
@[simp] theorem option_none_code {A : Word → Type} (P : Presented A) (w : Word) : P.option.code w none=0 := rfl
@[simp] theorem option_some_code {A : Word → Type} (P : Presented A) (w : Word) (a : A w) : P.option.code w (some a)=P.code w a+1 := rfl
end Presented
namespace Number
variable {A B : Word → Type} {AP : Presented A} {BP : Presented B}
def optionFst {f : ∀ w,A w × B w → ℕ} {g : ∀ w,B w → ℕ}
    (F : Number (AP.prod BP) f) (G : Number BP g) :
    Number (AP.option.prod BP) (fun w x => x.1.elim (g w x.2) (fun a => f w (a,x.2))) where
  eval w i := if (Nat.unpair i).1=0 then G.eval w (Nat.unpair i).2 else F.eval w (Nat.pair ((Nat.unpair i).1-1) (Nat.unpair i).2)
  correct w x := by
    rcases x with ⟨x,y⟩
    cases x with
    | none => simpa only [Presented.prod_code,Nat.unpair_pair,Presented.option_none_code,ite_true,Option.elim_none] using G.correct w y
    | some a => simpa only [Presented.prod_code,Nat.unpair_pair,Presented.option_some_code,Nat.add_one_ne_zero,ite_false,Nat.add_sub_cancel,Option.elim_some] using F.correct w (a,y)
  poly := NatPoly.iteProp (by word_poly) (G.eval_poly (Poly.var 0) (by word_poly))
    (F.eval_poly (Poly.var 0) (NatPoly.pair (NatPoly.sub (NatPoly.unpair_fst (NatPoly.var 1)) (NatPoly.const 1)) (NatPoly.unpair_snd (NatPoly.var 1))))
end Number
namespace Test
variable {A B : Word → Type} {AP : Presented A} {BP : Presented B}
def optionFst {f : ∀ w,A w × B w → Bool} {g : ∀ w,B w → Bool}
    (F : Test (AP.prod BP) f) (G : Test BP g) :
    Test (AP.option.prod BP) (fun w x => x.1.elim (g w x.2) (fun a => f w (a,x.2))) where
  eval w i := if (Nat.unpair i).1=0 then G.eval w (Nat.unpair i).2 else F.eval w (Nat.pair ((Nat.unpair i).1-1) (Nat.unpair i).2)
  correct w x := by
    rcases x with ⟨x,y⟩
    cases x with
    | none => simpa only [Presented.prod_code,Nat.unpair_pair,Presented.option_none_code,ite_true,Option.elim_none] using G.correct w y
    | some a => simpa only [Presented.prod_code,Nat.unpair_pair,Presented.option_some_code,Nat.add_one_ne_zero,ite_false,Nat.add_sub_cancel,Option.elim_some] using F.correct w (a,y)
  poly := BoolPoly.iteProp (by word_poly) (G.eval_poly (Poly.var 0) (by word_poly))
    (F.eval_poly (Poly.var 0) (NatPoly.pair (NatPoly.sub (NatPoly.unpair_fst (NatPoly.var 1)) (NatPoly.const 1)) (NatPoly.unpair_snd (NatPoly.var 1))))
end Test
namespace ProductRealizer
variable {A : Word → Type} {AP : Presented A} {d : Word → ℕ}
    {dp : NatPoly (fun X : Fin 1 → Word => d (X 0))} {D : ∀ w,A w → ProductMap (d w)}
noncomputable def optionCases (F : ProductRealizer AP d dp D) (E : ∀ w,ProductMap (d w))
    (dom : Test ((Presented.fin d dp).prod Presented.bool) (fun w x => decide (x.2∈(E w).domain x.1)))
    (map : Map ((Presented.fin d dp).prod Presented.bool) Presented.bool (fun w x => (E w).mapping x.1 x.2)) :
    ProductRealizer AP.option d dp (fun w x => x.elim (E w) (D w)) where
  domain := (Test.optionFst F.domain dom).congr (by intro w x; rcases x with ⟨x,y⟩; cases x <;> rfl)
  mapping := (Number.optionFst F.mapping map).congr (by intro w x; rcases x with ⟨x,y⟩; cases x <;> rfl)

noncomputable def singletonConstant (AP : Presented A) (d : Word → ℕ) (dp : NatPoly (fun X : Fin 1 → Word => d (X 0))) (a b : Bool) :
    ProductRealizer AP d dp (fun _ _ => ProductMap.singleton (fun _ => a) (fun _ => b)) where
  domain := (Test.eq ((Map.snd _ _).comp (Map.snd _ _)) (Map.const _ Presented.bool (fun _ => a) (NatPoly.const (NaturalCode.bool a)))).congr (by intro w x; simp only [ProductMap.singleton,Finset.mem_singleton])
  mapping := (Number.const _ (NaturalCode.bool b)).congr (by intro w x; rfl)

noncomputable def carry (d : Word → ℕ) (dp : NatPoly (fun X : Fin 1 → Word => d (X 0))) :
    ProductRealizer (Presented.fin d dp) d dp (fun _ h => BinaryAddress.carryMap h) where
  domain := {
    eval _ v := if (Nat.unpair (Nat.unpair v).2).1<(Nat.unpair v).1 then decide ((Nat.unpair (Nat.unpair v).2).2=1)
      else if (Nat.unpair (Nat.unpair v).2).1=(Nat.unpair v).1 then decide ((Nat.unpair (Nat.unpair v).2).2=0) else true
    correct w x := by
      simp only [Presented.prod_code,Presented.fin_code,Presented.bool_code,Nat.unpair_pair]
      rcases x with ⟨h,i,b⟩
      change (if i.val<h.val then _ else if i.val=h.val then _ else _)=_
      by_cases hi : i<h
      · simp [hi,show i.val<h.val from hi,BinaryAddress.carryMap,NaturalCode.bool]
      · by_cases he : i=h
        · subst i; simp [BinaryAddress.carryMap,NaturalCode.bool]
        · simp [hi,show ¬i.val<h.val from hi,he,show i.val≠h.val from fun hv => he (Fin.ext hv),BinaryAddress.carryMap]
    poly := BoolPoly.iteProp
      (NatPoly.lt (NatPoly.unpair_fst (NatPoly.unpair_snd (NatPoly.var 1))) (NatPoly.unpair_fst (NatPoly.var 1)))
      (NatPoly.eqtest (NatPoly.unpair_snd (NatPoly.unpair_snd (NatPoly.var 1))) (NatPoly.const 1))
      (BoolPoly.iteProp (NatPoly.eqtest (NatPoly.unpair_fst (NatPoly.unpair_snd (NatPoly.var 1))) (NatPoly.unpair_fst (NatPoly.var 1)))
        (NatPoly.eqtest (NatPoly.unpair_snd (NatPoly.unpair_snd (NatPoly.var 1))) (NatPoly.const 0)) (BoolPoly.const true)) }
  mapping := {
    eval _ v := if (Nat.unpair (Nat.unpair v).2).1≤(Nat.unpair v).1 then 1-(Nat.unpair (Nat.unpair v).2).2 else (Nat.unpair (Nat.unpair v).2).2
    correct w x := by
      simp only [Presented.prod_code,Presented.fin_code,Presented.bool_code,Nat.unpair_pair]
      rcases x with ⟨h,i,b⟩
      change (if i.val≤h.val then _ else _)=NaturalCode.bool (if i≤h then !b else b)
      by_cases hi : i≤h <;> cases b <;> simp [hi,show (i.val≤h.val) = (i≤h) from rfl,NaturalCode.bool]
    poly := NatPoly.iteProp (NatPoly.le (NatPoly.unpair_fst (NatPoly.unpair_snd (NatPoly.var 1))) (NatPoly.unpair_fst (NatPoly.var 1)))
      (NatPoly.sub (NatPoly.const 1) (NatPoly.unpair_snd (NatPoly.unpair_snd (NatPoly.var 1))))
      (NatPoly.unpair_snd (NatPoly.unpair_snd (NatPoly.var 1))) }

noncomputable def congr (F : ProductRealizer AP d dp D) {E : ∀ w,A w → ProductMap (d w)}
    (h : ∀ w a,D w a=E w a) : ProductRealizer AP d dp E where
  domain := F.domain.congr (by intro w x; rw [h w x.1])
  mapping := F.mapping.congr (by intro w x; dsimp only; rw [h w x.1])

noncomputable def cycle (d : Word → ℕ) (dp : NatPoly (fun X : Fin 1 → Word => d (X 0))) :
    ProductRealizer (Presented.fin d dp).option d dp (fun w j => BinaryAddress.cycleMap (d w) j) := by
  let S := singletonConstant Presented.unit d dp true false
  let P := Map.pair (Map.const ((Presented.fin d dp).prod Presented.bool) Presented.unit (fun _ => ()) (NatPoly.const 0)) (Map.id _)
  exact ((carry d dp).optionCases (fun _ => ProductMap.singleton (fun _ => true) (fun _ => false))
    (S.domain.comp P) (S.mapping.comp P)).congr (by intro w x; cases x <;> rfl)

end ProductRealizer
end FinitePresentation
end WLIdentification

end OAI

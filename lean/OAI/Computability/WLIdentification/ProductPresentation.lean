import OAI.Computability.WLIdentification.CircuitForms

namespace OAI

namespace WLIdentification
namespace FinitePresentation
open WordExpressions
attribute [local instance] Classical.propDecidable Classical.decEq

structure ProductRealizer {A : Word → Type} (AP : Presented A) (d : Word → ℕ)
    (dp : NatPoly (fun X : Fin 1 → Word => d (X 0))) (D : ∀ w,A w → ProductMap (d w)) where
  domain : Test (AP.prod ((Presented.fin d dp).prod Presented.bool)) (fun w x => decide (x.2.2∈(D w x.1).domain x.2.1))
  mapping : Map (AP.prod ((Presented.fin d dp).prod Presented.bool)) Presented.bool (fun w x => (D w x.1).mapping x.2.1 x.2.2)

namespace ProductRealizer
variable {A B : Word → Type} {AP : Presented A} {BP : Presented B}
    {d e : Word → ℕ} {dp : NatPoly (fun X : Fin 1 → Word => d (X 0))}
    {ep : NatPoly (fun X : Fin 1 → Word => e (X 0))}
    {D : ∀ w,A w → ProductMap (d w)}

noncomputable def comp (F : ProductRealizer AP d dp D) {f : ∀ w,B w → A w} (G : Map BP AP f) :
    ProductRealizer BP d dp (fun w b => D w (f w b)) where
  domain := F.domain.comp (Map.pair (G.comp (Map.fst _ _)) (Map.snd _ _))
  mapping := F.mapping.comp (Map.pair (G.comp (Map.fst _ _)) (Map.snd _ _))

noncomputable def sumCases (F : ProductRealizer AP d dp D) {E : ∀ w,B w → ProductMap (d w)}
    (G : ProductRealizer BP d dp E) : ProductRealizer (AP.sum BP) d dp (fun w x => x.elim (D w) (E w)) where
  domain := (Test.sumFst F.domain G.domain).congr (by intro w x; rcases x with ⟨x,y⟩; cases x <;> rfl)
  mapping := (Number.sumFst F.mapping G.mapping).congr (by intro w x; rcases x with ⟨x,y⟩; cases x <;> rfl)

noncomputable def identity (AP : Presented A) (d : Word → ℕ) (dp : NatPoly (fun X : Fin 1 → Word => d (X 0))) :
    ProductRealizer AP d dp (fun w _ => ProductMap.identity (d w)) where
  domain := (Test.const _ true).congr (by intro w x; simp [ProductMap.identity])
  mapping := (Map.snd _ _).comp (Map.snd _ _)

noncomputable def concat (F : ProductRealizer AP d dp D) {E : ∀ w,A w → ProductMap (e w)}
    (G : ProductRealizer AP e ep E) : ProductRealizer AP (fun w => d w+e w) (NatPoly.add dp ep)
      (fun w a => (D w a).concat (E w a)) where
  domain := {
    eval w v := if (Nat.unpair (Nat.unpair v).2).1<d w then F.domain.eval w v
      else G.domain.eval w (Nat.pair (Nat.unpair v).1 (Nat.pair ((Nat.unpair (Nat.unpair v).2).1-d w) (Nat.unpair (Nat.unpair v).2).2))
    correct w x := by
      rcases x with ⟨a,i,b⟩
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [Presented.prod_code,Presented.fin_code,Nat.unpair_pair,Fin.val_castAdd,j.isLt,ite_true]
        simpa only [Presented.prod_code,Presented.fin_code,ProductMap.concat,Fin.append_left] using F.domain.correct w (a,j,b)
      · simp only [Presented.prod_code,Presented.fin_code,Nat.unpair_pair,Fin.val_natAdd,show ¬d w+j.val<d w by omega,ite_false,Nat.add_sub_cancel_left]
        simpa only [Presented.prod_code,Presented.fin_code,ProductMap.concat,Fin.append_right] using G.domain.correct w (a,j,b)
    poly := BoolPoly.iteProp (NatPoly.lt (NatPoly.unpair_fst (NatPoly.unpair_snd (NatPoly.var 1))) (dp.rename (fun _ => 0))) F.domain.poly
      (G.domain.eval_poly (Poly.var 0) (NatPoly.pair (NatPoly.unpair_fst (NatPoly.var 1)) (NatPoly.pair
        (NatPoly.sub (NatPoly.unpair_fst (NatPoly.unpair_snd (NatPoly.var 1))) (dp.rename (fun _ => 0)))
        (NatPoly.unpair_snd (NatPoly.unpair_snd (NatPoly.var 1)))))) }
  mapping := {
    eval w v := if (Nat.unpair (Nat.unpair v).2).1<d w then F.mapping.eval w v
      else G.mapping.eval w (Nat.pair (Nat.unpair v).1 (Nat.pair ((Nat.unpair (Nat.unpair v).2).1-d w) (Nat.unpair (Nat.unpair v).2).2))
    correct w x := by
      rcases x with ⟨a,i,b⟩
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [Presented.prod_code,Presented.fin_code,Nat.unpair_pair,Fin.val_castAdd,j.isLt,ite_true]
        simpa only [Presented.prod_code,Presented.fin_code,ProductMap.concat,Fin.append_left] using F.mapping.correct w (a,j,b)
      · simp only [Presented.prod_code,Presented.fin_code,Nat.unpair_pair,Fin.val_natAdd,show ¬d w+j.val<d w by omega,ite_false,Nat.add_sub_cancel_left]
        simpa only [Presented.prod_code,Presented.fin_code,ProductMap.concat,Fin.append_right] using G.mapping.correct w (a,j,b)
    poly := NatPoly.iteProp (NatPoly.lt (NatPoly.unpair_fst (NatPoly.unpair_snd (NatPoly.var 1))) (dp.rename (fun _ => 0))) F.mapping.poly
      (G.mapping.eval_poly (Poly.var 0) (NatPoly.pair (NatPoly.unpair_fst (NatPoly.var 1)) (NatPoly.pair
        (NatPoly.sub (NatPoly.unpair_fst (NatPoly.unpair_snd (NatPoly.var 1))) (dp.rename (fun _ => 0)))
        (NatPoly.unpair_snd (NatPoly.unpair_snd (NatPoly.var 1)))))) }

noncomputable def inverse (F : ProductRealizer AP d dp D) : ProductRealizer AP d dp (fun w a => (D w a).inverse) where
  domain := {
    eval w v := (F.domain.eval w (Nat.pair (Nat.unpair v).1 (Nat.pair (Nat.unpair (Nat.unpair v).2).1 0)) &&
      decide (F.mapping.eval w (Nat.pair (Nat.unpair v).1 (Nat.pair (Nat.unpair (Nat.unpair v).2).1 0))=(Nat.unpair (Nat.unpair v).2).2)) ||
      (F.domain.eval w (Nat.pair (Nat.unpair v).1 (Nat.pair (Nat.unpair (Nat.unpair v).2).1 1)) &&
      decide (F.mapping.eval w (Nat.pair (Nat.unpair v).1 (Nat.pair (Nat.unpair (Nat.unpair v).2).1 1))=(Nat.unpair (Nat.unpair v).2).2))
    correct w x := by
      simp only [Presented.prod_code,Presented.fin_code,Nat.unpair_pair]
      have hdf := F.domain.correct w (x.1,x.2.1,false)
      have hdt := F.domain.correct w (x.1,x.2.1,true)
      have hmf := F.mapping.correct w (x.1,x.2.1,false)
      have hmt := F.mapping.correct w (x.1,x.2.1,true)
      simp only [Presented.prod_code,Presented.fin_code,Presented.bool_code] at hdf hdt hmf hmt
      simp only [show NaturalCode.bool false=0 from rfl,show NaturalCode.bool true=1 from rfl] at hdf hdt hmf hmt
      simp only [Presented.bool_code]
      rw [hdf,hdt,hmf,hmt]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.or_eq_true,Bool.and_eq_true,decide_eq_true_eq,(NaturalCode.bool).injective.eq_iff,
        ProductMap.inverse,Finset.mem_image,Bool.exists_bool]
    poly := by
      have hk (b : ℕ) : NatPoly (fun X : Fin 2 → Word => Nat.pair (Nat.unpair (X 1).length).1 (Nat.pair (Nat.unpair (Nat.unpair (X 1).length).2).1 b)) :=
        NatPoly.pair (NatPoly.unpair_fst (NatPoly.var 1)) (NatPoly.pair (NatPoly.unpair_fst (NatPoly.unpair_snd (NatPoly.var 1))) (NatPoly.const b))
      exact BoolPoly.or (BoolPoly.and (F.domain.eval_poly (Poly.var 0) (hk 0))
        (NatPoly.eqtest (F.mapping.eval_poly (Poly.var 0) (hk 0)) (NatPoly.unpair_snd (NatPoly.unpair_snd (NatPoly.var 1)))))
        (BoolPoly.and (F.domain.eval_poly (Poly.var 0) (hk 1))
        (NatPoly.eqtest (F.mapping.eval_poly (Poly.var 0) (hk 1)) (NatPoly.unpair_snd (NatPoly.unpair_snd (NatPoly.var 1))))) }
  mapping := {
    eval w v := if (F.domain.eval w (Nat.pair (Nat.unpair v).1 (Nat.pair (Nat.unpair (Nat.unpair v).2).1 0)) &&
      decide (F.mapping.eval w (Nat.pair (Nat.unpair v).1 (Nat.pair (Nat.unpair (Nat.unpair v).2).1 0))=(Nat.unpair (Nat.unpair v).2).2)) then 0 else 1
    correct w x := by
      simp only [Presented.prod_code,Presented.fin_code,Nat.unpair_pair]
      have hdf := F.domain.correct w (x.1,x.2.1,false)
      have hmf := F.mapping.correct w (x.1,x.2.1,false)
      simp only [Presented.prod_code,Presented.fin_code,Presented.bool_code] at hdf hmf
      simp only [show NaturalCode.bool false=0 from rfl] at hdf hmf
      simp only [Presented.bool_code]
      rw [hdf,hmf]
      simp only [Bool.and_eq_true,decide_eq_true_eq,(NaturalCode.bool).injective.eq_iff]
      change (if _ then 0 else 1)=NaturalCode.bool (if _ then false else true)
      split <;> rfl
    poly := NatPoly.ite (BoolPoly.and
      (F.domain.eval_poly (Poly.var 0) (NatPoly.pair (NatPoly.unpair_fst (NatPoly.var 1)) (NatPoly.pair (NatPoly.unpair_fst (NatPoly.unpair_snd (NatPoly.var 1))) (NatPoly.const 0))))
      (NatPoly.eqtest (F.mapping.eval_poly (Poly.var 0) (NatPoly.pair (NatPoly.unpair_fst (NatPoly.var 1)) (NatPoly.pair (NatPoly.unpair_fst (NatPoly.unpair_snd (NatPoly.var 1))) (NatPoly.const 0))))
        (NatPoly.unpair_snd (NatPoly.unpair_snd (NatPoly.var 1))))) (NatPoly.const 0) (NatPoly.const 1) }

end ProductRealizer
end FinitePresentation
end WLIdentification

end OAI

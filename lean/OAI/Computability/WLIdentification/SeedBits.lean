import OAI.Computability.WLIdentification.CellularPresentation

namespace OAI

namespace WLIdentification
namespace BinaryAddress
 theorem ofNat_apply (d n : ℕ) (i : Fin d) : ofNat d n i=decide (n/2^i.val%2=1) := by
  induction d generalizing n with
  | zero => exact Fin.elim0 i
  | succ d ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [ofNat,Fin.cons_zero,Fin.val_zero,pow_zero,Nat.div_one]
    · simp only [ofNat,Fin.cons_succ,Fin.val_succ,ih,pow_succ,Nat.div_div_eq_div_mul,Nat.mul_comm]
end BinaryAddress
namespace FinitePresentation
open WordExpressions
attribute [local instance] Classical.propDecidable Classical.decEq
namespace Test
variable {A : Word → Type} {AP : Presented A}
def ofNatBit {n : ∀ w,A w → ℕ} (N : Number AP n) (d : Word → ℕ)
    (dp : NatPoly (fun X : Fin 1 → Word => d (X 0))) :
    Test (AP.prod (Presented.fin d dp)) (fun w x => BinaryAddress.ofNat (d w) (n w x.1) x.2) where
  eval w v := decide (NumericKernel.digit 2 (N.eval w (Nat.unpair v).1) (Nat.unpair v).2=1)
  correct w x := by
    simp only [Presented.prod_code,Presented.fin_code,Nat.unpair_pair,N.correct,BinaryAddress.ofNat_apply,NumericKernel.digit]
  poly := NatPoly.eqtest (NatPoly.digit (NatPoly.const 2)
    (N.eval_poly (Poly.var 0) (NatPoly.unpair_fst (NatPoly.var 1))) (NatPoly.unpair_snd (NatPoly.var 1))) (NatPoly.const 1)
end Test
namespace ProductRealizer
variable {A : Word → Type} {AP : Presented A} {d : Word → ℕ}
    {dp : NatPoly (fun X : Fin 1 → Word => d (X 0))}
noncomputable def singletonBits {bits : ∀ w,A w → BinaryAddress.Bits (d w)}
    (B : Map (AP.prod (Presented.fin d dp)) Presented.bool (fun w x => bits w x.1 x.2)) :
    ProductRealizer AP d dp (fun w a => ProductMap.singleton (bits w a) (bits w a)) := by
  let I := Map.pair (Map.fst AP ((Presented.fin d dp).prod Presented.bool)) ((Map.fst _ _).comp (Map.snd _ _))
  exact {
    domain := (Test.eq ((Map.snd _ _).comp (Map.snd _ _)) (B.comp I)).congr (by intro w x; simp only [ProductMap.singleton,Finset.mem_singleton])
    mapping := B.comp I }

noncomputable def aboveBits {bits : ∀ w,BinaryAddress.Bits (d w)}
    (B : Map (Presented.fin d dp) Presented.bool (fun w i => bits w i)) :
    ProductRealizer (Presented.fin d dp) d dp (fun w h => BinaryAddress.aboveMap (bits w) h) := by
  let H := Number.code (Presented.fin d dp) |>.comp (Map.fst (Presented.fin d dp) ((Presented.fin d dp).prod Presented.bool))
  let I := (Number.code (Presented.fin d dp)).comp ((Map.fst _ _).comp (Map.snd (Presented.fin d dp) ((Presented.fin d dp).prod Presented.bool)))
  let V := (Map.snd _ _).comp (Map.snd (Presented.fin d dp) ((Presented.fin d dp).prod Presented.bool))
  let BI := B.comp ((Map.fst _ _).comp (Map.snd (Presented.fin d dp) ((Presented.fin d dp).prod Presented.bool)))
  exact {
    domain := (Test.ite (Test.numLt H I) (Test.eq V BI)
      (Test.ite (Test.numEq I H) (Test.ofBoolMap V) (Test.const _ true))).congr (by
        intro w x
        change (if decide (x.1.val<x.2.1.val) then decide (x.2.2=bits w x.2.1) else if decide (x.2.1.val=x.1.val) then x.2.2 else true)=_
        by_cases hi : x.1<x.2.1
        · simp [hi,show x.1.val<x.2.1.val from hi,BinaryAddress.aboveMap]
        · by_cases he : x.2.1=x.1
          · simp [he,BinaryAddress.aboveMap]
          · simp [hi,show ¬x.1.val<x.2.1.val from hi,he,show x.2.1.val≠x.1.val from fun h => he (Fin.ext h),BinaryAddress.aboveMap])
    mapping := V }
end ProductRealizer
namespace InitialRealizer
open Machine BinaryAddress
variable (d : Word → ℕ) (dp : NatPoly (fun X : Fin 1 → Word => d (X 0)))
 theorem span_poly : NatPoly (fun X : Fin 1 → Word => inputSpan (X 0)) := NatPoly.max (NatPoly.const 1) (NatPoly.var 0)
abbrev positionP := Presented.fin (fun w => inputSpan w) span_poly
abbrev digitP := Presented.fin d dp
noncomputable def spanBit : Map (digitP d dp) Presented.bool (fun w i => ofNat (d w) (inputSpan w) i) :=
  (Map.boolOfTest ((Test.ofNatBit (Number.param Presented.unit (fun w => inputSpan w) span_poly) d dp).comp
    (Map.pair (Map.const _ Presented.unit (fun _ => ()) (NatPoly.const 0)) (Map.id _)))).congr (by intro w x; rfl)
noncomputable def zeroBit : Test (digitP d dp) (fun w i => decide (ofNat (d w) (inputSpan w) i=false)) :=
  Test.eq (spanBit d dp) (Map.const _ Presented.bool (fun _ => false) (NatPoly.const 0))
noncomputable abbrev thresholdDigitP := (digitP d dp).restrict
  (fun w i => ofNat (d w) (inputSpan w) i=false) (zeroBit d dp)
noncomputable abbrev thresholdP := (thresholdDigitP d dp).option
noncomputable abbrev seedP := positionP.sum (thresholdP d dp)
noncomputable def positionBits : Map (positionP.prod (digitP d dp)) Presented.bool
    (fun w x => ofNat (d w) x.1.val x.2) := Map.boolOfTest (Test.ofNatBit (Number.code positionP) d dp)
noncomputable def thresholdMap : ProductRealizer (thresholdP d dp) d dp
    (fun w h => BinaryAddress.thresholdMap (ofNat (d w) (inputSpan w)) h) := by
  let S := ProductRealizer.singletonBits (AP := Presented.unit) (d := d) (dp := dp) (bits := fun w _ => ofNat (d w) (inputSpan w)) ((spanBit d dp).comp (Map.snd Presented.unit (digitP d dp)))
  let B := (ProductRealizer.aboveBits (spanBit d dp)).comp
    (Map.coe (digitP d dp) (fun w i => ofNat (d w) (inputSpan w) i=false) (zeroBit d dp))
  let U := Map.pair (Map.const ((digitP d dp).prod Presented.bool) Presented.unit (fun _ => ()) (NatPoly.const 0)) (Map.id _)
  exact (B.optionCases (fun w => ProductMap.singleton (ofNat (d w) (inputSpan w)) (ofNat (d w) (inputSpan w)))
    (S.domain.comp U) (S.mapping.comp U)).congr (by intro w x; cases x <;> rfl)
noncomputable def seedMap : ProductRealizer (seedP d dp) d dp (fun w => Machine.initialSeedMap (d w) w) :=
  ((ProductRealizer.singletonBits (positionBits d dp)).sumCases (thresholdMap d dp)).congr (by intro w x; cases x <;> rfl)
end InitialRealizer
end FinitePresentation

end WLIdentification

end OAI

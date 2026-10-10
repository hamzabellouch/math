import OAI.NumberTheory.DirichletL.Detector.SixthArray

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve HeckeInverseAmplification ProbeCompleted
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

abbrev SixthInnerIndex := HeckeInverseAmplification.NonzeroIdeal×((Id×Id)×Id)

def sixthRawEquiv : FreeRow×SixthInnerIndex ≃ RawHighIndex :=
  (Equiv.prodAssoc _ _ _).symm.trans
    (Equiv.prodCongr sixthFrequencyEquiv (Equiv.refl _))

def nonzeroLastEquiv : SixthInnerIndex ≃ {p : (Id×Id)×(Id×Id) // p.2.2≠0} where
  toFun p := ⟨(p.2.1,(p.2.2,p.1.val)),p.1.property⟩
  invFun p := (⟨p.val.2.2,p.property⟩,(p.val.1,p.val.2.1))
  left_inv _ := rfl
  right_inv _ := rfl

lemma markedIdealHighSummand_last_zero (S : Finset Id) (D : Id) (η : HeckeFamily.Character)
    (u : O) (x w z : ℂ) (I J K : Id) :
    markedIdealHighSummand S D η u x w z I J K 0=0 := by
  have hz : ¬(Squarefree I ∧ Supported I ∧ Supported J ∧ Supported K ∧ Supported (0:Id)) :=
    fun h=>h.2.2.2.2.1 rfl
  simp only [markedIdealHighSummand,bareIdealHighSummand,bareIdealHighCoefficient,
    dite_eq_right hz,zero_mul,mul_zero]

lemma markedIdealHighSeries_eq_sixth_inner (S : Finset Id) (D : Id) (η : HeckeFamily.Character)
    (u : O) (x w z : ℂ) :
    markedIdealHighSeries S D η u x w z=
      ∑'p : SixthInnerIndex,markedIdealHighSummand S D η u x w z p.2.1.1 p.2.1.2 p.2.2 p.1.val := by
  have he := nonzeroLastEquiv.tsum_eq (fun p=>
    markedIdealHighSummand S D η u x w z p.val.1.1 p.val.1.2 p.val.2.1 p.val.2.2)
  change (∑'p : SixthInnerIndex,markedIdealHighSummand S D η u x w z p.2.1.1 p.2.1.2 p.2.2 p.1.val)=_ at he
  rw [he]
  unfold markedIdealHighSeries
  symm
  apply tsum_subtype_eq_of_support_subset
    (f:=fun p : (Id×Id)×(Id×Id)=>markedIdealHighSummand S D η u x w z p.1.1 p.1.2 p.2.1 p.2.2)
    (s:={p : (Id×Id)×(Id×Id) | p.2.2≠0})
  intro p hp hz
  apply hp
  change markedIdealHighSummand S D η u x w z p.1.1 p.1.2 p.2.1 p.2.2=0
  rw [hz,markedIdealHighSummand_last_zero]

theorem rawArithmeticSeries_eq_sixth_high (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (hprime : ∀P∈S,Prime P) (hbad : fixedBadPrimes⊆S)
    (D : Id) (η : HeckeFamily.Character) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1<z.re) :
    rawArithmeticSeries S D η (calibrationForSet S hS) x w z=
      ∑'u : FreeRow,star ((calibrationForSet S hS).residueMonoid u.val)*
        frequencyWeight z ⟨u.val,u.property.1⟩*markedIdealHighSeries S D η u.val x w z := by
  let mask : NonzeroFrequency→ℂ := fun H=>star ((calibrationForSet S hS).residueMonoid H.val)
  have hm (H : NonzeroFrequency) : ‖mask H‖≤1 := by
    simpa only [mask,norm_star] using (calibrationForSet S hS).residueMonoid_norm_le_one H.val
  have hs := (fullHighSummand_summable S D η x w z hx hw hz mask hm).comp_injective
    rawHighEmbedding_injective
  have ht : Summable (fun p : FreeRow×SixthInnerIndex=>
      fullHighCoefficient S D η (fun H=>star ((calibrationForSet S hS).residueMonoid H.val)) x w z
        (rawHighEmbedding (sixthRawEquiv p))) := hs.comp_injective sixthRawEquiv.injective
  unfold rawArithmeticSeries
  rw [←sixthRawEquiv.tsum_eq]
  rw [ht.tsum_prod]
  apply tsum_congr
  intro u
  rw [markedIdealHighSeries_eq_sixth_inner,←tsum_mul_left]
  apply tsum_congr
  intro p
  exact rawHighCoefficient_sixth S hS hprime hbad D η x w z (u,p.1) p.2.1.1 p.2.1.2 p.2.2

end SevenEighths.ProbePhysical
end

end OAI

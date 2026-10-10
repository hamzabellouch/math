import OAI.NumberTheory.DirichletL.Detector.SixthMask
import OAI.NumberTheory.DirichletL.Detector.RawArithmetic

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve ProbeCompleted
open HeckeInverseAmplification ConcretePrimeRowBridge CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

lemma bareIdealHighCoefficient_sixth (η : HeckeFamily.Character)
    (p : FreeRow×HeckeInverseAmplification.NonzeroIdeal) (hL : Supported p.2.val)
    (I J K : Ideal O) :
    bareIdealHighCoefficient η (sixthFrequencyEquiv p).val I J K 1=
      bareIdealHighCoefficient η p.1.val I J K p.2.val := by
  rw [sixthFrequencyEquiv_primary p hL]
  unfold bareIdealHighCoefficient
  by_cases h : Squarefree I ∧ Supported I ∧ Supported J ∧ Supported K
  · simp only [h.1,h.2.1,h.2.2.1,h.2.2.2,hL,supported_one_ideal,and_self,dite_eq_left]
    congr 1
    simp only [primaryGenerator_one,one_pow,mul_one]
  · have h1 : ¬(Squarefree I ∧ Supported I ∧ Supported J ∧ Supported K ∧ Supported (1:Ideal O)) :=
      fun hh=>h ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1⟩
    have h2 : ¬(Squarefree I ∧ Supported I ∧ Supported J ∧ Supported K ∧ Supported p.2.val) :=
      fun hh=>h ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1⟩
    rw [dite_eq_right h1,dite_eq_right h2]

lemma rawHighCoefficient_sixth (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal)
    (hprime : ∀P∈S,Prime P) (hbad : fixedBadPrimes⊆S)
    (D : Ideal O) (η : HeckeFamily.Character) (x w z : ℂ)
    (p : FreeRow×HeckeInverseAmplification.NonzeroIdeal) (I J K : Ideal O) :
    fullHighCoefficient S D η
      (fun H=>star ((calibrationForSet S hS).residueMonoid H.val)) x w z
      (rawHighEmbedding (sixthFrequencyEquiv p,((I,J),K)))=
    star ((calibrationForSet S hS).residueMonoid p.1.val)*
      frequencyWeight z ⟨p.1.val,p.1.property.1⟩*
      markedIdealHighSummand S D η p.1.val x w z I J K p.2.val := by
  have hOne : ∀P∈S,¬P∣(1:Ideal O) := fun P hP=> (hprime P hP).not_dvd_one
  change star ((calibrationForSet S hS).residueMonoid (sixthFrequencyEquiv p).val)*
    frequencyWeight z (sixthFrequencyEquiv p)*
      markedIdealHighSummand S D η (sixthFrequencyEquiv p).val x w z I J K 1=_
  rw [sixthFrequencyWeight]
  rw [sixthFrequencyEquiv_apply,calibration_sixth_frequency_mask]
  by_cases hL : ∀P∈S,¬P∣p.2.val
  · have hs := supported_of_source_exclusions S hbad p.2.val p.2.property hL
    have hb := bareIdealHighCoefficient_sixth η p hs I J K
    rw [sixthFrequencyEquiv_apply] at hb
    simp only [ite_eq_left hL,mul_one,markedIdealHighSummand,highIdealMask,ite_eq_left hOne,
      bareIdealHighSummand,hb]
    have hw1 : fullIdealWeight (6*z) (1:Ideal O)=1 := (IdealEuler.normWeight (6*z)).map_one
    rw [hw1]
    ring
  · simp only [ite_eq_right hL,mul_zero,zero_mul,markedIdealHighSummand,highIdealMask]

end SevenEighths.ProbePhysical
end

end OAI

import OAI.NumberTheory.DirichletL.Detector.LowPrimeFamily
import OAI.NumberTheory.DirichletL.Hecke.RowClosure

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

lemma lowCalibrationGood_dvd (C : CalibrationData)
    (D : GoodMaskRowData C.generator 1 C.generator) : D.numeratorGood∣C.generator := by
  refine ⟨D.numeratorUnit.val*λ₀^D.numeratorLambda*(2:O)^D.numeratorTwo,?_⟩
  have hh := D.numeratorFactor
  simp only [one_pow,one_mul] at hh
  change C.generator=D.numeratorUnit.val*λ₀^D.numeratorLambda*(2:O)^D.numeratorTwo*D.numeratorGood at hh
  exact hh.trans (by ring)

theorem lowBaseModulus_coprime (η : HeckeFamily.Character) (C : CalibrationData)
    (D : GoodMaskRowData C.generator 1 C.generator)
    (hLam : λ₀∣C.generator) (h2 : (2:O)∣C.generator)
    (n : O) (hcn : IsCoprime C.generator n) (hη : HeckeFamily.elementCoeff η n≠0) :
    IsCoprime (Ideal.span {n}) (lowBaseModulus η C C.generator D*Ideal.span {(72:O)}) := by
  have heta : IsCoprime (Ideal.span {n}) η.modulus :=
    (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp (MulChar.apply_ne_zero_iff.mp hη)
  have hcal : IsCoprime (Ideal.span {n}) (Ideal.span {C.generator}) :=
    (Ideal.isCoprime_span_singleton_iff _ _).mpr hcn.symm
  have hgood : IsCoprime (Ideal.span {n}) (Ideal.span {D.numeratorGood}) :=
    (Ideal.isCoprime_span_singleton_iff _ _).mpr
      (hcn.of_isCoprime_of_dvd_left (lowCalibrationGood_dvd C D)).symm
  have htwo : IsCoprime n (2:O) := (hcn.of_isCoprime_of_dvd_left h2).symm
  have hs := supported_of_coprime_bad C.generator n hLam h2 hcn
  have hnine := (ShortDraftCRT.nine_coprime_of_not_lambda_dvd n ((supported_span_iff n).mp hs).1).symm
  have hseventy : IsCoprime n (72:O) := by
    convert (htwo.pow_right : IsCoprime n ((2:O)^3)).mul_right hnine using 1 ;norm_num
  have h72 : IsCoprime (Ideal.span {n}) (Ideal.span {(72:O)}) :=
    (Ideal.isCoprime_span_singleton_iff _ _).mpr hseventy
  have h4 : IsCoprime (Ideal.span {n}) (Ideal.span {(4:O)}) := by
    apply (Ideal.isCoprime_span_singleton_iff _ _).mpr
    convert htwo.pow_right (n:=2) using 1 ;norm_num
  unfold lowBaseModulus calibrationRowModulus
  exact (heta.mul_right (hcal.mul_right
    (((isCoprime_one_right).mul_right hcal).mul_right h72 |>.mul_right hgood))).mul_right h4 |>.mul_right h72

theorem lowSingleSlotWeight_zero_of_period (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (W : ℝ→ℂ) (P t : ℝ) (n : O) (hcn : IsCoprime (calibrationForSet S hS).generator n)
    (hperiod : ¬IsCoprime (Ideal.span {n})
      (lowBaseModulus η (calibrationForSet S hS) (calibrationForSet S hS).generator
        (calibrationLowData S hS)*Ideal.span {(72:O)})) :
    lowSingleSlotWeight η W P t n=0 := by
  have heta : HeckeFamily.elementCoeff η n=0 := by
    by_contra hh
    exact hperiod (lowBaseModulus_coprime η _ _ (calibration_generator_bad S hS hbad).1
      (calibration_generator_bad S hS hbad).2 n hcn hh)
  simp [lowSingleSlotWeight,heta]

end SevenEighths.ProbePhysical
end

end OAI

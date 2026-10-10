import OAI.NumberTheory.DirichletL.Detector.LowGramProfile
import OAI.NumberTheory.DirichletL.Detector.LowPeriod

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ConcreteTraceCRT ProbeRow CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
open RayFourExpansion InitialMeanSquare SecondPassArithmetic CanonicalCoefficientClass
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

def gramPeriodicMonoid (C : CalibrationData) (B : O) (D : GoodMaskRowData B 1 C.generator) : O→*ℂ :=
  conjugateMonoid C.residueMonoid*actualPeriodicRow 1 B D.numeratorUnit D.numeratorLambda D.numeratorTwo
    D.numeratorGood D.numeratorSupported

lemma gramPeriodicMonoid_norm (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (n : O) : ‖gramPeriodicMonoid C B D n‖≤1 := by
  rw [gramPeriodicMonoid,MonoidHom.mul_apply,norm_mul]
  change ‖star (C.residueMonoid n)‖*_≤1
  rw [norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) (C.residueMonoid_norm_le_one n)).trans (actualPeriodicRow_norm 1 (fun _=>by simp) B D.numeratorUnit D.numeratorLambda D.numeratorTwo
      D.numeratorGood D.numeratorSupported n)

lemma gramPeriodicMonoid_periodic (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) :
    FactorsModulo (Ideal.span {C.generator}*calibrationRowModulus C B D) (gramPeriodicMonoid C B D) := by
  have hp := actualPeriodicRow_periodic (1:O→*ℂ) 1 (fun _ _ _=>rfl)
    B D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood D.numeratorSupported
  intro x y hxy
  change star (C.residueMonoid x)*_=star (C.residueMonoid y)*_
  congr 1
  · apply congrArg star
    apply congrArg C.residue
    exact Ideal.Quotient.eq.mpr (Ideal.mul_le_left hxy)
  · exact hp x y (Ideal.mul_le_right hxy)

lemma gramPeriodicMonoid_zero (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (n : O) (hn : ¬IsCoprime B n) :
    gramPeriodicMonoid C B D n=0 := by
  have hm : coprimalityMask B n=(0:ℂ) := by change (if IsCoprime B n then (1:ℂ) else 0)=0;rw [ite_eq_right hn]
  change star (C.residueMonoid n)*
    ((((1:O→*ℂ) n*coprimalityMask B n)*
      numeratorBadTwist D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood D.numeratorSupported n)*
      movingNumeratorRow D.numeratorGood D.numeratorSupported n)=0
  rw [hm]
  simp

lemma gramPeriodicMonoid_primary (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (hBL : λ₀∣B) (hB2 : (2:O)∣B)
    (n : O) (hn : Supported (Ideal.span {n})) (hpn : λ₀^2∣n-1) (hc : IsCoprime B n) :
    gramPeriodicMonoid C B D n=(C.residueMonoid n)⁻¹*idealRowHom C.generator (Ideal.span {n}) := by
  have he := rowTwist_eq_actualPeriodicRow_primary (1:O→*ℂ) B 1 C.generator hBL hB2
    D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood D.numeratorSupported
    D.numeratorPrimary D.numeratorFactor n hpn
  rw [rowTwist_extract_sixth_mask _ _ _ _ _ hn] at he
  have hm : coprimalityMask B n=(1:ℂ) := by change (if IsCoprime B n then (1:ℂ) else 0)=1;rw [ite_eq_left hc]
  simp only [MonoidHom.one_apply,hm,one_mul,one_pow] at he
  change star (C.residueMonoid n)*_=_
  rw [←he]
  congr 1
  let := finite_quotient_span C.generator_ne_zero
  let : Fintype (O⧸Ideal.span {C.generator}) := Fintype.ofFinite _
  change star (C.residue (Ideal.Quotient.mk _ n))=(C.residue (Ideal.Quotient.mk _ n))⁻¹
  rw [MulChar.star_apply',MulChar.inv_apply_eq_inv']

theorem lowArithmeticCoefficient_periodic (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (s : {I : Id // Supported I}) :
    lowArithmeticCoefficient (calibrationForSet S hS) s=
      (calibrationForSet S hS).tau⁻¹*
        gramPeriodicMonoid (calibrationForSet S hS) (calibrationForSet S hS).generator
          (calibrationLowData S hS) (primaryGenerator s.val) := by
  let C := calibrationForSet S hS
  have hn := supported_primaryGenerator_ne_zero s.val s.property
  have he := (primaryGenerator_spec s.val hn).1
  have hp := (primaryGenerator_spec s.val hn).2
  have hsupp := (supported_span_primaryGenerator_iff s.val).mpr s.property
  have hb := calibration_generator_bad S hS hbad
  by_cases hc : IsCoprime C.generator (primaryGenerator s.val)
  · have hguard : ∀P∈C.excluded,¬P∣s.val := by
      rw [show C.excluded=S from calibrationForSet_excluded S hS,←he]
      exact (calibration_coprime_iff_excluded_span S hS _).mp hc
    rw [lowArithmeticCoefficient,ite_eq_left hguard,
      gramPeriodicMonoid_primary C C.generator (calibrationLowData S hS) hb.1 hb.2 _ hsupp hp hc,he]
    ring
  · have hguard : ¬∀P∈C.excluded,¬P∣s.val := by
      rw [show C.excluded=S from calibrationForSet_excluded S hS,←he]
      exact fun h=>hc ((calibration_coprime_iff_excluded_span S hS _).mpr h)
    rw [lowArithmeticCoefficient,ite_eq_right hguard,gramPeriodicMonoid_zero C C.generator (calibrationLowData S hS) _ hc,mul_zero]

end SevenEighths.ProbePhysical
end

end OAI

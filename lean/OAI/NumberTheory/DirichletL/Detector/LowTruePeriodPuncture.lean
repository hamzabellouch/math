import OAI.NumberTheory.DirichletL.Detector.LowPeriodFilter
import OAI.NumberTheory.DirichletL.Reflection.PunctureAbsorption

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss RayFourExpansion SecondPassArithmetic
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma physicalRayPeriodicBase_support (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S) (σ : RayRing) (χ : RayCharacter)
    (n : O) (hn : physicalRayPeriodicBase η S hS σ χ n≠0) :
    IsCoprime (Ideal.span {n}) (lowPeriodIdeal η S hS) := by
  let C := calibrationForSet S hS
  let D := calibrationLowData S hS
  change ((rayMonoid χ n*HeckeFamily.elementCoeff η n)*
    star (C.residueMonoid n*CanonicalRowCompletion.actualPeriodicRow 1 C.generator
      D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood D.numeratorSupported n))*
      _≠0 at hn
  have ha := left_ne_zero_of_mul hn
  have heta := right_ne_zero_of_mul (left_ne_zero_of_mul ha)
  have hres := left_ne_zero_of_mul (star_ne_zero.mp (right_ne_zero_of_mul ha))
  have hc : IsCoprime C.generator n := by
    apply (Ideal.isCoprime_span_singleton_iff _ _).mp
    exact ((IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp
      (C.residue.apply_ne_zero_iff.mp hres)).symm
  exact lowBaseModulus_coprime η C D (calibration_generator_bad S hS hbad).1
    (calibration_generator_bad S hS hbad).2 n hc heta

def lowTruePeriodGenerator (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) : O := ConcretePrimeRowBridge.idealGenerator (lowPeriodIdeal η S hS)

lemma lowPeriodIdeal_ne_zero (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) : lowPeriodIdeal η S hS≠0 := by
  unfold lowPeriodIdeal
  apply mul_ne_zero
  · exact lowBaseModulus_ne_zero η _ _ (calibrationForSet S hS).generator_ne_zero _
  · apply Ideal.span_singleton_eq_bot.not.mpr
    norm_num

lemma lowTruePeriodGenerator_ne_zero (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) : lowTruePeriodGenerator η S hS≠0 :=
  ConcretePrimeRowBridge.idealGenerator_ne_zero _ (lowPeriodIdeal_ne_zero η S hS)

lemma lowTruePeriodGenerator_span (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) : Ideal.span {lowTruePeriodGenerator η S hS}=lowPeriodIdeal η S hS :=
  ConcretePrimeRowBridge.span_idealGenerator _

lemma physicalRayPeriodicBase_zero_true_puncture (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S) (σ : RayRing) (χ : RayCharacter)
    (n : O) (hn : ¬IsCoprime (lowTruePeriodGenerator η S hS) n) :
    physicalRayPeriodicBase η S hS σ χ n=0 := by
  by_contra hh
  apply hn
  apply (Ideal.isCoprime_span_singleton_iff _ _).mp
  rw [lowTruePeriodGenerator_span]
  exact (physicalRayPeriodicBase_support η S hS hbad σ χ n hh).symm

theorem physical_row_absorb_true_period (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S) (σ : RayRing) (χ : RayCharacter)
    (f z : O) :
    rowTwist (physicalRayPeriodicBase η S hS σ χ)
      ((calibrationForSet S hS).generator*lowTruePeriodGenerator η S hS) f z=
    rowTwist (physicalRayPeriodicBase η S hS σ χ) (calibrationForSet S hS).generator f z := by
  exact InverseReflectedPhase.rowTwist_absorb_puncture _ _ _ f z
    (calibration_generator_bad S hS hbad).1 (calibration_generator_bad S hS hbad).2
    (physicalRayPeriodicBase_zero_true_puncture η S hS hbad σ χ)

lemma physical_true_period_residual_coprime (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (I F : Id) :
    IsCoprime (lowPeriodIdeal η S hS)
      (rowResidualPart I
        (Ideal.span {(calibrationForSet S hS).generator*lowTruePeriodGenerator η S hS}*F)) := by
  apply InverseReflectedPhase.rowResidualPart_coprime_enlarged_period
  rw [lowTruePeriodGenerator_span]

def lowReflectionPeriod (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) : Id :=
  lowBaseModulus η (calibrationForSet S hS) (calibrationForSet S hS).generator (calibrationLowData S hS)

lemma lowReflectionPeriod_ne_zero (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) : lowReflectionPeriod η S hS≠0 :=
  lowBaseModulus_ne_zero η _ _ (calibrationForSet S hS).generator_ne_zero _

lemma lowReflectionPeriod_actual (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (σ : RayRing) (χ : RayCharacter) :
    CanonicalCoefficientClass.FactorsModulo (lowReflectionPeriod η S hS) (physicalRayPeriodicBase η S hS σ χ) ∧
      ∀n : O,‖physicalRayPeriodicBase η S hS σ χ n‖≤1 := by
  exact ⟨lowPeriodicBase_periodic η _ _ _ _ _ χ,lowPeriodicBase_norm η _ _ _ _ _ χ⟩

def lowReflectionMask (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) : O :=
  (calibrationForSet S hS).generator*lowTruePeriodGenerator η S hS

lemma lowReflectionMask_ne_zero (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) : lowReflectionMask η S hS≠0 :=
  mul_ne_zero (calibrationForSet S hS).generator_ne_zero (lowTruePeriodGenerator_ne_zero η S hS)

lemma lowReflectionMask_bad (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S) :
    ConcretePrimeRowBridge.goodLambda∣lowReflectionMask η S hS ∧ (2:O)∣lowReflectionMask η S hS := by
  exact ⟨dvd_mul_of_dvd_left (calibration_generator_bad S hS hbad).1 _,
    dvd_mul_of_dvd_left (calibration_generator_bad S hS hbad).2 _⟩

lemma lowReflectionMask_period (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) : lowPeriodIdeal η S hS∣Ideal.span {lowReflectionMask η S hS} := by
  rw [lowReflectionMask,←Ideal.span_singleton_mul_span_singleton,lowTruePeriodGenerator_span]
  exact dvd_mul_left _ _

lemma physical_markedCompletedT_absorb_true_period (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S) (σ : RayRing) (χ : RayCharacter)
    (f z : O) (W : ℝ→ℂ) (X : ℝ) (mark : Id→ℂ) :
    InverseMoment.markedCompletedT
      (rowTwist (physicalRayPeriodicBase η S hS σ χ) (lowReflectionMask η S hS) f z) W X mark=
    InverseMoment.markedCompletedT
      (rowTwist (physicalRayPeriodicBase η S hS σ χ) (calibrationForSet S hS).generator f z) W X mark := by
  rw [lowReflectionMask,physical_row_absorb_true_period η S hS hbad σ χ]

end SevenEighths.ProbePhysical
end

end OAI

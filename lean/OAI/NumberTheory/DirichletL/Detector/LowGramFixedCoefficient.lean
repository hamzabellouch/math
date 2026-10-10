import OAI.NumberTheory.DirichletL.Detector.LowGramArithmetic

namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def gramFixedModulus (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) : Id :=
  (Ideal.span {(calibrationForSet S hS).generator}*
    calibrationRowModulus (calibrationForSet S hS) (calibrationForSet S hS).generator (calibrationLowData S hS))*
      Ideal.span {(4:O)}

lemma gramFixedModulus_nonzero (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) : gramFixedModulus S hS≠0 := by
  unfold gramFixedModulus
  apply mul_ne_zero
  · exact mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr (calibrationForSet S hS).generator_ne_zero)
      (calibrationRowModulus_ne_zero _ _ (calibrationForSet S hS).generator_ne_zero _)
  · exact Ideal.span_singleton_eq_bot.not.mpr (by norm_num)

def gramCoefficientExtension (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing) (n : O) : ℂ :=
  if physicalRay n=σ then (calibrationForSet S hS).tau⁻¹*
    gramPeriodicMonoid (calibrationForSet S hS) (calibrationForSet S hS).generator (calibrationLowData S hS) n
  else 0

lemma gramCoefficientExtension_norm (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing) (n : O) :
    ‖gramCoefficientExtension S hS σ n‖≤1 := by
  unfold gramCoefficientExtension
  split_ifs
  · rw [norm_mul,norm_inv,calibrationForSet_tau_norm,inv_one,one_mul]
    exact gramPeriodicMonoid_norm _ _ _ _
  · simp

lemma gramCoefficientExtension_zero (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (σ : RayRing) (n : O)
    (hn : ¬IsCoprime (calibrationForSet S hS).generator n) : gramCoefficientExtension S hS σ n=0 := by
  unfold gramCoefficientExtension
  split_ifs
  · rw [gramPeriodicMonoid_zero _ _ _ _ hn,mul_zero]
  · rfl

theorem lowGramCoefficient_eq_extension (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (s : {I : Id // Supported I}) :
    lowGramCoefficient (calibrationForSet S hS) σ s=
      gramCoefficientExtension S hS σ (primaryGenerator s.val) := by
  unfold lowGramCoefficient gramCoefficientExtension
  change (if physicalRay (primaryGenerator s.val)=σ then _ else 0)=_
  rw [lowArithmeticCoefficient_periodic S hS hbad s]

theorem gramCoefficientExtension_periodic (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (σ : RayRing) (x y : O) (hxy : x-y∈gramFixedModulus S hS) :
    gramCoefficientExtension S hS σ x=gramCoefficientExtension S hS σ y := by
  have hr : physicalRay x=physicalRay y := Ideal.Quotient.eq.mpr (Ideal.mul_le_right hxy)
  have hm := gramPeriodicMonoid_periodic (calibrationForSet S hS) (calibrationForSet S hS).generator
    (calibrationLowData S hS) x y (Ideal.mul_le_left hxy)
  simp only [gramCoefficientExtension,hr,hm]

lemma gramCoefficientExtension_scaled_periodic (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (σ : RayRing) (d x y : O) (hxy : x-y∈gramFixedModulus S hS) :
    gramCoefficientExtension S hS σ (d*x)=gramCoefficientExtension S hS σ (d*y) := by
  apply gramCoefficientExtension_periodic
  rw [←mul_sub]
  exact (gramFixedModulus S hS).mul_mem_left d hxy

end SevenEighths.ProbePhysical
end

end OAI

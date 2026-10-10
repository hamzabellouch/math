import OAI.NumberTheory.CubicMoment.Angular.AngularPrimeCoordinateCollection
import OAI.NumberTheory.CubicMoment.Angular.AngularResidueLift

namespace OAI

noncomputable section
open scoped BigOperators
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (ℓ : ℤ)

lemma angular_squarefreePrimeTuple_product_character (a b : Eisenstein)
    (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ)
    (r : Eisenstein) (ψ : MulChar (Residues r) ℂ) :
    primaryAngularSquarefreePrimeTuple ℓ a b (fun i => q i*r)
      (fun i => productResidueChar (η i) ψ) t W X V Y =
      ∑ z ∈ orderedConvolutionSupport (coordinatePrimeSupport W X Y),
        squarefreeConvolution (coordinatePrimeSupport W X Y) (coordinateFactor q η t W X) z*
          (mixedCubic a b z*ψ (Ideal.Quotient.mk (modulus r) z)*theta ℓ z*V (norm z/Y)) := by
  unfold primaryAngularSquarefreePrimeTuple
  apply Finset.sum_congr rfl
  intro z hz
  have hf : coordinateFactor (fun i => q i*r)
      (fun i => productResidueChar (η i) ψ) t W X =
      fun i n => coordinateFactor q η t W X i n*ψ (Ideal.Quotient.mk (modulus r) n) := by
    funext i n
    exact coordinateFactor_product_character q η t W X r ψ i n
  rw [hf]
  let χ : Eisenstein →* ℂ := ψ.toMonoidHom.comp (Ideal.Quotient.mk (modulus r)).toMonoidHom
  change squarefreeConvolution _ (fun i n => coordinateFactor q η t W X i n*χ n) z*_
    = _
  rw [squarefreeConvolution_mul_character]
  change (_*ψ (Ideal.Quotient.mk (modulus r) z))*_ = _
  ring

lemma angular_squarefreePrimeTuple_small_second_conductor (a b : Eisenstein) (hb : primary b)
    (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ) :
    primaryAngularSquarefreePrimeTuple ℓ a 1 (fun i => q i*(3*(1*b)))
      (fun i => productResidueChar (η i) (primaryMixedResidueChar 1 b primary_one hb))
        t W X V Y = primaryAngularSquarefreePrimeTuple ℓ a b q η t W X V Y := by
  rw [angular_squarefreePrimeTuple_product_character ℓ]
  unfold primaryAngularSquarefreePrimeTuple
  apply Finset.sum_congr rfl
  intro z hz
  have hzprim := orderedPrimarySupport_primary (coordinatePrimeSupport W X Y)
    (fun i p hp => (coordinatePrimeSupport_primary W X Y i p hp).1) hz
  rw [primaryMixedResidueChar_primary primary_one hb hzprim]
  simp only [mixedCubic,cubicSymbol_one_lower,star_one,mul_one,one_mul]

lemma angular_squarefreePrimeTuple_lift (a b : Eisenstein)
    (q : ι → Eisenstein) (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ) :
    primaryAngularSquarefreePrimeTuple ℓ a b (fun i => q i*3)
      (fun i => angularLiftResidueChar (η i) ℓ) t W X V Y =
        primaryAngularSquarefreePrimeTuple ℓ a b q η t W X V Y := by
  dsimp only [angularLiftResidueChar]
  rw [angular_squarefreePrimeTuple_product_character]
  unfold primaryAngularSquarefreePrimeTuple
  apply Finset.sum_congr rfl
  intro z hz
  have hp := orderedPrimarySupport_primary (coordinatePrimeSupport W X Y)
    (fun i p h => (coordinatePrimeSupport_primary W X Y i p h).1) hz
  rw [angularCorrectionChar_mk,angularUnitCorrection_primary hp,mul_one]

end CubicFirstMoment

end

end OAI

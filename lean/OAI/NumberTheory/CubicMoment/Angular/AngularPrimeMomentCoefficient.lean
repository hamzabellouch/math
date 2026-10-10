import OAI.NumberTheory.CubicMoment.Angular.AngularSquarefreeTwists
import OAI.NumberTheory.CubicMoment.Estimates.PrimeMomentCoefficient

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (ℓ : ℤ)

def structuredAngularPrimeMoment (a b v e : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ) : ℂ :=
  ∑ z ∈ (orderedConvolutionSupport (coordinatePrimeSupport W X Y)).filter
      (fun z => IsCoprime z e),
    primeMomentCoefficient W X Y z*theta ℓ z*mellinPhase u (norm z)*
      cubicSymbol z (v*a*b^2)*V (norm z/Y)

/-- The literal numerator and excluded-prime factors are assembled into
one explicitly constructed finite character of modulus 9ve. -/
lemma structuredAngularPrimeMoment_eq_tuple (hpub : CubicSupplementaryPeriodicity)
    (a b v e : Eisenstein) (ha : primary a) (hb : primary b) (hv : v ≠ 0)
    (u : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ) :
    structuredAngularPrimeMoment ℓ a b v e u W X V Y =
      primaryAngularSquarefreePrimeTuple ℓ a b (fun _ : ι => 1*((9*v)*e))
        (fun _ => productResidueChar (1 : MulChar (Residues (1:Eisenstein)) ℂ)
          (productResidueChar (cubicNumeratorChar hpub v hv) (1 : MulChar (Residues e) ℂ)))
        (fun _ => u) W X V Y := by
  rw [angular_squarefreePrimeTuple_product_character ℓ]
  have hf : coordinateFactor (fun _ : ι => 1) (fun _ => 1) (fun _ => u) W X =
      fun i n => W i (norm n/X i)*mellinPhase u (norm n) := by
    funext i n
    simp only [coordinateFactor,MulChar.one_apply (residue_isUnit_of_isCoprime isCoprime_one_left),mul_one]
  rw [hf,structuredAngularPrimeMoment,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z hz
  have hzprim := orderedPrimarySupport_primary (coordinatePrimeSupport W X Y)
    (fun i n hn => (coordinatePrimeSupport_primary W X Y i n hn).1) hz
  rw [squarefreeConvolution_norm_twist _
    (fun i n hn => (coordinatePrimeSupport_primary W X Y i n hn).2.ne_zero),
    productResidueChar_mk,cubicNumeratorChar_primary hpub v hv hzprim,principal_residue_value]
  by_cases hcop : IsCoprime z e
  · rw [ite_eq_left hcop,ite_eq_left hcop,mul_one,mixedCubic_numerator ha hb hzprim,
      cubicSymbol_mul_upper hzprim]
    simp only [cubicSymbol_mul_upper hzprim]
    unfold primeMomentCoefficient
    ring
  · simp only [ite_eq_right hcop,mul_zero,zero_mul]

lemma structuredAngularPrimeMoment_eq_lifted_tuple (hperiod : CubicSupplementaryPeriodicity)
    (a b v e : Eisenstein) (ha : primary a) (hb : primary b) (hv : v ≠ 0)
    (u : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ) (V : ℝ → ℂ) (Y : ℝ) :
    structuredAngularPrimeMoment ℓ a b v e u W X V Y =
      primaryAngularSquarefreePrimeTuple ℓ a b (fun _ : ι => structuredAngularTwistModulus v e)
        (fun _ => structuredAngularTwistCharacter hperiod v e hv ℓ)
        (fun _ => u) W X V Y := by
  rw [structuredAngularPrimeMoment_eq_tuple ℓ hperiod a b v e ha hb hv u W X V Y]
  exact (angular_squarefreePrimeTuple_lift ℓ a b (fun _ : ι => structuredTwistModulus v e)
    (fun _ => structuredTwistCharacter hperiod v e hv) (fun _ => u) W X V Y).symm

end CubicFirstMoment

end

end OAI

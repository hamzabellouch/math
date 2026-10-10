import OAI.NumberTheory.CubicMoment.Estimates.StructuredResidualFrequencies
import OAI.NumberTheory.CubicMoment.Angular.AngularFullPrimeConvolution
import OAI.NumberTheory.CubicMoment.Estimates.NoncubeOrdinaryBounds
import OAI.NumberTheory.CubicGram.MixedPoisson

namespace OAI

/-! Exact passage from ramified/cube frequencies to the structured pair
moments. A cube factor becomes an arithmetic exclusion. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma fullStructuredAngularPrimeSum_residual (R : ℝ) (r j p q v e : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) :
    fullStructuredAngularPrimeSum ℓ R (r*p*q^2*j^3) 1 v e u W X =
      fullStructuredAngularPrimeSum ℓ R p q (v*r) (e*j) u W X := by
  unfold fullStructuredAngularPrimeSum
  rw [Finset.sum_filter,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z hz
  have hp := orderedPrimarySupport_primary (fullPrimeSupport R W X)
    (fullPrimeSupport_primary R W X) hz
  have hcop : IsCoprime z (e*j) ↔ IsCoprime z e ∧ IsCoprime z j :=
    ⟨fun h => ⟨h.of_mul_right_left,h.of_mul_right_right⟩,fun h => h.1.mul_right h.2⟩
  have hnum : v*(r*p*q^2*j^3)*1^2 = ((v*r)*p*q^2)*j^3 := by ring
  rw [hnum,cubicSymbol_mul_upper hp,cubicSymbol_cube_indicator hp j]
  by_cases he : IsCoprime z e <;> by_cases hj : IsCoprime z j <;>
    simp only [hcop,he,hj,and_self,and_false,false_and,ite_true,ite_false,mul_one,mul_zero]

lemma fullStructuredAngular_residual_mass_le (R : ℝ) (Ram J H : Finset Eisenstein)
    (P : Finset (Eisenstein × Eisenstein))
    (hH : H ⊆ coprimeResidualSupport Ram J P) (v e : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) :
    (∑ h ∈ H, ‖fullStructuredAngularPrimeSum ℓ R h 1 v e u W X‖^2) ≤
      ∑ r ∈ Ram, ∑ j ∈ J, ∑ z ∈ P,
        ‖fullStructuredAngularPrimeSum ℓ R z.1 z.2 (v*r) (e*j) u W X‖^2 := by
  apply (Finset.sum_le_sum_of_subset_of_nonneg hH (fun _ _ _ => sq_nonneg _)).trans
  unfold coprimeResidualSupport
  apply (Finset.sum_image_le_of_nonneg (fun _ _ => sq_nonneg _)).trans_eq
  calc
    _ = ∑ r ∈ Ram, ∑ j ∈ J, ∑ z ∈ P,
        ‖fullStructuredAngularPrimeSum ℓ R (r*z.1*z.2^2*j^3) 1 v e u W X‖^2 :=
      (Finset.sum_product (Ram.product J) P
        (fun t : (Eisenstein × Eisenstein) × (Eisenstein × Eisenstein) =>
          ‖fullStructuredAngularPrimeSum ℓ R (t.1.1*t.2.1*t.2.2^2*t.1.2^3) 1 v e u W X‖^2)).trans
        (Finset.sum_product Ram J (fun t : Eisenstein × Eisenstein =>
          ∑ z ∈ P, ‖fullStructuredAngularPrimeSum ℓ R (t.1*z.1*z.2^2*t.2^3) 1 v e u W X‖^2))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro z hz
      rw [fullStructuredAngularPrimeSum_residual ℓ]

end CubicFirstMoment

end

end OAI

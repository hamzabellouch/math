import OAI.NumberTheory.CubicMoment.Estimates.FullPrimeConvolution
import OAI.NumberTheory.CubicMoment.Estimates.NoncubeOrdinaryBounds
import OAI.NumberTheory.CubicGram.MixedPoisson

namespace OAI

/-! Exact passage from ramified/cube frequencies to the structured pair
moments. A cube factor becomes an arithmetic exclusion. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma fullPrimeSupport_primary (R : ℝ) (W : ι → ℝ → ℂ) (X : ι → ℝ) :
    ∀ i, ∀ z ∈ fullPrimeSupport R W X i, primary z := by
  intro i z hz
  exact (mem_primaryElementBall.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).1).1

lemma cubicSymbol_cube_indicator {z : Eisenstein} (hz : primary z) (j : Eisenstein) :
    cubicSymbol z (j^3) = if IsCoprime z j then 1 else 0 := by
  rw [cubicSymbol_pow_upper hz]
  by_cases hj : IsCoprime z j
  · rw [ite_eq_left hj,cubicSymbol_cube_of_isCoprime hz j hj]
  · rw [ite_eq_right hj,cubicSymbol_eq_zero_of_not_isCoprime hz hj,zero_pow (by norm_num : (3:ℕ) ≠ 0)]

lemma fullStructuredPrimeSum_residual (R : ℝ) (r j p q v e : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) :
    fullStructuredPrimeSum R (r*p*q^2*j^3) 1 v e u W X =
      fullStructuredPrimeSum R p q (v*r) (e*j) u W X := by
  unfold fullStructuredPrimeSum
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

lemma fullStructured_residual_mass_le (R : ℝ) (Ram J H : Finset Eisenstein)
    (P : Finset (Eisenstein × Eisenstein))
    (hH : H ⊆ coprimeResidualSupport Ram J P) (v e : Eisenstein) (u : ℝ)
    (W : ι → ℝ → ℂ) (X : ι → ℝ) :
    (∑ h ∈ H, ‖fullStructuredPrimeSum R h 1 v e u W X‖^2) ≤
      ∑ r ∈ Ram, ∑ j ∈ J, ∑ z ∈ P,
        ‖fullStructuredPrimeSum R z.1 z.2 (v*r) (e*j) u W X‖^2 := by
  apply (Finset.sum_le_sum_of_subset_of_nonneg hH (fun _ _ _ => sq_nonneg _)).trans
  unfold coprimeResidualSupport
  apply (Finset.sum_image_le_of_nonneg (fun _ _ => sq_nonneg _)).trans_eq
  calc
    _ = ∑ r ∈ Ram, ∑ j ∈ J, ∑ z ∈ P,
        ‖fullStructuredPrimeSum R (r*z.1*z.2^2*j^3) 1 v e u W X‖^2 :=
      (Finset.sum_product (Ram.product J) P
        (fun t : (Eisenstein × Eisenstein) × (Eisenstein × Eisenstein) =>
          ‖fullStructuredPrimeSum R (t.1.1*t.2.1*t.2.2^2*t.1.2^3) 1 v e u W X‖^2)).trans
        (Finset.sum_product Ram J (fun t : Eisenstein × Eisenstein =>
          ∑ z ∈ P, ‖fullStructuredPrimeSum R (t.1*z.1*z.2^2*t.2^3) 1 v e u W X‖^2))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro z hz
      rw [fullStructuredPrimeSum_residual]

end CubicFirstMoment

end

end OAI

import OAI.Probability.InvariantIsing.Magnetic.MagneticGroupPath
import OAI.Probability.InvariantIsing.Magnetic.MagneticPartitionSupport

namespace OAI

/-! The supporting inequality for the weighted magnetic functional,
with the same common height path for all field groups. -/
noncomputable section
open MeasureTheory IsingPerceptron
open scoped BigOperators
namespace InvariantIsing

lemma fieldPairing_magneticGroup {A : Type*} [Fintype A] (γ mag : A → ℝ)
    (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a=1) (h k : FieldStep) :
    fieldPairing (magneticGroupPath γ mag hγ hγsum h) k =
      ∑ a, γ a * fieldPairing (magneticFieldPath h (mag a)) k := by
  unfold fieldPairing
  simp_rw [magneticGroupPath_eq_sum, Finset.sum_mul, mul_assoc]
  rw [integral_finsetSum _ (fun a _ => (integrable_path_mul_field (magneticFieldPath h (mag a)) k).const_mul (γ a))]
  simp only [integral_const_mul]

lemma magneticGroup_support_pairing {A : Type*} [Fintype A] (γ mag : A → ℝ)
    (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a=1) (hmag : ∀ a, |mag a|<1)
    (h k : FieldStep) :
    magneticGroupValue γ mag k + fieldPairing (magneticGroupPath γ mag hγ hγsum h) k/2 ≤
      magneticGroupValue γ mag h + fieldPairing (magneticGroupPath γ mag hγ hγsum h) h/2 := by
  have he (v : FieldStep) : magneticGroupValue γ mag v +
      fieldPairing (magneticGroupPath γ mag hγ hγsum h) v/2 =
      ∑ a, γ a * (constrainedFieldValue v (mag a) +
        (1/2 : ℝ)*fieldPairing (magneticFieldPath h (mag a)) v) := by
    rw [fieldPairing_magneticGroup]
    simp only [magneticGroupValue, mul_add, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [he k,he h]
  exact Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left
    (magneticField_support_pairing h k (hmag a)) (hγ a)

theorem magneticGroup_support {A : Type*} [Fintype A] (γ mag : A → ℝ)
    (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a=1) (hmag : ∀ a, |mag a|<1)
    (h k : FieldStep) :
    magneticGroupValue γ mag k ≤ magneticGroupValue γ mag h -
      (∫ s, magneticGroupPath γ mag hγ hγsum h s *
        (fieldFunction k s-fieldFunction h s) ∂pathMeasure)/2 := by
  have hs := magneticGroup_support_pairing γ mag hγ hγsum hmag h k
  have he : (∫ s, magneticGroupPath γ mag hγ hγsum h s *
      (fieldFunction k s-fieldFunction h s) ∂pathMeasure) =
      fieldPairing (magneticGroupPath γ mag hγ hγsum h) k -
        fieldPairing (magneticGroupPath γ mag hγ hγsum h) h := by
    simp only [mul_sub]
    exact integral_sub (integrable_path_mul_field _ _) (integrable_path_mul_field _ _)
  rw [he]
  linarith

end InvariantIsing

end

end OAI

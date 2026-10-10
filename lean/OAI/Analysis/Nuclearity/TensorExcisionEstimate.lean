import OAI.Analysis.WeakInfiniteness.TensorNorm
import OAI.Analysis.WeakInfiniteness.CrossUniverseTensorMap

namespace OAI

/-! Finite tensor estimates for the product-state excision step in the
elementary-ideal argument. The estimates are independent of nuclearity. -/

noncomputable section
open scoped BigOperators

namespace WeakPureInfiniteness

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

private def elementaryLeftLinear (b : B) : A →ₗ[ℂ] MinimalTensor A B where
  toFun a := minimalElementary a b
  map_add' a c := Subtype.ext (spatialElementary_add_left a c b)
  map_smul' r a := minimalElementary_smul_left r a b

private def elementaryRightLinear (a : A) : B →ₗ[ℂ] MinimalTensor A B where
  toFun b := minimalElementary a b
  map_add' b c := Subtype.ext (spatialElementary_add_right a b c)
  map_smul' r b := Subtype.ext (spatialElementary_smul_right r a b)

private lemma norm_sandwich_le (e a : A) (he : ‖e‖ ≤ 1) : ‖e * a * e‖ ≤ ‖a‖ := by
  calc
    _ ≤ (‖e‖ * ‖a‖) * ‖e‖ := (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ (1 * ‖a‖) * 1 := mul_le_mul
      (mul_le_mul_of_nonneg_right he (norm_nonneg _)) he (norm_nonneg _) (by positivity)
    _ = ‖a‖ := by ring

lemma tensor_excision_error_identity (e a : A) (f b : B) (α β : ℂ) :
    minimalElementary e f * minimalElementary a b * minimalElementary e f -
        (α * β) • minimalElementary (e * e) (f * f) =
      minimalElementary (e * a * e - α • (e * e)) (f * b * f) +
        α • minimalElementary (e * e) (f * b * f - β • (f * f)) := by
  rw [← minimalElementary_mul, ← minimalElementary_mul]
  change minimalElementary (e * a * e) (f * b * f) - _ =
    elementaryLeftLinear (f * b * f) (e * a * e - α • (e * e)) +
      α • elementaryRightLinear (e * e) (f * b * f - β • (f * f))
  simp only [map_sub, map_smul, elementaryLeftLinear, elementaryRightLinear,
    LinearMap.coe_mk, AddHom.coe_mk, smul_sub, smul_smul]
  abel

theorem tensor_excision_error_le (e a : A) (f b : B) (α β : ℂ)
    (he : ‖e‖ ≤ 1) (hf : ‖f‖ ≤ 1) (hα : ‖α‖ ≤ ‖a‖)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (ha : ‖e * a * e - α • (e * e)‖ ≤ δ)
    (hb : ‖f * b * f - β • (f * f)‖ ≤ δ) :
    ‖minimalElementary e f * minimalElementary a b * minimalElementary e f -
        (α * β) • minimalElementary (e * e) (f * f)‖ ≤ δ * ‖b‖ + ‖a‖ * δ := by
  rw [tensor_excision_error_identity]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · rw [norm_minimalElementary]
    exact mul_le_mul ha (norm_sandwich_le f b hf) (norm_nonneg _) hδ
  · rw [norm_smul, norm_minimalElementary]
    have he2 : ‖e * e‖ ≤ 1 := (norm_mul_le _ _).trans (by nlinarith [norm_nonneg e])
    calc
      _ ≤ ‖a‖ * (1 * δ) := mul_le_mul hα
        (mul_le_mul he2 hb (norm_nonneg _) zero_le_one)
        (by positivity) (norm_nonneg _)
      _ = _ := by ring

theorem tensor_excision_sum_error_le {I : Type*} [Fintype I]
    (e : A) (f : B) (a : I → A) (b : I → B) (α β : I → ℂ)
    (he : ‖e‖ ≤ 1) (hf : ‖f‖ ≤ 1) (hα : ∀ i, ‖α i‖ ≤ ‖a i‖)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (ha : ∀ i, ‖e * a i * e - α i • (e * e)‖ ≤ δ)
    (hb : ∀ i, ‖f * b i * f - β i • (f * f)‖ ≤ δ) :
    ‖minimalElementary e f * (∑ i : I, minimalElementary (a i) (b i)) * minimalElementary e f -
        (∑ i : I, α i * β i) • minimalElementary (e * e) (f * f)‖ ≤
      δ * (∑ i : I, (‖b i‖ + ‖a i‖)) := by
  classical
  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_smul, ← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ i : I, (δ * ‖b i‖ + ‖a i‖ * δ) := Finset.sum_le_sum fun i _ =>
      tensor_excision_error_le e (a i) f (b i) (α i) (β i) he hf (hα i) hδ (ha i) (hb i)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

end WeakPureInfiniteness

end

end OAI

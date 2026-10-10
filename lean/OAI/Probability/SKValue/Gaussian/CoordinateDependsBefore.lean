import Mathlib
import OAI.Probability.SKValue.Equations.GradientErrorConstant

namespace OAI

section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal
namespace SKValue
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

lemma coordinate_dependsBefore {N i j : ℕ} (hi : i<N+1) (hij : i<j) :
    DependsBefore j (coordinate N i) := by
  intro z z' h
  rw [coordinate_eq_apply hi, coordinate_eq_apply hi]
  exact h ⟨i,hi⟩ hij

lemma finite_rounding_coefficient {N : ℕ} {U K : (Fin (N+1) → ℝ) → ℝ}
    (hU : Measurable U) (hK : Measurable K)
    (hKi : Integrable K (gaussianProduct (Fin (N+1))))
    (hUb : ∀ z, |U z|≤1) (hUp : DependsBefore N U) (hKp : DependsBefore N K) :
    (∫ z, Real.sign (U z+2*cdf standardGaussian (coordinate N N z)-1)*K z
      ∂gaussianProduct (Fin (N+1))) = ∫ z, U z*K z ∂gaussianProduct (Fin (N+1)) := by
  let : IsProbabilityMeasure (gaussianProduct (Fin (N+1))) := gaussianProduct_probability _
  exact independent_rounding_integral hU hK hKi (Filter.Eventually.of_forall hUb)
    (coordinate_hasLaw N N) ((hUp.prodMk hKp).independent (by omega) (hU.prodMk hK))

lemma normalized_family_orthonormal {N : ℕ}
    {H : Fin N → (Fin (N+1) → ℝ) → ℝ}
    (hm : ∀ j, Measurable (H j)) (hp : ∀ j : Fin N, DependsBefore (j : ℕ) (H j))
    (hpos : ∀ j, 0 < ∫ z, (H j z)^2 ∂gaussianProduct (Fin (N+1))) :
    ∀ i j : Fin N,
      (∫ z, normalizedIncrement (H i) (coordinate N i) (gaussianProduct (Fin (N+1))) z *
        normalizedIncrement (H j) (coordinate N j) (gaussianProduct (Fin (N+1))) z
        ∂gaussianProduct (Fin (N+1))) = if i=j then 1 else 0 := by
  intro i j
  rcases lt_trichotomy i j with hij | rfl | hji
  · rw [ite_eq_right (ne_of_lt hij)]
    exact normalizedIncrements_orthogonal hij (by omega) (hm i) (hm j) (hp i) (hp j)
  · rw [ite_eq_left rfl]
    simp only [← pow_two]
    exact normalizedIncrement_second_moment (hm i).aestronglyMeasurable (coordinate_hasLaw N i)
      ((hp i).independent (by omega) (hm i)) (hpos i)
  · rw [ite_eq_right (ne_of_gt hji)]
    rw [show (fun z ↦ normalizedIncrement (H i) (coordinate N i) (gaussianProduct (Fin (N+1))) z *
        normalizedIncrement (H j) (coordinate N j) (gaussianProduct (Fin (N+1))) z) =
      (fun z ↦ normalizedIncrement (H j) (coordinate N j) (gaussianProduct (Fin (N+1))) z *
        normalizedIncrement (H i) (coordinate N i) (gaussianProduct (Fin (N+1))) z)
        from funext (fun _ ↦ mul_comm _ _)]
    exact normalizedIncrements_orthogonal hji (by omega) (hm j) (hm i) (hp j) (hp i)

lemma coordinate_family_orthonormal (N : ℕ) :
    ∀ i j : Fin N, (∫ z, coordinate N i z*coordinate N j z
      ∂gaussianProduct (Fin (N+1))) = if i=j then 1 else 0 := by
  intro i j
  rcases lt_trichotomy i j with hij | rfl | hji
  · rw [ite_eq_right (ne_of_lt hij)]
    have hind := (coordinate_dependsBefore (by omega : (i : ℕ)<N+1) hij).independent
      (by omega : (j : ℕ)<N+1) (measurable_coordinate N i)
    have h := hind.integral_mul_eq_mul_integral (measurable_coordinate N i).aestronglyMeasurable
      (measurable_coordinate N j).aestronglyMeasurable
    simp only [Pi.mul_apply] at h
    rw [h, gaussian_mean (coordinate_hasLaw N j), mul_zero]
  · rw [ite_eq_left rfl]
    simpa only [← pow_two] using gaussian_second_moment (coordinate_hasLaw N i)
  · rw [ite_eq_right (ne_of_gt hji)]
    have hind := (coordinate_dependsBefore (by omega : (j : ℕ)<N+1) hji).independent
      (by omega : (i : ℕ)<N+1) (measurable_coordinate N j)
    have h := hind.symm.integral_mul_eq_mul_integral (measurable_coordinate N i).aestronglyMeasurable
      (measurable_coordinate N j).aestronglyMeasurable
    simp only [Pi.mul_apply] at h
    rw [h, gaussian_mean (coordinate_hasLaw N j), mul_zero]

lemma normalized_coordinate_pair {N : ℕ}
    {H : Fin N → (Fin (N+1) → ℝ) → ℝ}
    (hm : ∀ j, Measurable (H j)) (hp : ∀ j : Fin N, DependsBefore (j : ℕ) (H j)) (i j : Fin N) :
    (∫ z, normalizedIncrement (H i) (coordinate N i) (gaussianProduct (Fin (N+1))) z *
      coordinate N j z ∂gaussianProduct (Fin (N+1))) =
      if i=j then predictableNormalizer (H i) (gaussianProduct (Fin (N+1))) *
        ∫ z, H i z ∂gaussianProduct (Fin (N+1)) else 0 := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · rw [ite_eq_right (ne_of_lt hij)]
    have hind := ((normalizedIncrement_dependsBefore (by omega) (hp i)).mono
      (show (i : ℕ)+1≤j from hij)).independent (by omega : (j : ℕ)<N+1)
        (measurable_normalizedIncrement (hm i))
    have h := hind.integral_mul_eq_mul_integral (measurable_normalizedIncrement (hm i)).aestronglyMeasurable
      (measurable_coordinate N j).aestronglyMeasurable
    simp only [Pi.mul_apply] at h
    rw [h, gaussian_mean (coordinate_hasLaw N j), mul_zero]
  · rw [ite_eq_left rfl]
    exact normalizedIncrement_gaussian_coefficient (hm i).aestronglyMeasurable (coordinate_hasLaw N i)
      ((hp i).independent (by omega) (hm i))
  · rw [ite_eq_right (ne_of_gt hji)]
    have heq := predictable_product_mean_zero (hm i).aestronglyMeasurable
      (measurable_coordinate N j).aestronglyMeasurable (coordinate_hasLaw N i)
      (((hp i).mul (coordinate_dependsBefore (by omega) hji)).independent (by omega)
        ((hm i).mul (measurable_coordinate N j)))
    simpa only [mul_comm] using heq

end SKValue

end

end OAI

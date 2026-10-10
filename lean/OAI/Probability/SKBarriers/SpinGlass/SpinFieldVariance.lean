import Mathlib
import OAI.Probability.SKBarriers.SpinGlass.SpinMonomials
import OAI.Probability.SKBarriers.Hierarchy.HierarchyJointLaw

namespace OAI

section
section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
noncomputable section
open MeasureTheory Set Filter
open scoped Topology Interval
noncomputable section
open MeasureTheory Set
open scoped Interval
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology
namespace SK
open Analytic

theorem hierarchy_spin_variance_probability {N : ℕ} (d : ℕ) (m : Fin d → ℝ)
    (hm : ∀ j, 0 ≤ m j) (hmu : ∀ j, m j ≤ 1) (hmono : Monotone m)
    (a b : Fin d → ℝ) (I : Fin d → Finset (Fin N)) :
    ProbabilityTheory.variance (fun sz => spinExponent d b I sz.1 sz.2)
      (hierarchyLaw d m (spinExponent d a I)) ≤ ∑ j, (b j)^2 := by
  rw [hierarchyLaw_variance d m hm hmu hmono _ _ (spinExponent_sq_le d b I)]
  exact hierarchy_spin_variance d m hm hmu hmono a b I

def fieldCoefficients {N d : ℕ} (e : Fin N ↪ Fin d) (j : Fin d) : ℝ :=
  if j ∈ Finset.univ.image e then (N : ℝ)⁻¹ else 0

theorem fieldCoefficients_squares {N d : ℕ} (e : Fin N ↪ Fin d) :
    (∑ j, (fieldCoefficients e j)^2) = (N : ℝ)⁻¹ := by
  classical
  have hc : (Finset.univ.image e).card = N := by
    rw [Finset.card_image_of_injective _ e.injective]
    simp
  simp only [fieldCoefficients,ite_pow,zero_pow (by omega : 2 ≠ 0)]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero,add_zero,Finset.filter_mem_eq_inter,
    Finset.univ_inter,Finset.sum_const,hc,nsmul_eq_mul]
  by_cases hN : N = 0
  · simp [hN]
  · have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN
    field_simp

theorem spinExponent_field {N d : ℕ} (e : Fin N ↪ Fin d)
    (I : Fin d → Finset (Fin N)) (hI : ∀ i, I (e i) = {i})
    (s : Config N) (z : ParameterSpace d) :
    spinExponent d (fieldCoefficients e) I s z =
      (∑ i : Fin N, coordinateProjection d (e i) z * spin (s i))/(N : ℝ) := by
  classical
  simp only [spinExponent,coordinateLinear_apply,fieldCoefficients,ite_mul,zero_mul]
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero,add_zero,Finset.filter_mem_eq_inter,Finset.univ_inter]
  rw [Finset.sum_image (fun i _ j _ hij => e.injective hij)]
  simp only [hI,spinMonomial,Finset.prod_singleton]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem hierarchy_field_energy {N d : ℕ} (e : Fin N ↪ Fin d)
    (m : Fin d → ℝ) (hm : ∀ j, 0 ≤ m j) (hmu : ∀ j, m j ≤ 1) (hmono : Monotone m)
    (a : Fin d → ℝ) (I : Fin d → Finset (Fin N)) (hI : ∀ i, I (e i) = {i}) :
    ProbabilityTheory.variance
      (fun sz => (∑ i : Fin N, coordinateProjection d (e i) sz.2 * spin (sz.1 i))/(N : ℝ))
      (hierarchyLaw d m (spinExponent d a I)) ≤ 1/(N : ℝ) := by
  have hh := hierarchy_spin_variance_probability d m hm hmu hmono a (fieldCoefficients e) I
  simpa only [spinExponent_field e I hI,fieldCoefficients_squares,one_div] using hh

end SK

end
end
end
end
end
end

end OAI

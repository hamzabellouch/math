import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.HierarchyIncrementCovariance

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section
variable {S : Type} [Fintype S] [Nonempty S]

theorem affineHierarchy_weighted_increment_square (n : ℕ) (m : Fin n → ℝ)
    (c : S → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ) (g : S → ℝ)
    (a k : Fin n → ℝ) (hU : ∀ s i, U s (coordinateAxis n i)=a i*g s) (x : ℝ) :
    (∫ z, (∑ i, k i*a i*coordinateProjection n i z)^2
      ∂hierarchyPathLaw n m (affineLogPartition c U) x)=
      (∑ i, (k i)^2*(a i)^2)+
      ∑ i, ∑ j, k i*k j*(a i)^2*(a j)^2*m (max i j)*
        affineHierarchyResponse n m c U g (min i j) x := by
  classical
  let f := affineLogPartition c U
  let μ := hierarchyPathLaw n m f x
  have hf := affineLogPartition_boundedDerivs c U
  have hij (i j : Fin n) : Integrable (fun z =>
      (k i*a i*coordinateProjection n i z)*(k j*a j*coordinateProjection n j z)) μ :=
    (((HasExpGrowth.const (k i*a i)).mul (HasExpGrowth.linear (coordinateProjection n i))).mul
      ((HasExpGrowth.const (k j*a j)).mul (HasExpGrowth.linear (coordinateProjection n j)))).integrable_hierarchyPathLaw n m hf
      (((coordinateProjection n i).continuous.const_mul _).mul
        ((coordinateProjection n j).continuous.const_mul _)) x
  have he (z : ParameterSpace n) : (∑ i, k i*a i*coordinateProjection n i z)^2=
      ∑ i, ∑ j, (k i*a i*coordinateProjection n i z)*(k j*a j*coordinateProjection n j z) := by
    rw [pow_two, Finset.sum_mul]
    simp only [Finset.mul_sum]
  rw [integral_congr_ae (ae_of_all _ he),integral_finsetSum _ (fun i _ =>
    integrable_finsetSum _ (fun j _ => hij i j))]
  simp_rw [integral_finsetSum _ (fun j _ => hij _ j)]
  have hterm (i j : Fin n) : (∫ z,
      (k i*a i*coordinateProjection n i z)*(k j*a j*coordinateProjection n j z) ∂μ)=
      (if i=j then (k i)^2*(a i)^2 else 0)+
        k i*k j*(a i)^2*(a j)^2*m (max i j)*affineHierarchyResponse n m c U g (min i j) x := by
    have hp (z : ParameterSpace n) :
        (k i*a i*coordinateProjection n i z)*(k j*a j*coordinateProjection n j z)=
        (k i*a i*(k j*a j))*(coordinateProjection n i z*coordinateProjection n j z) := by ring
    rw [integral_congr_ae (ae_of_all _ hp),integral_const_mul,
      affineHierarchy_increment_covariance_symm n m c U g a hU i j x]
    by_cases h : i=j
    · subst j; simp only [ite_true]; ring
    · simp only [ite_eq_right h]; ring
  simp_rw [hterm,Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true]

end

end SK.Analytic

end
end

end OAI

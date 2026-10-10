import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.HierarchyScoreBound
import OAI.Probability.SKBarriers.Scalar.TiltedExponentialSquare

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem hierarchyPathLaw_eq_tilted (n : ℕ) (m : Fin n → ℝ)
    (f : ParameterSpace n → ℝ) (hf : BoundedDerivs f) (x : ℝ) :
    hierarchyPathLaw n m f x=(fiberGaussian n x).tilted (hierarchyPathLogDensity n m f) := by
  have he : (fun z => Real.exp (hierarchyPathLogDensity n m f z))=hierarchyPathWeight n m f := by
    funext z
    simpa only [hierarchyPathLogDensity,one_mul] using (hierarchyPathWeight_eq n m f 1 z).symm
  rw [Measure.tilted,he,(hierarchyPathWeight_normalized n m f hf x).2]
  simp only [div_one,hierarchyPathLaw]
  simp_rw [show ∀ z, Real.exp (hierarchyPathLogDensity n m f z)=hierarchyPathWeight n m f z from fun z => congrFun he z]

section
variable {S : Type} [Fintype S] [Nonempty S]

theorem affineHierarchy_exp_square_bound (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m)
    (d : S → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ) (C : Fin n → ℝ)
    (hC : ∀ i, 0 ≤ C i) (hU : ∀ s i, |U s (coordinateAxis n i)| ≤ C i)
    (x : ℝ) (a : Fin n → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hsmall : c*(4*(∑ i, (a i)^2)+(2*∑ i, |a i| *C i)^2) ≤ 1/2) :
    Integrable (fun z => Real.exp (c*(coordinateLinear n a z)^2))
      (hierarchyPathLaw n m (affineLogPartition d U) x) ∧
    (∫ z, Real.exp (c*(coordinateLinear n a z)^2)
      ∂hierarchyPathLaw n m (affineLogPartition d U) x) ≤ 2 := by
  rw [hierarchyPathLaw_eq_tilted n m _ (affineLogPartition_boundedDerivs d U) x]
  exact tilted_linear_exp_square_bound n _
    (hierarchyPathLogDensity_regular n m (affineLogPartition_boundedDerivs d U)) x a
    (mul_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (hC i)))) (affineHierarchy_score_direction_bound n m hm hmono d U C hC hU a) hc hsmall

theorem affineHierarchy_square_bound (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m)
    (d : S → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ) (C : Fin n → ℝ)
    (hC : ∀ i, 0 ≤ C i) (hU : ∀ s i, |U s (coordinateAxis n i)| ≤ C i)
    (x : ℝ) (a : Fin n → ℝ) :
    (∫ z, (coordinateLinear n a z)^2
      ∂hierarchyPathLaw n m (affineLogPartition d U) x) ≤
      2*(∑ i, (a i)^2)+(2*∑ i, |a i| *C i)^2 := by
  rw [hierarchyPathLaw_eq_tilted n m _ (affineLogPartition_boundedDerivs d U) x]
  have H := tilted_linear_even_moment_step n _
    (hierarchyPathLogDensity_regular n m (affineLogPartition_boundedDerivs d U)) x a
    (mul_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (hC i))))
    (affineHierarchy_score_direction_bound n m hm hmono d U C hC hU a) 0
  let := fiberGaussian_tilted_probability n _
    (hierarchyPathLogDensity_regular n m (affineLogPartition_boundedDerivs d U)) x
  simpa using H

end

end SK.Analytic

end
end

end OAI

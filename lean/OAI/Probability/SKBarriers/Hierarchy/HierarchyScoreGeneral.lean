import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.HierarchyExponentialMoment

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem hierarchyLevel_coordinate_bound (n : ℕ) (m : Fin n → ℝ)
    (f : ParameterSpace n → ℝ) (hf : BoundedDerivs f) (i : Fin n)
    {C : ℝ} (hC : 0 ≤ C) (hF : ∀ z, |fderiv ℝ f z (coordinateAxis n i)| ≤ C)
    (j : Fin (n+1)) (z : ParameterSpace n) :
    |fderiv ℝ (hierarchyLevel n m f j) z (coordinateAxis n i)| ≤ C := by
  by_cases h : i.val < j.val
  · rw [hierarchyLevel_gradient n m f hf j _ z (tailZero_coordinateAxis n i j h)]
    have hc : Continuous (directionalGradient f (coordinateAxis n i)) :=
      (hf.1.continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hb : ∀ z, ‖directionalGradient f (coordinateAxis n i) z‖ ≤ C := by
      intro z; simpa only [directionalGradient,Real.norm_eq_abs] using hF z
    simpa only [Real.norm_eq_abs] using
      (hierarchyMomentLevel_bounded_continuous n m f _ hf hc hC hb j).2 z
  · rw [(hierarchyLevel_invariant_of_prefix n m f _ j
        (prefixZero_coordinateAxis n i j (Nat.le_of_not_gt h))).fderiv_zero
        ((hierarchyLevel_boundedDerivs n m f hf j).1.differentiable (by norm_num)) z]
    simpa using hC

theorem hierarchy_score_coordinate_bound (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m)
    (f : ParameterSpace n → ℝ) (hf : BoundedDerivs f) (i : Fin n)
    {C : ℝ} (hC : 0 ≤ C) (hF : ∀ z, |fderiv ℝ f z (coordinateAxis n i)| ≤ C)
    (z : ParameterSpace n) :
    |fderiv ℝ (hierarchyPathLogDensity n m f) z (coordinateAxis n i)| ≤ 2*C := by
  have hp := hierarchyPenalty_boundedDerivs n m 1 f hf
  have hw (j) : 0 ≤ hierarchyAtom n m 1 j :=
    hierarchyAtom_nonneg n m zero_le_one (fun i => (hm i).1) (fun i => (hm i).2) hmono j
  have hpB : |fderiv ℝ (hierarchyPenalty n m 1 f) z (coordinateAxis n i)| ≤ C := by
    rw [fderiv_hierarchyPenalty_apply n m 1 f hf]
    calc
      _ ≤ ∑ j, |hierarchyAtom n m 1 j*fderiv ℝ (hierarchyLevel n m f j) z (coordinateAxis n i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, hierarchyAtom n m 1 j*C := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul,abs_of_nonneg (hw j)]
        exact mul_le_mul_of_nonneg_left (hierarchyLevel_coordinate_bound n m f hf i hC hF j z) (hw j)
      _ = C := by rw [← Finset.sum_mul,hierarchyAtom_sum,one_mul]
  change |fderiv ℝ (fun z => f z-hierarchyPenalty n m 1 f z) z (coordinateAxis n i)| ≤ 2*C
  rw [fderiv_fun_sub (hf.1.differentiable (by norm_num) z)
    (hp.1.differentiable (by norm_num) z),sub_apply]
  exact (abs_sub _ _).trans (by have := hF z; linarith)

theorem hierarchy_score_direction_bound (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m)
    (f : ParameterSpace n → ℝ) (hf : BoundedDerivs f) (C : Fin n → ℝ)
    (hC : ∀ i, 0 ≤ C i) (hF : ∀ z i, |fderiv ℝ f z (coordinateAxis n i)| ≤ C i)
    (a : Fin n → ℝ) (z : ParameterSpace n) :
    |fderiv ℝ (hierarchyPathLogDensity n m f) z (coordinateVector n a)| ≤
      2*∑ i, |a i| *C i := by
  rw [coordinateVector,map_sum]
  calc
    _ ≤ ∑ i, |fderiv ℝ (hierarchyPathLogDensity n m f) z (a i • coordinateAxis n i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |a i| *(2*C i) := by
      apply Finset.sum_le_sum
      intro i _
      rw [map_smul,smul_eq_mul,abs_mul]
      exact mul_le_mul_of_nonneg_left
        (hierarchy_score_coordinate_bound n m hm hmono f hf i (hC i) (fun z => hF z i) z) (abs_nonneg _)
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring

theorem hierarchy_exp_square_bound (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m)
    (f : ParameterSpace n → ℝ) (hf : BoundedDerivs f) (C : Fin n → ℝ)
    (hC : ∀ i, 0 ≤ C i) (hF : ∀ z i, |fderiv ℝ f z (coordinateAxis n i)| ≤ C i)
    (x : ℝ) (a : Fin n → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hsmall : c*(4*(∑ i, (a i)^2)+(2*∑ i, |a i| *C i)^2) ≤ 1/2) :
    Integrable (fun z => Real.exp (c*(coordinateLinear n a z)^2)) (hierarchyPathLaw n m f x) ∧
    (∫ z, Real.exp (c*(coordinateLinear n a z)^2) ∂hierarchyPathLaw n m f x) ≤ 2 := by
  rw [hierarchyPathLaw_eq_tilted n m f hf x]
  exact tilted_linear_exp_square_bound n _ (hierarchyPathLogDensity_regular n m hf) x a
    (mul_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (hC i))))
    (hierarchy_score_direction_bound n m hm hmono f hf C hC hF a) hc hsmall

theorem hierarchy_square_bound (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m)
    (f : ParameterSpace n → ℝ) (hf : BoundedDerivs f) (C : Fin n → ℝ)
    (hC : ∀ i, 0 ≤ C i) (hF : ∀ z i, |fderiv ℝ f z (coordinateAxis n i)| ≤ C i)
    (x : ℝ) (a : Fin n → ℝ) :
    (∫ z, (coordinateLinear n a z)^2 ∂hierarchyPathLaw n m f x) ≤
      2*(∑ i, (a i)^2)+(2*∑ i, |a i| *C i)^2 := by
  rw [hierarchyPathLaw_eq_tilted n m f hf x]
  have H := tilted_linear_even_moment_step n _ (hierarchyPathLogDensity_regular n m hf) x a
    (mul_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (hC i))))
    (hierarchy_score_direction_bound n m hm hmono f hf C hC hF a) 0
  let := fiberGaussian_tilted_probability n _ (hierarchyPathLogDensity_regular n m hf) x
  simpa using H

end SK.Analytic

end
end

end OAI

import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.HierarchyScoreBound
import OAI.Probability.SKBarriers.Scalar.ScalarLevelRepresentation

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem scalarLogDensity_direction_bounds (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m)
    {f : ℝ → ℝ} (hf : BoundedDerivs f) (hspin : ScalarSpinConvex f)
    (u : ParameterSpace n) (hu : scalarSpinField n v u=0) (z : ParameterSpace n) :
    |fderiv ℝ (hierarchyPathLogDensity n m (fun z => f (scalarSpinField n v z))) z u|≤
      ∑ j, hierarchyAtom n m 1 j*|scalarLevelField n v j u| ∧
    |fderiv ℝ (fderiv ℝ (hierarchyPathLogDensity n m (fun z => f (scalarSpinField n v z)))) z u u|≤
      ∑ j, hierarchyAtom n m 1 j*(scalarLevelField n v j u)^2 := by
  let F : ParameterSpace n → ℝ := fun z => f (scalarSpinField n v z)
  let P := hierarchyPenalty n m 1 F
  let V := hierarchyPathLogDensity n m F
  have hF : BoundedDerivs F := hf.compCLM (scalarSpinField n v)
  have hP : BoundedDerivs P := hierarchyPenalty_boundedDerivs n m 1 F hF
  have hV : BoundedDerivs V := hierarchyPathLogDensity_regular n m hF
  have hw (j) : 0≤hierarchyAtom n m 1 j := hierarchyAtom_nonneg n m zero_le_one
    (fun i => (hm i).1) (fun i => (hm i).2) hmono j
  have hLv (j) := hierarchyLevel_boundedDerivs n m F hF j
  have he (z) : directionalGradient V u z =
      -(∑ j, hierarchyAtom n m 1 j*directionalGradient (hierarchyLevel n m F j) u z) := by
    change fderiv ℝ (fun z => F z-P z) z u = _
    rw [fderiv_fun_sub (hF.1.differentiable (by norm_num) z)
      (hP.1.differentiable (by norm_num) z),sub_apply]
    have hz := (scalar_comp_directional hf (scalarSpinField n v) z u).1
    change fderiv ℝ F z u=_ at hz
    rw [hz,hu,mul_zero,zero_sub,fderiv_hierarchyPenalty_apply n m 1 F hF]
    rfl
  have he' : directionalGradient V u = fun z =>
      -(∑ j, hierarchyAtom n m 1 j*directionalGradient (hierarchyLevel n m F j) u z) := funext he
  change directionalGradient V u = -(fun z => ∑ j, hierarchyAtom n m 1 j*directionalGradient (hierarchyLevel n m F j) u z) at he'
  have hd (j) := (directionalGradient_contDiff _ (hLv j).1 u).differentiable (by norm_num) z
  have H := (HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
    (hd j).hasFDerivAt.const_mul (hierarchyAtom n m 1 j))).neg
  have hh : fderiv ℝ (fderiv ℝ V) z u u =
      -(∑ j, hierarchyAtom n m 1 j*fderiv ℝ (fderiv ℝ (hierarchyLevel n m F j)) z u u) := by
    have hh := congrArg (fun L : ParameterSpace n →L[ℝ] ℝ => L u) H.fderiv
    rw [← he',fderiv_directionalGradient _ hV.1] at hh
    simpa only [ContinuousLinearMap.flip_apply,neg_apply,sum_apply,smul_apply,smul_eq_mul,
      fderiv_directionalGradient _ (hLv _).1] using hh
  constructor
  · change |directionalGradient V u z|≤_
    rw [he,abs_neg]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
    rw [abs_mul,abs_of_nonneg (hw j)]
    exact mul_le_mul_of_nonneg_left (hierarchyLevel_scalar_direction_bounds n m v hm hf hspin j z u).1 (hw j)
  · change |fderiv ℝ (fderiv ℝ V) z u u|≤_
    rw [hh,abs_neg]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
    rw [abs_mul,abs_of_nonneg (hw j)]
    exact mul_le_mul_of_nonneg_left (hierarchyLevel_scalar_direction_bounds n m v hm hf hspin j z u).2 (hw j)

theorem scalarLogDensity_local_bound (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m)
    {f : ℝ → ℝ} (hf : BoundedDerivs f) (hspin : ScalarSpinConvex f)
    (u : ParameterSpace n) (hu : scalarSpinField n v u=0)
    (S : Finset (Fin (n+1))) {B : ℝ} (hB : 0≤B)
    (houtside : ∀ j, j∉S → scalarLevelField n v j u=0)
    (hinside : ∀ j∈S, |scalarLevelField n v j u|≤B) (z : ParameterSpace n) :
    |fderiv ℝ (hierarchyPathLogDensity n m (fun z => f (scalarSpinField n v z))) z u|≤
      B*∑ j∈S, hierarchyAtom n m 1 j ∧
    |fderiv ℝ (fderiv ℝ (hierarchyPathLogDensity n m (fun z => f (scalarSpinField n v z)))) z u u|≤
      B^2*∑ j∈S, hierarchyAtom n m 1 j := by
  have H := scalarLogDensity_direction_bounds n m v hm hmono hf hspin u hu z
  have hw (j) : 0≤hierarchyAtom n m 1 j := hierarchyAtom_nonneg n m zero_le_one
    (fun i => (hm i).1) (fun i => (hm i).2) hmono j
  have hb₁ : (∑ j, hierarchyAtom n m 1 j*|scalarLevelField n v j u|)≤
      B*∑ j∈S, hierarchyAtom n m 1 j := by
    rw [← Finset.sum_subset (Finset.subset_univ S) (fun j _ hj => by rw [houtside j hj]; simp)]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hinside j hj) (hw j)
  have hb₂ : (∑ j, hierarchyAtom n m 1 j*(scalarLevelField n v j u)^2)≤
      B^2*∑ j∈S, hierarchyAtom n m 1 j := by
    rw [← Finset.sum_subset (Finset.subset_univ S) (fun j _ hj => by rw [houtside j hj]; simp)]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hsq : (scalarLevelField n v j u)^2≤B^2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).mpr (hinside j hj)
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hsq (hw j)
  exact ⟨H.1.trans hb₁,H.2.trans hb₂⟩

end SK.Analytic

end
end

end OAI

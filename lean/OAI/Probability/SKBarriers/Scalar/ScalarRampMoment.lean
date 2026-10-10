import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.HierarchyExponentialMoment
import OAI.Probability.SKBarriers.Scalar.ScalarLevelRepresentation
import OAI.Probability.SKBarriers.Gaussian.FiberLipschitzTent

namespace OAI

section

noncomputable section
open scoped BigOperators NNReal Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem scalarLogDensity_ramp_bounds (n : ℕ) (m v : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m)
    {f : ℝ → ℝ} (hf : BoundedDerivs f) (hspin : ScalarSpinConvex f)
    (u : ParameterSpace n) {B : ℝ} (hB : 0≤B)
    (hprefix : ∀ j, |scalarLevelField n v j u|≤B) (z : ParameterSpace n) :
    |fderiv ℝ (hierarchyPathLogDensity n m (fun z => f (scalarSpinField n v z))) z u|≤2*B ∧
    |fderiv ℝ (fderiv ℝ (hierarchyPathLogDensity n m (fun z => f (scalarSpinField n v z)))) z u u|≤2*B^2 := by
  let F : ParameterSpace n → ℝ := fun z => f (scalarSpinField n v z)
  let P := hierarchyPenalty n m 1 F
  let V := hierarchyPathLogDensity n m F
  have hF : BoundedDerivs F := hf.compCLM (scalarSpinField n v)
  have hP : BoundedDerivs P := hierarchyPenalty_boundedDerivs n m 1 F hF
  have hV : BoundedDerivs V := hierarchyPathLogDensity_regular n m hF
  have hw (j) : 0≤hierarchyAtom n m 1 j := hierarchyAtom_nonneg n m zero_le_one
    (fun i => (hm i).1) (fun i => (hm i).2) hmono j
  have hLv (j) := hierarchyLevel_boundedDerivs n m F hF j
  have he' : directionalGradient P u = fun z =>
      ∑ j, hierarchyAtom n m 1 j*directionalGradient (hierarchyLevel n m F j) u z := by
    funext z
    exact fderiv_hierarchyPenalty_apply n m 1 F hF z u
  have hd (j) := (directionalGradient_contDiff _ (hLv j).1 u).differentiable (by norm_num) z
  have H := HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ =>
    (hd j).hasFDerivAt.const_mul (hierarchyAtom n m 1 j))
  have hh : fderiv ℝ (fderiv ℝ P) z u u =
      ∑ j, hierarchyAtom n m 1 j*fderiv ℝ (fderiv ℝ (hierarchyLevel n m F j)) z u u := by
    have hh := congrArg (fun L : ParameterSpace n →L[ℝ] ℝ => L u) H.fderiv
    rw [← he',fderiv_directionalGradient _ hP.1] at hh
    simpa only [ContinuousLinearMap.flip_apply,sum_apply,smul_apply,smul_eq_mul,
      fderiv_directionalGradient _ (hLv _).1] using hh
  have hp₁ : |fderiv ℝ P z u|≤B := by
    change |directionalGradient P u z|≤B
    rw [he']
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ j, hierarchyAtom n m 1 j*B := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul,abs_of_nonneg (hw j)]
        exact mul_le_mul_of_nonneg_left
          ((hierarchyLevel_scalar_direction_bounds n m v hm hf hspin j z u).1.trans (hprefix j)) (hw j)
      _ = B := by rw [← Finset.sum_mul,hierarchyAtom_sum,one_mul]
  have hp₂ : |fderiv ℝ (fderiv ℝ P) z u u|≤B^2 := by
    rw [hh]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ j, hierarchyAtom n m 1 j*B^2 := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul,abs_of_nonneg (hw j)]
        apply mul_le_mul_of_nonneg_left _ (hw j)
        exact (hierarchyLevel_scalar_direction_bounds n m v hm hf hspin j z u).2.trans
          (by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).mpr (hprefix j))
      _ = B^2 := by rw [← Finset.sum_mul,hierarchyAtom_sum,one_mul]
  have ht := hierarchyLevel_scalar_direction_bounds n m v hm hf hspin (Fin.last n) z u
  rw [hierarchyLevel_last,scalarLevelField_last] at ht
  have htl : |scalarSpinField n v u|≤B := by simpa only [scalarLevelField_last] using hprefix (Fin.last n)
  have ht₁ : |fderiv ℝ F z u|≤B := ht.1.trans htl
  have ht₂ : |fderiv ℝ (fderiv ℝ F) z u u|≤B^2 := ht.2.trans
    (by simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hB).mpr htl)
  have hv₁ : fderiv ℝ V z u=fderiv ℝ F z u-fderiv ℝ P z u := by
    change fderiv ℝ (fun z => F z-P z) z u=_
    rw [fderiv_fun_sub (hF.1.differentiable (by norm_num) z) (hP.1.differentiable (by norm_num) z),sub_apply]
  have hv₂ : fderiv ℝ (fderiv ℝ V) z u u=fderiv ℝ (fderiv ℝ F) z u u-fderiv ℝ (fderiv ℝ P) z u u := by
    have he : fderiv ℝ V=fun z => fderiv ℝ F z-fderiv ℝ P z := by
      funext z
      exact fderiv_fun_sub (hF.1.differentiable (by norm_num) z) (hP.1.differentiable (by norm_num) z)
    rw [he,fderiv_fun_sub ((hF.1.fderiv_right (m:=1) (by norm_num)).differentiable (by norm_num) z)
      ((hP.1.fderiv_right (m:=1) (by norm_num)).differentiable (by norm_num) z),sub_apply,sub_apply]
  constructor
  · change |fderiv ℝ V z u|≤_
    rw [hv₁]
    exact (abs_sub _ _).trans (by linarith)
  · change |fderiv ℝ (fderiv ℝ V) z u u|≤_
    rw [hv₂]
    exact (abs_sub _ _).trans (by linarith)

theorem scalarPath_ramp_square_error (n : ℕ) (m v a : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m)
    {f : ℝ → ℝ} (hf : BoundedDerivs f) (hspin : ScalarSpinConvex f)
    {B : ℝ} (hB : 0≤B)
    (hprefix : ∀ j, |scalarLevelField n v j (coordinateVector n a)|≤B) (x : ℝ) :
    |(∫ z, (coordinateLinear n a z)^2 ∂hierarchyPathLaw n m (fun z => f (scalarSpinField n v z)) x)-
      (∑ i, (a i)^2)|≤4*B^2+2*B^2 := by
  let V := hierarchyPathLogDensity n m (fun z => f (scalarSpinField n v z))
  have hV : BoundedDerivs V := hierarchyPathLogDensity_regular n m (hf.compCLM (scalarSpinField n v))
  have H := fiberGaussian_tent_error_C1 n V (fun _ => 1) hV contDiff_const
    (HasExpGrowth.const 1) (by
      apply HasExpGrowth.of_bounded (C:=0) le_rfl
      intro z
      simp)
    x a (fun _ _ => rfl) (2*B) (2*B^2) (fun _ => by norm_num)
    (fun z => (scalarLogDensity_ramp_bounds n m v hm hmono hf hspin _ hB hprefix z).1)
    (fun z => (scalarLogDensity_ramp_bounds n m v hm hmono hf hspin _ hB hprefix z).2)
  have := fiberGaussian_tilted_probability n V hV x
  rw [hierarchyPathLaw_eq_tilted n m _ (hf.compCLM (scalarSpinField n v))]
  simpa only [mul_one,integral_const,probReal_univ,smul_eq_mul,one_mul,show (2*B)^2=4*B^2 by ring] using H

end SK.Analytic

end
end

end OAI

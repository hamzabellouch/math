import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.HierarchyProbability
import OAI.Probability.SKBarriers.Hierarchy.AverageMeanVariance
import OAI.Probability.SKBarriers.Calculus.CoordinatePrefix

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section SpinCovarianceVariation
variable {S : Type} [Fintype S] [Nonempty S]

omit [Nonempty S] in
theorem hierarchySpinMean_const_mul (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (c : S → ℝ) (a : ℝ) (j : Fin (n+1)) :
    hierarchySpinMean n m U (fun s => a*c s) j =
      fun z => a*hierarchySpinMean n m U c j z := by
  have he : affineMoment (fun _ => 0) U (fun s => a*c s) =
      fun z => a*affineMoment (fun _ => 0) U c z := by
    funext z
    simp only [affineMoment,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _
    ring
  simp only [hierarchySpinMean,he,hierarchyMomentLevel_const_mul]

theorem hierarchyLevel_coordinate_gradient (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (c : S → ℝ) (a : ℝ) (i : Fin n)
    (hU : ∀ s, U s (coordinateAxis n i) = a*c s) (j : Fin (n+1)) (z : ParameterSpace n) :
    fderiv ℝ (hierarchyLevel n m (affineLogPartition (fun _ => 0) U) j) z (coordinateAxis n i) =
      if i.val < j.val then a*hierarchySpinMean n m U c j z else 0 := by
  split_ifs with h
  · have H := congrFun (hierarchyLevel_spinMean n m U (fun s => a*c s) j
      (coordinateAxis n i) (tailZero_coordinateAxis n i j h) hU) z
    rw [hierarchySpinMean_const_mul] at H
    exact H
  · exact (hierarchyLevel_invariant_of_prefix n m _ _ j
      (prefixZero_coordinateAxis n i j (Nat.le_of_not_gt h))).fderiv_zero
        ((hierarchyLevel_boundedDerivs n m _ (affineLogPartition_boundedDerivs (fun _ => 0) U) j).1.differentiable
          (by norm_num)) z

variable [MeasurableSpace S] [MeasurableSingletonClass S]

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem hierarchyPotential_coordinate_gradient (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (c : S → ℝ) (a : ℝ) (i : Fin n)
    (hU : ∀ s, U s (coordinateAxis n i) = a*c s) (s : S) (z : ParameterSpace n) :
    fderiv ℝ (hierarchyPotential n m U s) z (coordinateAxis n i) =
      a*c s-∑ j : Fin (n+1), if i.val < j.val then
        hierarchyAtom n m 1 j*(a*hierarchySpinMean n m U c j z) else 0 := by
  have hf := affineLogPartition_boundedDerivs (fun _ => 0) U
  have hp := hierarchyPenalty_boundedDerivs n m 1 _ hf
  change fderiv ℝ (fun z => U s z-hierarchyPenalty n m 1 (affineLogPartition (fun _ => 0) U) z) z _ = _
  rw [fderiv_fun_sub (U s).differentiableAt (hp.1.differentiable (by norm_num) z)]
  simp only [sub_apply,ContinuousLinearMap.fderiv,hU]
  rw [fderiv_hierarchyPenalty_apply n m 1 _ hf]
  simp_rw [hierarchyLevel_coordinate_gradient n m U c a i hU]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp only [mul_zero]

theorem hierarchyGaussian_coordinate_spin (n : ℕ) (m : Fin n → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (c : S → ℝ) (a : ℝ) (i : Fin n)
    (hU : ∀ s, U s (coordinateAxis n i) = a*c s) (hc : ∀ s, ‖c s‖ ≤ 1)
    (hsq : ∀ s, (c s)^2 = 1) :
    (∫ sz, c sz.1*coordinateProjection n i sz.2 ∂hierarchyGaussianLaw n m U) =
      a*(1-∑ j : Fin (n+1), if i.val < j.val then hierarchyAtom n m 1 j *
        (∫ z, (hierarchySpinMean n m U c j z)^2
          ∂hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0) else 0) := by
  let μ := hierarchyGaussianLaw n m U
  let := hierarchyGaussian_probability n m U
  have hr (j : Fin (n+1)) := hierarchySpinMean_regular n m U c (by norm_num : (0:ℝ) ≤ 1) hc j
  have hI (j : Fin (n+1)) : Integrable (fun sz => c sz.1*hierarchySpinMean n m U c j sz.2) μ := by
    change Integrable (fun sz => c sz.1*hierarchySpinMean n m U c j sz.2) (hierarchyGaussianLaw n m U)
    apply hierarchyGaussian_integrable n m U (fun s z => c s*hierarchySpinMean n m U c j z)
    · intro s
      exact (HasExpGrowth.const (c s)).mul (HasExpGrowth.of_bounded (by norm_num) (hr j).2)
    · intro s
      exact continuous_const.mul (hr j).1
  have H := spinGaussian_weighted_stein n (hierarchyPotential n m U) (fun s _ => c s)
    (hierarchyPotential_boundedDerivs n m U) (fun _ => contDiff_const)
    (fun s => HasExpGrowth.const (c s)) (fun s => by
      have he : fderiv ℝ (fun _ : ParameterSpace n => c s) = fun _ => 0 := by funext z; exact fderiv_const_apply _
      rw [he]
      exact HasExpGrowth.const (0 : ParameterSpace n →L[ℝ] ℝ)) i
  rw [← hierarchyGaussianLaw_eq_spinGaussian] at H
  simp only [fderiv_const_apply,zero_apply,integral_zero,zero_add] at H
  have he (sz : S × ParameterSpace n) :
      c sz.1*fderiv ℝ (hierarchyPotential n m U sz.1) sz.2 (coordinateAxis n i) =
        a-∑ j : Fin (n+1), if i.val < j.val then
          a*(hierarchyAtom n m 1 j*(c sz.1*hierarchySpinMean n m U c j sz.2)) else 0 := by
    rw [hierarchyPotential_coordinate_gradient n m U c a i hU,mul_sub,Finset.mul_sum]
    have hc2 : c sz.1*(a*c sz.1) = a := by
      calc
        _ = a*(c sz.1)^2 := by ring
        _ = a := by rw [hsq sz.1,mul_one]
    rw [hc2]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  have hJ (j : Fin (n+1)) : Integrable (fun sz : S × ParameterSpace n =>
      if i.val < j.val then a*(hierarchyAtom n m 1 j*(c sz.1*hierarchySpinMean n m U c j sz.2)) else 0) μ := by
    by_cases h : i.val < j.val
    · simpa only [ite_eq_left h] using ((hI j).const_mul (hierarchyAtom n m 1 j)).const_mul a
    · simp only [ite_eq_right h]; exact integrable_const 0
  calc
    _ = ∫ sz, coordinateProjection n i sz.2*c sz.1 ∂μ := by congr 1; funext sz; ring
    _ = ∫ sz, a-∑ j : Fin (n+1), if i.val < j.val then
        a*(hierarchyAtom n m 1 j*(c sz.1*hierarchySpinMean n m U c j sz.2)) else 0 ∂μ :=
      H.trans (integral_congr_ae (ae_of_all _ he))
    _ = a-∑ j : Fin (n+1), if i.val < j.val then
        a*(hierarchyAtom n m 1 j*(∫ z, (hierarchySpinMean n m U c j z)^2
          ∂hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0)) else 0 := by
      rw [integral_sub (integrable_const _) (integrable_finsetSum _ (fun j _ => hJ j)),
        integral_finsetSum _ (fun j _ => hJ j),integral_const]
      simp only [probReal_univ,one_smul]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : i.val < j.val
      · simp only [ite_eq_left h,integral_const_mul]
        rw [hierarchySpinMean_terminal_product n m U c (by norm_num) hc j]
      · simp only [ite_eq_right h,integral_zero]
    _ = _ := by
      rw [mul_sub,mul_one,Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> ring
end SpinCovarianceVariation
end SK.Analytic

end
end

end

end OAI

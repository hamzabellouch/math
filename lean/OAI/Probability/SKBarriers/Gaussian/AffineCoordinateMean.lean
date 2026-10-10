import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.HierarchyProjectedCovariance

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section
variable {S : Type} [Fintype S] [Nonempty S]

theorem affineHierarchy_coordinate_mean (n : ℕ) (m : Fin n → ℝ)
    (c : S → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ) (g : S → ℝ)
    (a : ℝ) (i : Fin n) (hU : ∀ s,U s (coordinateAxis n i)=a*g s) (x : ℝ) :
    (∫ z, coordinateProjection n i z ∂hierarchyPathLaw n m (affineLogPartition c U) x)=
      a*m i*(∫ z, affineMoment c U g z ∂hierarchyPathLaw n m (affineLogPartition c U) x) := by
  classical
  let f := affineLogPartition c U
  let G := affineMoment c U g
  let M := hierarchyMomentLevel n m f G
  let μ := hierarchyPathLaw n m f x
  have hf := affineLogPartition_boundedDerivs c U
  let : IsProbabilityMeasure μ := hierarchyPathLaw_probability n m f hf x
  let B := ∑ s, ‖g s‖
  have hB : 0≤B := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hb : ∀ s, ‖g s‖≤B := fun s => Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ s)
  have hcG := affineMoment_continuous c U g
  have hbG := affineMoment_norm_le c U g hb
  have hM (k) := hierarchyMomentLevel_bounded_continuous n m f G hf hcG hB hbG k
  have hiG : Integrable G μ := hierarchyPathLaw_integrable n m f G hf hcG hbG x
  have hmean (k : Fin (n+1)) : (∫ z, M k z ∂μ)=∫ z, G z ∂μ := by
    rw [← hierarchyAverage_eq_integral n m f hf (M k) (hM k).1 hB (hM k).2,
      ← hierarchyAverage_eq_integral n m f hf G hcG hB hbG]
    exact hierarchyAverage_momentLevel n m f G hf k x
  have hdConst : HasExpGrowth (fderiv ℝ (fun _ : ParameterSpace n => (1:ℝ))) := by
    have he : fderiv ℝ (fun _ : ParameterSpace n => (1:ℝ)) = fun _ => 0 := funext (fun _ => fderiv_const_apply 1)
    rw [he]
    exact HasExpGrowth.const 0
  have H := fiberGaussian_tilted_weighted_stein n (hierarchyPathLogDensity n m f)
    (fun _ => (1:ℝ)) (hierarchyPathLogDensity_regular n m hf) contDiff_const
    (HasExpGrowth.const 1) hdConst x i
  rw [← hierarchyPathLaw_eq_tilted n m f hf x] at H
  simp only [mul_one,one_mul,fderiv_const_apply,zero_apply,integral_zero,zero_add] at H
  have hJ (k : Fin (n+1)) : Integrable (fun z =>
      if i.val<k.val then hierarchyAtom n m 1 k*M k z else 0) μ := by
    by_cases hik : i.val<k.val
    · simp only [ite_eq_left hik]
      exact (hierarchyPathLaw_integrable n m f (M k) hf (hM k).1 (hM k).2 x).const_mul _
    · simp only [ite_eq_right hik]; exact integrable_const 0
  have he (z) : fderiv ℝ (hierarchyPathLogDensity n m f) z (coordinateAxis n i)=
      a*(G z-∑ k : Fin (n+1), if i.val<k.val then hierarchyAtom n m 1 k*M k z else 0) :=
    affineHierarchy_score_coordinate n m c U g a i hU z
  have hsum : (∑ k : Fin (n+1), ∫ z, (if i.val<k.val then hierarchyAtom n m 1 k*M k z else 0) ∂μ)=
      (1-m i)*(∫ z, G z ∂μ) := by
    rw [← hierarchyAtom_tail_sum n m 1 i,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hik : i.val<k.val
    · simp only [ite_eq_left hik,integral_const_mul,hmean]
    · simp only [ite_eq_right hik,integral_zero,zero_mul]
  calc
    _ = ∫ z, fderiv ℝ (hierarchyPathLogDensity n m f) z (coordinateAxis n i) ∂μ := H
    _ = a*((∫ z, G z ∂μ)-(1-m i)*(∫ z, G z ∂μ)) := by
      rw [integral_congr_ae (ae_of_all _ he),integral_const_mul,
        integral_sub hiG (integrable_finsetSum _ (fun k _ => hJ k)),
        integral_finsetSum _ (fun k _ => hJ k),hsum]
    _ = _ := by ring

end

end SK.Analytic

end
end

end OAI

import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.HierarchyPrefix
import OAI.Probability.SKBarriers.Hierarchy.HierarchyProbability
import OAI.Probability.SKBarriers.Gaussian.AffineMomentCalculus

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem hierarchyPathLaw_integral_tilt (n : ℕ) (m : Fin n → ℝ)
    (f : ParameterSpace n → ℝ) (hf : BoundedDerivs f) (x : ℝ)
    (g : ParameterSpace n → ℝ) :
    (∫ z, g z ∂hierarchyPathLaw n m f x) =
      ∫ z, g z ∂(fiberGaussian n x).tilted (fun z => f z-hierarchyPenalty n m 1 f z) := by
  rw [integral_tilted_real_eq_div]
  have he : (fun z => Real.exp (f z-hierarchyPenalty n m 1 f z)) = hierarchyPathWeight n m f := by
    funext z
    simpa only [one_mul] using (hierarchyPathWeight_eq n m f 1 z).symm
  rw [he,(hierarchyPathWeight_normalized n m f hf x).2,div_one,hierarchyPathLaw_integral n m f hf]
  congr 1
  funext z
  rw [show Real.exp (f z-hierarchyPenalty n m 1 f z) = hierarchyPathWeight n m f z from congrFun he z]
  ring

section
variable {S : Type} [Fintype S] [Nonempty S]

theorem hierarchyLevel_affine_coordinate (n : ℕ) (m : Fin n → ℝ)
    (c : S → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ) (g : S → ℝ)
    (a : ℝ) (i : Fin n) (hU : ∀ s, U s (coordinateAxis n i) = a*g s)
    (j : Fin (n+1)) (z : ParameterSpace n) :
    fderiv ℝ (hierarchyLevel n m (affineLogPartition c U) j) z (coordinateAxis n i) =
      if i.val < j.val then a*hierarchyMomentLevel n m (affineLogPartition c U) (affineMoment c U g) j z else 0 := by
  have hf := affineLogPartition_boundedDerivs c U
  split_ifs with h
  · rw [hierarchyLevel_gradient n m _ hf j _ z (tailZero_coordinateAxis n i j h)]
    have he : directionalGradient (affineLogPartition c U) (coordinateAxis n i) =
        fun z => a*affineMoment c U g z := by
      funext z
      simp only [directionalGradient,fderiv_affineLogPartition_apply,hU,affineMoment_const_mul]
    rw [he,hierarchyMomentLevel_const_mul]
  · exact (hierarchyLevel_invariant_of_prefix n m _ _ j
      (prefixZero_coordinateAxis n i j (Nat.le_of_not_gt h))).fderiv_zero
        ((hierarchyLevel_boundedDerivs n m _ hf j).1.differentiable (by norm_num)) z

theorem weightedHierarchy_coordinate_covariance (n : ℕ) (m : Fin n → ℝ)
    (c : S → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ) (g : S → ℝ)
    (a : ℝ) (i : Fin n) (hU : ∀ s, U s (coordinateAxis n i) = a*g s) :
    (∫ z, coordinateProjection n i z*affineMoment c U g z
      ∂hierarchyPathLaw n m (affineLogPartition c U) 0) =
      a*((∫ z, affineMoment c U (fun s => (g s)^2) z
        ∂hierarchyPathLaw n m (affineLogPartition c U) 0)-
        ∑ j : Fin (n+1), if i.val < j.val then hierarchyAtom n m 1 j *
          (∫ z, (hierarchyMomentLevel n m (affineLogPartition c U) (affineMoment c U g) j z)^2
            ∂hierarchyPathLaw n m (affineLogPartition c U) 0) else 0) := by
  classical
  let f := affineLogPartition c U
  let G := affineMoment c U g
  let A := hierarchyMomentLevel n m f G
  let μ := hierarchyPathLaw n m f 0
  let V (z : ParameterSpace n) := f z-hierarchyPenalty n m 1 f z
  have hf := affineLogPartition_boundedDerivs c U
  let : IsProbabilityMeasure μ := hierarchyPathLaw_probability n m f hf 0
  have hp := hierarchyPenalty_boundedDerivs n m 1 f hf
  have hV : BoundedDerivs V := by
    convert hf.add (hp.const_mul (-1)) using 1
    funext z
    dsimp [V]
    ring
  let B := ∑ s, ‖g s‖
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hb : ∀ s, ‖g s‖ ≤ B := fun s => Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ s)
  have hG := affineMoment_contDiff c U g
  have hGb := affineMoment_norm_le c U g hb
  obtain ⟨C,hC,hC'⟩ := affineMoment_fderiv_bounded c U g
  have H := fiberGaussian_tilted_weighted_stein n V G hV hG
    (HasExpGrowth.of_bounded hB hGb) (HasExpGrowth.of_bounded hC hC') 0 i
  dsimp only [V] at H
  simp_rw [← hierarchyPathLaw_integral_tilt n m f hf 0] at H
  have hA (j : Fin (n+1)) := hierarchyMomentLevel_bounded_continuous n m f G hf hG.continuous hB hGb j
  have hi (j : Fin (n+1)) : Integrable (fun z => G z*A j z) μ :=
    hierarchyPathLaw_integrable n m f _ hf (hG.continuous.mul (hA j).1)
      (fun z => by simp only [Pi.mul_apply,norm_mul]; exact mul_le_mul (hGb z) ((hA j).2 z) (norm_nonneg _) hB) 0
  have hi2 : Integrable (fun z => affineMoment c U (fun s => (g s)^2) z) μ :=
    hierarchyPathLaw_integrable n m f _ hf (affineMoment_continuous _ _ _)
      (affineMoment_norm_le c U _ (fun s => by
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (hb s) 2)) 0
  have hprod (j : Fin (n+1)) :
      (∫ z, G z*A j z ∂μ) = ∫ z, (A j z)^2 ∂μ := by
    have H := hierarchyPathLaw_fixed_mul n m f G (A j) hf hG.continuous (hA j).1 hB hB
      hGb (hA j).2 j (hierarchyMomentLevel_retained n m f G hf j j le_rfl) 0
    calc
      _ = ∫ z, A j z*G z ∂μ := by congr 1; funext z; ring
      _ = _ := H.trans (by congr 1; funext z; change A j z*A j z = _; ring)
  have hdG (z) : fderiv ℝ G z (coordinateAxis n i) =
      a*(affineMoment c U (fun s => (g s)^2) z-(G z)^2) := by
    rw [fderiv_affineMoment_apply]
    simp only [hU]
    have he : (fun s => g s*(a*g s)) = fun s => a*(g s)^2 := by funext s; ring
    rw [he,affineMoment_const_mul,affineMoment_const_mul]
    dsimp [G]
    ring
  have hdV (z) : fderiv ℝ V z (coordinateAxis n i) = a*G z-
      ∑ j : Fin (n+1), if i.val < j.val then hierarchyAtom n m 1 j*(a*A j z) else 0 := by
    rw [show V = fun z => f z-hierarchyPenalty n m 1 f z from rfl,
      fderiv_fun_sub (hf.1.differentiable (by norm_num) z) (hp.1.differentiable (by norm_num) z)]
    simp only [sub_apply]
    rw [fderiv_affineLogPartition_apply]
    simp only [hU,affineMoment_const_mul]
    rw [fderiv_hierarchyPenalty_apply n m 1 f hf]
    dsimp only [f]
    simp_rw [hierarchyLevel_affine_coordinate n m c U g a i hU]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp [A,G,f]
  have hI1 : Integrable (fun z => fderiv ℝ G z (coordinateAxis n i)) μ := by
    apply hierarchyPathLaw_integrable n m f _ hf
      ((hG.continuous_fderiv (by norm_num)).clm_apply continuous_const)
    intro z
    exact ((fderiv ℝ G z).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hC' z) (norm_nonneg _))
  have hI2 : Integrable (fun z => G z*fderiv ℝ V z (coordinateAxis n i)) μ := by
    obtain ⟨hVc,D,E,hD,_,hbV,_⟩ := hV
    apply hierarchyPathLaw_integrable n m f _ hf
      (hG.continuous.mul ((hVc.continuous_fderiv (by norm_num)).clm_apply continuous_const))
      (C:=B*(D*‖coordinateAxis n i‖))
    intro z
    simp only [Pi.mul_apply,norm_mul]
    exact mul_le_mul (hGb z)
      (((fderiv ℝ V z).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hbV z) (norm_nonneg _)))
      (norm_nonneg _) hB
  have hJ (j : Fin (n+1)) : Integrable (fun z =>
      if i.val < j.val then hierarchyAtom n m 1 j*(G z*A j z) else 0) μ := by
    by_cases h : i.val < j.val
    · simpa only [ite_eq_left h] using (hi j).const_mul (hierarchyAtom n m 1 j)
    · simp only [ite_eq_right h]; exact integrable_const 0
  change (∫ z, coordinateProjection n i z*G z ∂μ) = _ at H ⊢
  rw [H,← integral_add hI1 hI2]
  have he (z) : fderiv ℝ G z (coordinateAxis n i)+G z*fderiv ℝ V z (coordinateAxis n i) =
      a*(affineMoment c U (fun s => (g s)^2) z-
        ∑ j : Fin (n+1), if i.val < j.val then hierarchyAtom n m 1 j*(G z*A j z) else 0) := by
    rw [hdG,hdV]
    simp only [mul_sub,Finset.mul_sum]
    have he : (∑ j : Fin (n+1), G z*(if i.val < j.val then hierarchyAtom n m 1 j*(a*A j z) else 0)) =
        ∑ j : Fin (n+1), a*(if i.val < j.val then hierarchyAtom n m 1 j*(G z*A j z) else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> ring
    rw [he]
    ring
  rw [integral_congr_ae (ae_of_all _ he),integral_const_mul,
    integral_sub hi2 (integrable_finsetSum _ (fun j _ => hJ j)),integral_finsetSum _ (fun j _ => hJ j)]
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : i.val < j.val
  · simp only [ite_eq_left h,integral_const_mul,hprod]
    rfl
  · simp only [ite_eq_right h,integral_zero]

end
end SK.Analytic

end
end

end OAI

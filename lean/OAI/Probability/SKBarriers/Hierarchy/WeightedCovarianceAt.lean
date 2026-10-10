import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.WeightedHierarchyCovariance

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section
variable {S : Type} [Fintype S] [Nonempty S]

theorem weightedHierarchy_coordinate_covariance_at (n : ℕ) (m : Fin n → ℝ)
    (c : S → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ) (g : S → ℝ)
    (a : ℝ) (i : Fin n) (hU : ∀ s, U s (coordinateAxis n i) = a*g s) (x : ℝ) :
    (∫ z, coordinateProjection n i z*affineMoment c U g z
      ∂hierarchyPathLaw n m (affineLogPartition c U) x) =
      a*((∫ z, affineMoment c U (fun s => (g s)^2) z
        ∂hierarchyPathLaw n m (affineLogPartition c U) x)-
        ∑ j : Fin (n+1), if i.val < j.val then hierarchyAtom n m 1 j *
          (∫ z, (hierarchyMomentLevel n m (affineLogPartition c U) (affineMoment c U g) j z)^2
            ∂hierarchyPathLaw n m (affineLogPartition c U) x) else 0) := by
  classical
  let f := affineLogPartition c U
  let G := affineMoment c U g
  let A := hierarchyMomentLevel n m f G
  let μ := hierarchyPathLaw n m f x
  let V (z : ParameterSpace n) := f z-hierarchyPenalty n m 1 f z
  have hf := affineLogPartition_boundedDerivs c U
  let : IsProbabilityMeasure μ := hierarchyPathLaw_probability n m f hf x
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
    (HasExpGrowth.of_bounded hB hGb) (HasExpGrowth.of_bounded hC hC') x i
  dsimp only [V] at H
  simp_rw [← hierarchyPathLaw_integral_tilt n m f hf x] at H
  have hA (j : Fin (n+1)) := hierarchyMomentLevel_bounded_continuous n m f G hf hG.continuous hB hGb j
  have hi (j : Fin (n+1)) : Integrable (fun z => G z*A j z) μ :=
    hierarchyPathLaw_integrable n m f _ hf (hG.continuous.mul (hA j).1)
      (fun z => by simp only [Pi.mul_apply,norm_mul]; exact mul_le_mul (hGb z) ((hA j).2 z) (norm_nonneg _) hB) x
  have hi2 : Integrable (fun z => affineMoment c U (fun s => (g s)^2) z) μ :=
    hierarchyPathLaw_integrable n m f _ hf (affineMoment_continuous _ _ _)
      (affineMoment_norm_le c U _ (fun s => by
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (hb s) 2)) x
  have hprod (j : Fin (n+1)) :
      (∫ z, G z*A j z ∂μ) = ∫ z, (A j z)^2 ∂μ := by
    have H := hierarchyPathLaw_fixed_mul n m f G (A j) hf hG.continuous (hA j).1 hB hB
      hGb (hA j).2 j (hierarchyMomentLevel_retained n m f G hf j j le_rfl) x
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

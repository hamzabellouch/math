import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.HierarchyMassPrefix
import OAI.Probability.SKBarriers.Hierarchy.HierarchySandwich

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem hierarchyAtom_tail_sum (n : ℕ) (m : Fin n → ℝ) (c : ℝ) (i : Fin n) :
    (∑ j : Fin (n+1), if i.val < j.val then hierarchyAtom n m c j else 0)=c-m i := by
  have H := massFromAtoms_hierarchyAtom n m c i
  have he : (∑ j : Fin (n+1), if i.val < j.val then hierarchyAtom n m c j else 0)+
      massFromAtoms n (hierarchyAtom n m c) i=c := by
    rw [massFromAtoms,← Finset.sum_add_distrib]
    convert hierarchyAtom_sum n m c using 1
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i.val < j.val <;> simp [hij,show (j.val ≤ i.val) ↔ ¬i.val < j.val by omega]
  rw [H] at he
  linarith

section
variable {S : Type} [Fintype S] [Nonempty S]

theorem affineHierarchy_score_coordinate (n : ℕ) (m : Fin n → ℝ)
    (c : S → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ) (g : S → ℝ)
    (a : ℝ) (i : Fin n) (hU : ∀ s, U s (coordinateAxis n i)=a*g s) (z : ParameterSpace n) :
    fderiv ℝ (hierarchyPathLogDensity n m (affineLogPartition c U)) z (coordinateAxis n i)=
      a*(affineMoment c U g z-∑ j : Fin (n+1), if i.val < j.val then hierarchyAtom n m 1 j*
        hierarchyMomentLevel n m (affineLogPartition c U) (affineMoment c U g) j z else 0) := by
  have hf := affineLogPartition_boundedDerivs c U
  have hp := hierarchyPenalty_boundedDerivs n m 1 (affineLogPartition c U) hf
  change fderiv ℝ (fun z => affineLogPartition c U z-hierarchyPenalty n m 1 (affineLogPartition c U) z) z (coordinateAxis n i)=_
  rw [fderiv_fun_sub (hf.1.differentiable (by norm_num) z)
    (hp.1.differentiable (by norm_num) z),sub_apply,fderiv_affineLogPartition_apply]
  simp only [hU,affineMoment_const_mul]
  rw [fderiv_hierarchyPenalty_apply n m 1 _ hf]
  simp_rw [hierarchyLevel_affine_coordinate n m c U g a i hU]
  rw [mul_sub,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> ring

theorem affineHierarchyMoment_directional (n : ℕ) (m : Fin n → ℝ)
    (c : S → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ) (g : S → ℝ)
    (j : Fin (n+1)) (u : ParameterSpace n) (hu : TailZero n j u) (hU : ∀ s, U s u=g s) :
    hierarchyMomentLevel n m (affineLogPartition c U) (affineMoment c U g) j=
      directionalGradient (hierarchyLevel n m (affineLogPartition c U) j) u := by
  funext z
  rw [directionalGradient,hierarchyLevel_gradient n m _ (affineLogPartition_boundedDerivs c U) j u z hu]
  congr 2
  funext z
  simp only [directionalGradient,fderiv_affineLogPartition_apply,hU]

theorem affineHierarchyMoment_regular (n : ℕ) (m : Fin n → ℝ)
    (c : S → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ) (g : S → ℝ)
    (j : Fin (n+1)) (u : ParameterSpace n) (hu : TailZero n j u) (hU : ∀ s, U s u=g s) :
    ContDiff ℝ 1 (hierarchyMomentLevel n m (affineLogPartition c U) (affineMoment c U g) j) ∧
      HasExpGrowth (fderiv ℝ (hierarchyMomentLevel n m (affineLogPartition c U) (affineMoment c U g) j)) := by
  rw [affineHierarchyMoment_directional n m c U g j u hu hU]
  have hf := hierarchyLevel_boundedDerivs n m _ (affineLogPartition_boundedDerivs c U) j
  exact ⟨directionalGradient_contDiff _ hf.1 u,(hf.directionalGradient_bounds u).2⟩

theorem affineHierarchy_future_coordinate_moment (n : ℕ) (m : Fin n → ℝ)
    (c : S → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ) (g : S → ℝ)
    (a : ℝ) (i : Fin n) (hU : ∀ s, U s (coordinateAxis n i)=a*g s)
    (j : Fin (n+1)) (hji : j.val ≤ i.val)
    (u : ParameterSpace n) (hu : TailZero n j u) (hUr : ∀ s, U s u=g s) (x : ℝ) :
    (∫ z, coordinateProjection n i z*hierarchyMomentLevel n m (affineLogPartition c U)
      (affineMoment c U g) j z ∂hierarchyPathLaw n m (affineLogPartition c U) x)=
      a*m i*∫ z, (hierarchyMomentLevel n m (affineLogPartition c U) (affineMoment c U g) j z)^2
        ∂hierarchyPathLaw n m (affineLogPartition c U) x := by
  classical
  let f := affineLogPartition c U
  let G := affineMoment c U g
  let M := hierarchyMomentLevel n m f G
  let μ := hierarchyPathLaw n m f x
  have hf := affineLogPartition_boundedDerivs c U
  let : IsProbabilityMeasure μ := hierarchyPathLaw_probability n m f hf x
  have hV := hierarchyPathLogDensity_regular n m hf
  have hreg := affineHierarchyMoment_regular n m c U g j u hu hUr
  let B := ∑ s, ‖g s‖
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hb : ∀ s, ‖g s‖ ≤ B := fun s => Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ s)
  have hcG := affineMoment_continuous c U g
  have hbG := affineMoment_norm_le c U g hb
  have hM (k) := hierarchyMomentLevel_bounded_continuous n m f G hf hcG hB hbG k
  have hMG (k) : HasExpGrowth (M k) := HasExpGrowth.of_bounded hB (hM k).2
  have hprod (k : Fin (n+1)) (hjk : j ≤ k) :
      (∫ z, M j z*M k z ∂μ)=∫ z, (M j z)^2 ∂μ := by
    have H := hierarchyPathLaw_fixed_mul n m f (M k) (M j) hf (hM k).1 (hM j).1 hB hB
      (hM k).2 (hM j).2 j (hierarchyMomentLevel_retained n m f G hf j j le_rfl) x
    rw [hierarchyMomentLevel_tower n m f G hf j k hjk] at H
    exact H.trans (by congr 1; funext z; ring)
  have hlast : M (Fin.last n)=G := by
    cases n with
    | zero => rfl
    | succ n => simp only [M,hierarchyMomentLevel,Fin.lastCases_last]
  have hd (z) : fderiv ℝ (M j) z (coordinateAxis n i)=0 := by
    have he := affineHierarchyMoment_directional n m c U g j u hu hUr
    have hi := hierarchyLevel_invariant_of_prefix n m f (coordinateAxis n i) j (prefixZero_coordinateAxis n i j hji)
    rw [show M j=directionalGradient (hierarchyLevel n m f j) u from he]
    exact (hi.directionalGradient u).fderiv_zero
      ((directionalGradient_contDiff _ (hierarchyLevel_boundedDerivs n m f hf j).1 u).differentiable (by norm_num)) z
  have H := fiberGaussian_tilted_weighted_stein n (hierarchyPathLogDensity n m f) (M j) hV hreg.1
    (hMG j) hreg.2 x i
  rw [← hierarchyPathLaw_eq_tilted n m f hf x] at H
  rw [H]
  simp only [hd,integral_zero,zero_add]
  have hJ (k : Fin (n+1)) : Integrable (fun z =>
      if i.val < k.val then hierarchyAtom n m 1 k*(M j z*M k z) else 0) μ := by
    by_cases hik : i.val < k.val
    · simp only [ite_eq_left hik]
      exact (((hMG j).mul (hMG k)).integrable_hierarchyPathLaw n m hf ((hM j).1.mul (hM k).1) x).const_mul _
    · simp only [ite_eq_right hik]; exact integrable_const 0
  have hiG : Integrable (fun z => M j z*G z) μ :=
    ((hMG j).mul (HasExpGrowth.of_bounded hB hbG)).integrable_hierarchyPathLaw n m hf ((hM j).1.mul hcG) x
  have he (z) : M j z*fderiv ℝ (hierarchyPathLogDensity n m f) z (coordinateAxis n i)=
      a*(M j z*G z-∑ k : Fin (n+1), if i.val < k.val then hierarchyAtom n m 1 k*(M j z*M k z) else 0) := by
    rw [affineHierarchy_score_coordinate n m c U g a i hU]
    simp only [mul_sub,Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro k _
      split_ifs <;> ring
  rw [integral_congr_ae (ae_of_all _ he),integral_const_mul,integral_sub hiG
    (integrable_finsetSum _ (fun k _ => hJ k)),integral_finsetSum _ (fun k _ => hJ k)]
  rw [← hlast,hprod (Fin.last n) (Fin.le_last j)]
  have heS : (∑ k : Fin (n+1), ∫ z, (if i.val < k.val then hierarchyAtom n m 1 k*(M j z*M k z) else 0) ∂μ)=
      (1-m i)*(∫ z, (M j z)^2 ∂μ) := by
    rw [← hierarchyAtom_tail_sum n m 1 i,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hik : i.val < k.val
    · simp only [ite_eq_left hik,integral_const_mul,hprod k (show j≤k from by exact le_of_lt (show j<k from by change j.val<k.val; omega))]
    · simp only [ite_eq_right hik,integral_zero,zero_mul]
  rw [heS]
  ring

end

end SK.Analytic

end
end

end OAI

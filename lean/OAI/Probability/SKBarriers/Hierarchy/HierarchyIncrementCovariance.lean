import Mathlib
import OAI.Probability.SKBarriers.Gaussian.ExponentialPrefix
import OAI.Probability.SKBarriers.Hierarchy.HierarchyProjectedCovariance
import OAI.Probability.SKBarriers.Hierarchy.WeightedCovarianceAt

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section
variable {S : Type} [Fintype S] [Nonempty S]

def affineHierarchyResponse (n : ℕ) (m : Fin n → ℝ) (c : S → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (g : S → ℝ) (i : Fin n) (x : ℝ) : ℝ :=
  (∫ z, affineMoment c U (fun s => (g s)^2) z ∂hierarchyPathLaw n m (affineLogPartition c U) x)-
    ∑ k : Fin (n+1), if i.val < k.val then hierarchyAtom n m 1 k*
      (∫ z, (hierarchyMomentLevel n m (affineLogPartition c U) (affineMoment c U g) k z)^2
        ∂hierarchyPathLaw n m (affineLogPartition c U) x) else 0

theorem affineHierarchy_increment_covariance (n : ℕ) (m : Fin n → ℝ)
    (c : S → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ) (g : S → ℝ)
    (a : Fin n → ℝ) (hU : ∀ s i, U s (coordinateAxis n i)=a i*g s)
    (i j : Fin n) (hij : i ≤ j) (x : ℝ) :
    (∫ z, coordinateProjection n i z*coordinateProjection n j z
      ∂hierarchyPathLaw n m (affineLogPartition c U) x)=
      (if i=j then 1 else 0)+a i*a j*m j*affineHierarchyResponse n m c U g i x := by
  classical
  let f := affineLogPartition c U
  let G := affineMoment c U g
  let M := hierarchyMomentLevel n m f G
  let μ := hierarchyPathLaw n m f x
  have hf := affineLogPartition_boundedDerivs c U
  let : IsProbabilityMeasure μ := hierarchyPathLaw_probability n m f hf x
  have hV := hierarchyPathLogDensity_regular n m hf
  let B := ∑ s, ‖g s‖
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hb : ∀ s, ‖g s‖ ≤ B := fun s => Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ s)
  have hcG := affineMoment_continuous c U g
  have hbG := affineMoment_norm_le c U g hb
  have hM (k) := hierarchyMomentLevel_bounded_continuous n m f G hf hcG hB hbG k
  let L := coordinateProjection n i
  have hL := HasExpGrowth.linear L
  have hMG (k) : HasExpGrowth (M k) := HasExpGrowth.of_bounded hB (hM k).2
  have hprod (k : Fin (n+1)) (hik : i.val < k.val) :
      (∫ z, L z*M k z ∂μ)=∫ z, L z*G z ∂μ := by
    exact (hierarchyPathLaw_fixed_mul_exp n m hf hcG L.continuous
      (HasExpGrowth.of_bounded hB hbG) hL k (hierarchyMomentLevel_coordinate_fixed n m hf i k hik) x).symm
  have hdL : HasExpGrowth (fderiv ℝ (L : ParameterSpace n → ℝ)) := by
    have he : fderiv ℝ (L : ParameterSpace n → ℝ) = fun _ => L := funext (fun _ => L.fderiv)
    rw [he]
    exact HasExpGrowth.const L
  have H := fiberGaussian_tilted_weighted_stein n (hierarchyPathLogDensity n m f) L hV L.contDiff hL hdL x j
  rw [← hierarchyPathLaw_eq_tilted n m f hf x] at H
  simp only [L.fderiv,L,coordinateProjection_coordinateAxis] at H
  have hiG : Integrable (fun z => L z*G z) μ :=
    (hL.mul (HasExpGrowth.of_bounded hB hbG)).integrable_hierarchyPathLaw n m hf (L.continuous.mul hcG) x
  have hJ (k : Fin (n+1)) : Integrable (fun z =>
      if j.val < k.val then hierarchyAtom n m 1 k*(L z*M k z) else 0) μ := by
    by_cases hjk : j.val < k.val
    · simp only [ite_eq_left hjk]
      exact ((hL.mul (hMG k)).integrable_hierarchyPathLaw n m hf (L.continuous.mul (hM k).1) x).const_mul _
    · simp only [ite_eq_right hjk]; exact integrable_const 0
  have he (z) : L z*fderiv ℝ (hierarchyPathLogDensity n m f) z (coordinateAxis n j)=
      a j*(L z*G z-∑ k : Fin (n+1), if j.val < k.val then hierarchyAtom n m 1 k*(L z*M k z) else 0) := by
    rw [affineHierarchy_score_coordinate n m c U g (a j) j (fun s => hU s j)]
    simp only [mul_sub,Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro k _
      split_ifs <;> ring
  have heS : (∑ k : Fin (n+1), ∫ z, (if j.val < k.val then hierarchyAtom n m 1 k*(L z*M k z) else 0) ∂μ)=
      (1-m j)*(∫ z, L z*G z ∂μ) := by
    rw [← hierarchyAtom_tail_sum n m 1 j,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    by_cases hjk : j.val < k.val
    · rw [ite_eq_left hjk]
      simp only [ite_eq_left hjk,integral_const_mul,hprod k (show i.val < k.val from lt_of_le_of_lt hij hjk)]
    · simp only [ite_eq_right hjk,integral_zero,zero_mul]
  have hc : (∫ z, L z*G z ∂μ)=a i*affineHierarchyResponse n m c U g i x :=
    weightedHierarchy_coordinate_covariance_at n m c U g (a i) i (fun s => hU s i) x
  calc
    _ = ∫ z, coordinateProjection n j z*L z ∂μ := by congr 1; funext z; ring
    _ = (if i=j then 1 else 0)+∫ z, L z*fderiv ℝ (hierarchyPathLogDensity n m f) z (coordinateAxis n j) ∂μ := by
      simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using H
    _ = (if i=j then 1 else 0)+a j*((∫ z, L z*G z ∂μ)-(1-m j)*(∫ z, L z*G z ∂μ)) := by
      rw [integral_congr_ae (ae_of_all _ he),integral_const_mul,integral_sub hiG
        (integrable_finsetSum _ (fun k _ => hJ k)),integral_finsetSum _ (fun k _ => hJ k),heS]
    _ = _ := by rw [hc]; ring

theorem affineHierarchy_increment_covariance_symm (n : ℕ) (m : Fin n → ℝ)
    (c : S → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ) (g : S → ℝ)
    (a : Fin n → ℝ) (hU : ∀ s i, U s (coordinateAxis n i)=a i*g s)
    (i j : Fin n) (x : ℝ) :
    (∫ z, coordinateProjection n i z*coordinateProjection n j z
      ∂hierarchyPathLaw n m (affineLogPartition c U) x)=
      (if i=j then 1 else 0)+a i*a j*m (max i j)*affineHierarchyResponse n m c U g (min i j) x := by
  classical
  rcases le_total i j with hij|hji
  · simpa only [max_eq_right hij,min_eq_left hij] using affineHierarchy_increment_covariance n m c U g a hU i j hij x
  · rw [max_eq_left hji,min_eq_right hji]
    have H := affineHierarchy_increment_covariance n m c U g a hU j i hji x
    rw [integral_congr_ae (ae_of_all _ (fun z => mul_comm (coordinateProjection n i z) (coordinateProjection n j z))),H]
    have he : (if j=i then (1:ℝ) else 0)=(if i=j then 1 else 0) := by simp only [eq_comm]
    rw [he]
    ring

end

end SK.Analytic

end
end

end OAI

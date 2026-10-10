import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.WeightedHierarchyCovariance
import OAI.Probability.SKBarriers.Scalar.TerminalPathStability

namespace OAI

section

noncomputable section
open scoped BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

section
variable {S : Type} [Fintype S] [Nonempty S]

theorem affineHierarchy_coordinate_bound (n : ℕ) (m : Fin n → ℝ)
    (c : S → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ) (i : Fin n)
    {C : ℝ} (hC : 0 ≤ C) (hU : ∀ s, |U s (coordinateAxis n i)| ≤ C)
    (j : Fin (n+1)) (z : ParameterSpace n) :
    |fderiv ℝ (hierarchyLevel n m (affineLogPartition c U) j) z (coordinateAxis n i)| ≤ C := by
  have H := hierarchyLevel_affine_coordinate n m c U (fun s => U s (coordinateAxis n i)) 1 i
    (fun s => by simp) j z
  rw [H]
  split_ifs
  · simp only [one_mul]
    have Hb := affineMoment_norm_le c U (fun s => U s (coordinateAxis n i))
      (fun s => by simpa only [Real.norm_eq_abs] using hU s)
    simpa only [Real.norm_eq_abs] using
      (hierarchyMomentLevel_bounded_continuous n m _ _ (affineLogPartition_boundedDerivs c U)
        (affineMoment_contDiff c U _).continuous hC Hb j).2 z
  · simpa using hC

def hierarchyPathLogDensity (n : ℕ) (m : Fin n → ℝ) (f : ParameterSpace n → ℝ) : ParameterSpace n → ℝ :=
  fun z => f z-hierarchyPenalty n m 1 f z

theorem hierarchyPathLogDensity_regular (n : ℕ) (m : Fin n → ℝ)
    {f : ParameterSpace n → ℝ} (hf : BoundedDerivs f) : BoundedDerivs (hierarchyPathLogDensity n m f) := by
  convert hf.add ((hierarchyPenalty_boundedDerivs n m 1 f hf).const_mul (-1)) using 1
  funext z; dsimp only [hierarchyPathLogDensity]; ring

theorem affineHierarchy_score_coordinate_bound (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m)
    (c : S → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ) (i : Fin n)
    {C : ℝ} (hC : 0 ≤ C) (hU : ∀ s, |U s (coordinateAxis n i)| ≤ C)
    (z : ParameterSpace n) :
    |fderiv ℝ (hierarchyPathLogDensity n m (affineLogPartition c U)) z (coordinateAxis n i)| ≤ 2*C := by
  let f := affineLogPartition c U
  have hf := affineLogPartition_boundedDerivs c U
  have hp := hierarchyPenalty_boundedDerivs n m 1 f hf
  have hw (j) : 0 ≤ hierarchyAtom n m 1 j :=
    hierarchyAtom_nonneg n m zero_le_one (fun i => (hm i).1) (fun i => (hm i).2) hmono j
  have hl (j) := affineHierarchy_coordinate_bound n m c U i hC hU j z
  have hpB : |fderiv ℝ (hierarchyPenalty n m 1 f) z (coordinateAxis n i)| ≤ C := by
    rw [fderiv_hierarchyPenalty_apply n m 1 f hf]
    calc
      _ ≤ ∑ j, |hierarchyAtom n m 1 j*fderiv ℝ (hierarchyLevel n m f j) z (coordinateAxis n i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, hierarchyAtom n m 1 j*C := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul,abs_of_nonneg (hw j)]
        exact mul_le_mul_of_nonneg_left (hl j) (hw j)
      _ = C := by rw [← Finset.sum_mul,hierarchyAtom_sum,one_mul]
  have hfB : |fderiv ℝ f z (coordinateAxis n i)| ≤ C := by
    have H := hl (Fin.last n)
    have he : hierarchyLevel n m f (Fin.last n)=f := by
      cases n with
      | zero => rfl
      | succ n => simp only [hierarchyLevel,Fin.lastCases_last]
    change |fderiv ℝ (hierarchyLevel n m f (Fin.last n)) z (coordinateAxis n i)| ≤ C at H
    simpa only [he] using H
  change |fderiv ℝ (fun z => f z-hierarchyPenalty n m 1 f z) z (coordinateAxis n i)| ≤ 2*C
  rw [fderiv_fun_sub (hf.1.differentiable (by norm_num) z)
    (hp.1.differentiable (by norm_num) z),sub_apply]
  exact (abs_sub _ _).trans (by linarith)

theorem affineHierarchy_score_direction_bound (n : ℕ) (m : Fin n → ℝ)
    (hm : ∀ i, m i∈Icc (0:ℝ) 1) (hmono : Monotone m)
    (c : S → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ) (C : Fin n → ℝ)
    (hC : ∀ i, 0 ≤ C i) (hU : ∀ s i, |U s (coordinateAxis n i)| ≤ C i)
    (a : Fin n → ℝ) (z : ParameterSpace n) :
    |fderiv ℝ (hierarchyPathLogDensity n m (affineLogPartition c U)) z (coordinateVector n a)| ≤
      2*∑ i, |a i| *C i := by
  rw [coordinateVector,map_sum]
  calc
    _ ≤ ∑ i, |fderiv ℝ (hierarchyPathLogDensity n m (affineLogPartition c U)) z (a i • coordinateAxis n i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |a i| *(2*C i) := by
      apply Finset.sum_le_sum
      intro i _
      rw [map_smul,smul_eq_mul,abs_mul]
      exact mul_le_mul_of_nonneg_left
        (affineHierarchy_score_coordinate_bound n m hm hmono c U i (hC i) (fun s => hU s i) z) (abs_nonneg _)
    _ = _ := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring

end

end SK.Analytic

end
end

end OAI

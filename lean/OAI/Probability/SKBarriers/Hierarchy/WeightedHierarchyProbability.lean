import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.HierarchyReplica
import OAI.Probability.SKBarriers.Replicas.ReplicaEdgeIdentity

namespace OAI

section

noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace
section
variable {S : Type} [Fintype S] [Nonempty S]

def weightedHierarchyWeight (n : ℕ) (m : Fin n → ℝ) (c : S → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (j : Fin (n+1))
    (z : ParameterSpace n) (s : S) : ℝ :=
  hierarchyMomentLevel n m (affineLogPartition c U) (fun z => affineGibbs c U z s) j z

theorem weightedHierarchyWeight_regular (n : ℕ) (m : Fin n → ℝ) (c : S → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (j : Fin (n+1)) (s : S) :
    Continuous (fun z => weightedHierarchyWeight n m c U j z s) ∧
      ∀ z, ‖weightedHierarchyWeight n m c U j z s‖ ≤ 1 :=
  hierarchyMomentLevel_bounded_continuous n m _ _ (affineLogPartition_boundedDerivs c U)
    (affineGibbs_continuous c U s) (by norm_num) (fun z => affineGibbs_norm_le_one c U z s) j

theorem weightedHierarchyWeight_nonneg (n : ℕ) (m : Fin n → ℝ) (c : S → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (j : Fin (n+1)) (z : ParameterSpace n) (s : S) :
    0 ≤ weightedHierarchyWeight n m c U j z s :=
  hierarchyMomentLevel_nonneg n m _ _ (fun z => (affineGibbs_pos c U z s).le) j z

theorem weightedHierarchyWeight_sum (n : ℕ) (m : Fin n → ℝ) (c : S → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (j : Fin (n+1)) (z : ParameterSpace n) :
    ∑ s, weightedHierarchyWeight n m c U j z s = 1 := by
  have H := hierarchyMomentLevel_sum n m (affineLogPartition c U)
    (affineLogPartition_boundedDerivs c U) (fun s z => affineGibbs c U z s)
    (affineGibbs_continuous c U) (fun _ => 1) (fun _ => by norm_num)
    (fun s z => affineGibbs_norm_le_one c U z s) j
  have he : (fun z => ∑ s, affineGibbs c U z s) = fun _ => 1 := funext (affineGibbs_sum c U)
  rw [he,hierarchyMomentLevel_const n m _ (affineLogPartition_boundedDerivs c U)] at H
  exact (congrFun H z).symm

theorem weightedHierarchyMean_eq_sum (n : ℕ) (m : Fin n → ℝ) (c : S → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (g : S → ℝ) (j : Fin (n+1)) (z : ParameterSpace n) :
    hierarchyMomentLevel n m (affineLogPartition c U) (affineMoment c U g) j z =
      ∑ s, weightedHierarchyWeight n m c U j z s*g s := by
  have H := hierarchyMomentLevel_sum n m (affineLogPartition c U)
    (affineLogPartition_boundedDerivs c U) (fun s z => g s*affineGibbs c U z s)
    (fun s => continuous_const.mul (affineGibbs_continuous c U s))
    (fun s => ‖g s‖) (fun s => norm_nonneg _) (fun s z => by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (affineGibbs_norm_le_one c U z s) (norm_nonneg _)).trans_eq (mul_one _)) j
  simp_rw [hierarchyMomentLevel_const_mul] at H
  change hierarchyMomentLevel n m (affineLogPartition c U)
    (fun z => ∑ s, affineGibbs c U z s*g s) j z = _
  simpa only [weightedHierarchyWeight,mul_comm] using congrFun H z

def weightedHierarchyReplica (n : ℕ) (m : Fin n → ℝ) (c : S → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (j : Fin (n+1)) (K : S → S → ℝ) : ℝ :=
  ∫ z, finiteReplicaMoment (weightedHierarchyWeight n m c U j z) K
    ∂hierarchyPathLaw n m (affineLogPartition c U) 0

theorem weightedHierarchyReplica_integrable (n : ℕ) (m : Fin n → ℝ) (c : S → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (j : Fin (n+1)) (K : S → S → ℝ) :
    Integrable (fun z => finiteReplicaMoment (weightedHierarchyWeight n m c U j z) K)
      (hierarchyPathLaw n m (affineLogPartition c U) 0) := by
  classical
  let B := ∑ s, ∑ t, ‖K s t‖
  apply hierarchyPathLaw_integrable n m _ _ (affineLogPartition_boundedDerivs c U)
    (finiteReplicaMoment_continuous _ (fun s => (weightedHierarchyWeight_regular n m c U j s).1) K)
    (C:=B)
  intro z
  unfold finiteReplicaMoment
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro s _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro t _
  simp only [norm_mul]
  have hs := (weightedHierarchyWeight_regular n m c U j s).2 z
  have ht := (weightedHierarchyWeight_regular n m c U j t).2 z
  have H := mul_le_mul hs ht (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  exact (mul_le_mul_of_nonneg_right H (norm_nonneg _)).trans_eq (by ring)

theorem weightedHierarchyReplica_const (n : ℕ) (m : Fin n → ℝ) (c : S → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (j : Fin (n+1)) (a : ℝ) :
    weightedHierarchyReplica n m c U j (fun _ _ => a) = a := by
  let := hierarchyPathLaw_probability n m _ (affineLogPartition_boundedDerivs c U) 0
  simp only [weightedHierarchyReplica,finiteReplicaMoment_const _ (weightedHierarchyWeight_sum n m c U j _),integral_const,probReal_univ,smul_eq_mul,one_mul]

theorem weightedHierarchyReplica_mono (n : ℕ) (m : Fin n → ℝ) (c : S → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (j : Fin (n+1)) {K L : S → S → ℝ}
    (h : ∀ s t, K s t ≤ L s t) :
    weightedHierarchyReplica n m c U j K ≤ weightedHierarchyReplica n m c U j L :=
  integral_mono (weightedHierarchyReplica_integrable n m c U j K)
    (weightedHierarchyReplica_integrable n m c U j L)
    (fun z => finiteReplicaMoment_mono _ (weightedHierarchyWeight_nonneg n m c U j z) K L h)

theorem weightedHierarchyReplica_sum {I : Type} [Fintype I] (n : ℕ) (m : Fin n → ℝ)
    (c : S → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ) (j : Fin (n+1)) (K : I → S → S → ℝ) :
    weightedHierarchyReplica n m c U j (fun s t => ∑ i, K i s t) =
      ∑ i, weightedHierarchyReplica n m c U j (K i) := by
  simp only [weightedHierarchyReplica,finiteReplicaMoment_sum]
  exact integral_finsetSum _ (fun i _ => weightedHierarchyReplica_integrable n m c U j (K i))

omit [Nonempty S] in
theorem weightedHierarchyReplica_const_mul (n : ℕ) (m : Fin n → ℝ) (c : S → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (j : Fin (n+1)) (K : S → S → ℝ) (a : ℝ) :
    weightedHierarchyReplica n m c U j (fun s t => a*K s t) =
      a*weightedHierarchyReplica n m c U j K := by
  simp only [weightedHierarchyReplica,finiteReplicaMoment_const_mul,integral_const_mul]

theorem weightedHierarchyReplica_separable_square (n : ℕ) (m : Fin n → ℝ) (c : S → ℝ)
    (U : S → ParameterSpace n →L[ℝ] ℝ) (j : Fin (n+1)) (g : S → ℝ) :
    weightedHierarchyReplica n m c U j (fun s t => g s*g t) =
      ∫ z, (hierarchyMomentLevel n m (affineLogPartition c U) (affineMoment c U g) j z)^2
        ∂hierarchyPathLaw n m (affineLogPartition c U) 0 := by
  simp only [weightedHierarchyReplica,finiteReplicaMoment_separable_square,weightedHierarchyMean_eq_sum]

end
end SK.Analytic

end
end

end OAI

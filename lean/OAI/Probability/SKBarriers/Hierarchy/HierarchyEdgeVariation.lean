import Mathlib
import OAI.Probability.SKBarriers.Hierarchy.HierarchyReplicaSecond
import OAI.Probability.SKBarriers.Replicas.ReplicaEdgeIdentity

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter
namespace SK.Analytic
attribute [local instance 2000] parameterNormedGroup parameterNormedSpace

theorem hierarchySpinMean_square_integrable {S : Type} [Fintype S] [Nonempty S]
    (n : ℕ) (m : Fin n → ℝ) (U : S → ParameterSpace n →L[ℝ] ℝ) (c : S → ℝ)
    (hc : ∀ s, ‖c s‖ ≤ 1) (j : Fin (n+1)) :
    Integrable (fun z => (hierarchySpinMean n m U c j z)^2)
      (hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0) := by
  have hr := hierarchySpinMean_regular n m U c (by norm_num : (0:ℝ) ≤ 1) hc j
  apply hierarchyPathLaw_integrable n m _ _ (affineLogPartition_boundedDerivs (fun _ => 0) U)
    (hr.1.pow 2) (C := 1) _ 0
  intro z
  dsimp only [Pi.pow_apply]
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (hr.2 z)

theorem hierarchy_edge_variation {N : ℕ} (hN : 0 < N)
    (n : ℕ) (m : Fin n → ℝ) (U : Config N → ParameterSpace n →L[ℝ] ℝ) (j : Fin (n+1)) :
    2*(∑ e : Edge N, (1-∫ z, (hierarchySpinMean n m U
      (fun s => spin (s e.val.1)*spin (s e.val.2)) j z)^2
        ∂hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0)) =
      (N:ℝ)^2*(1-hierarchyReplicaSecond n m U (fun s i => spin (s i)) j) := by
  let μ := hierarchyPathLaw n m (affineLogPartition (fun _ => 0) U) 0
  let := hierarchyPathLaw_probability n m _ (affineLogPartition_boundedDerivs (fun _ => 0) U) 0
  have hi (e : Edge N) : Integrable (fun z => (hierarchySpinMean n m U
      (fun s => spin (s e.val.1)*spin (s e.val.2)) j z)^2) μ := by
    exact hierarchySpinMean_square_integrable n m U _ (fun s => by cases s e.val.1 <;> cases s e.val.2 <;> norm_num [spin]) j
  have hs := hierarchyReplicaSecond_integrable n m U (fun s i => spin (s i))
    (fun s i => by cases s i <;> norm_num [spin]) j
  calc
    _ = ∫ z, 2*(∑ e : Edge N, (1-(hierarchySpinMean n m U
        (fun s => spin (s e.val.1)*spin (s e.val.2)) j z)^2)) ∂μ := by
      rw [integral_const_mul,integral_finsetSum]
      · congr 1
        apply Finset.sum_congr rfl
        intro e _
        rw [integral_sub (integrable_const 1) (hi e)]
        simp [μ]
      · intro e _
        exact (integrable_const 1).sub (hi e)
    _ = ∫ z, (N:ℝ)^2*(1-finiteReplicaMoment (hierarchySpinWeight n m U j z)
        (fun s t => (normalizedDot (fun i => spin (s i)) (fun i => spin (t i)))^2)) ∂μ := by
      apply integral_congr_ae
      exact ae_of_all _ fun z => by
        simp only [hierarchySpinMean_eq_sum]
        exact finiteReplica_edge_variation hN _ (hierarchySpinWeight_sum n m U j z)
    _ = _ := by
      rw [integral_const_mul,integral_sub (integrable_const 1) hs]
      simp [hierarchyReplicaSecond]
end SK.Analytic

end
end

end

end OAI

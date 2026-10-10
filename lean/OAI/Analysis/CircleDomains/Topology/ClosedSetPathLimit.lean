import Mathlib.Topology.UniformSpace.Path
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace OAI

/-! Uniform limits of successively improved ambient paths lie in the
closed target set, retaining the endpoints and all summable error bounds. -/
open Set Function Filter Metric
open scoped Topology unitInterval
noncomputable section
namespace CircleDomainRigidity

lemma closed_set_path_limit
    {E : Type*} [MetricSpace E] [CompleteSpace E] {K : Set E} (hK : IsClosed K)
    {x y : E} (γ : ℕ → Path x y) (d η : ℕ → ℝ) (hd : Summable d) (hd0 : ∀ n, 0 ≤ d n)
    (hstep : ∀ n t, dist (γ n t) (γ (n + 1) t) ≤ d n)
    (hη : Tendsto η atTop (𝓝 0)) (hnear : ∀ n t, ∃ c ∈ K, dist (γ n t) c < η n) :
    ∃ β : Path x y, (∀ t, β t ∈ K) ∧
      ∀ n t, dist (γ n t) (β t) ≤ ∑' j, d (n + j) := by
  let F : ℕ → C(I, E) := fun n => (γ n).toContinuousMap
  have hdist : ∀ n, dist (F n) (F (n + 1)) ≤ d n := fun n =>
    (ContinuousMap.dist_le (hd0 n)).mpr (hstep n)
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_dist_le_of_summable d hdist hd)
  have hpt : ∀ t, Tendsto (fun n => F n t) atTop (𝓝 (g t)) := fun t =>
    (continuous_eval_const t).continuousAt.tendsto.comp hg
  have h0 : g 0 = x := by
    have h : Tendsto (fun _ : ℕ => x) atTop (𝓝 (g 0)) := by simpa [F] using hpt 0
    exact tendsto_nhds_unique h tendsto_const_nhds
  have h1 : g 1 = y := by
    have h : Tendsto (fun _ : ℕ => y) atTop (𝓝 (g 1)) := by simpa [F] using hpt 1
    exact tendsto_nhds_unique h tendsto_const_nhds
  let β : Path x y := { toContinuousMap := g, source' := h0, target' := h1 }
  refine ⟨β, ?_, ?_⟩
  · intro t
    choose c hc hdistance using fun n => hnear n t
    have hct : Tendsto c atTop (𝓝 (g t)) := by
      apply Metric.tendsto_nhds.mpr
      intro ε hε
      have hFe := Metric.tendsto_nhds.mp (hpt t) (ε / 2) (by linarith)
      have hηe := hη.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by linarith))
      filter_upwards [hFe, hηe] with n hn hηn
      have hd' := hdistance n
      have ht := dist_triangle (c n) (F n t) (g t)
      rw [dist_comm (c n) (F n t)] at ht
      change dist (γ n t) (g t) < ε / 2 at hn
      change dist (c n) (g t) ≤ dist (γ n t) (c n) + dist (γ n t) (g t) at ht
      linarith
    exact hK.mem_of_tendsto hct (Eventually.of_forall hc)
  · intro n t
    have ht := dist_le_tsum_of_dist_le_of_tendsto d hdist hd hg n
    exact (ContinuousMap.dist_apply_le_dist t).trans ht

end CircleDomainRigidity

end

end OAI

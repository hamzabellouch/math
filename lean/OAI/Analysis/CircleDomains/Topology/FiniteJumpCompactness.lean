import OAI.Analysis.CircleDomains.Uniformization.ShrinkingJumpLimits

namespace OAI

/-! Common compactness for finitely many shrinking new jumps and true
pieces, retaining fixed old-jump costs in the limiting total budget. -/

open Set Function Filter Metric
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X I P : Type*} [MetricSpace X] [CompactSpace X] [Fintype I] [Fintype P]

theorem exists_joint_finite_jump_limits
    (B : Set X) (hB : IsClosed B) (m : X → ℝ≥0∞) (r : ℝ≥0∞)
    {τ : ℝ} (hτ : 0 < τ) (V : I → ℕ → Set X) (x y : I → ℕ → X)
    (c : P → ℕ → ℝ≥0∞)
    (hx : ∀i k, x i k ∈ V i k) (hy : ∀i k, y i k ∈ V i k)
    (hmeet : ∀i k, (V i k ∩ B).Nonempty)
    (hdiam : ∀i, Tendsto (fun k => diam (V i k)) atTop (𝓝 0))
    (K M : ℝ≥0∞)
    (hbudget : ∀k, (∑i, c i k) + (∑i, fixedWidthJumpToll B m r τ (V i k)) + K ≤ M) :
    ∃ (s : ℕ → ℕ) (p : I → X) (A : P → ℝ≥0∞) (J : I → ℝ≥0∞),
      StrictMono s ∧ (∀i, p i ∈ B) ∧
      (∀i, Tendsto (x i ∘ s) atTop (𝓝 (p i))) ∧
      (∀i, Tendsto (y i ∘ s) atTop (𝓝 (p i))) ∧
      (∀i, Tendsto (c i ∘ s) atTop (𝓝 (A i))) ∧
      (∀i, Tendsto (fun k => fixedWidthJumpToll B m r τ (V i (s k))) atTop (𝓝 (J i))) ∧
      (∀i, m (p i) ≤ J i) ∧ (∑i, A i) + (∑i, J i) + K ≤ M := by
  let v : ℕ → (I → X) × (P → ℝ≥0∞) × (I → ℝ≥0∞) :=
    fun k => (fun i => x i k, (fun i => c i k),
      (fun i => fixedWidthJumpToll B m r τ (V i k)))
  obtain ⟨q, _, s, hs, hv⟩ := isCompact_univ.tendsto_subseq (fun k => mem_univ (v k))
  have hxs (i : I) : Tendsto (x i ∘ s) atTop (𝓝 (q.1 i)) :=
    ((continuous_apply i).tendsto q.1).comp ((continuous_fst.tendsto q).comp hv)
  have hAs (i : P) : Tendsto (c i ∘ s) atTop (𝓝 (q.2.1 i)) :=
    ((continuous_apply i).tendsto q.2.1).comp
      ((continuous_fst.tendsto q.2).comp ((continuous_snd.tendsto q).comp hv))
  have hJs (i : I) :
      Tendsto (fun k => fixedWidthJumpToll B m r τ (V i (s k))) atTop (𝓝 (q.2.2 i)) :=
    ((continuous_apply i).tendsto q.2.2).comp
      ((continuous_snd.tendsto q.2).comp ((continuous_snd.tendsto q).comp hv))
  have hclose (i : I) (z : ℕ → X) (hz : ∀k, z k ∈ V i k) :
      Tendsto (fun k => dist (x i (s k)) (z (s k))) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => dist_nonneg) _ ((hdiam i).comp hs.tendsto_atTop)
    intro k
    exact dist_le_diam_of_mem
      ((isCompact_univ : IsCompact (univ : Set X)).isBounded.subset (subset_univ (V i (s k))))
      (hx i (s k)) (hz (s k))
  have hpB (i : I) : q.1 i ∈ B := by
    choose b hb using hmeet i
    exact hB.mem_of_tendsto ((hxs i).congr_dist (hclose i b (fun k => (hb k).1)))
      (Eventually.of_forall (fun k => (hb (s k)).2))
  have hys (i : I) : Tendsto (y i ∘ s) atTop (𝓝 (q.1 i)) :=
    (hxs i).congr_dist (hclose i (y i) (hy i))
  have hpaid (i : I) : m (q.1 i) ≤ q.2.2 i :=
    limiting_fixedWidthJumpToll_ge B m r hτ (hxs i) (fun k => hx i (s k)) (hpB i) (hJs i)
  have htotal : Tendsto (fun k => (∑i, c i (s k)) +
      (∑i, fixedWidthJumpToll B m r τ (V i (s k))) + K) atTop
      (𝓝 ((∑i, q.2.1 i) + (∑i, q.2.2 i) + K)) :=
    ((tendsto_finsetSum _ (fun i _ => hAs i)).add
      (tendsto_finsetSum _ (fun i _ => hJs i))).add tendsto_const_nhds
  exact ⟨s, q.1, q.2.1, q.2.2, hs, hpB, hxs, hys, hAs, hJs, hpaid,
    le_of_tendsto htotal (Eventually.of_forall (fun k => hbudget (s k)))⟩

end CircleDomainRigidity

end

end OAI

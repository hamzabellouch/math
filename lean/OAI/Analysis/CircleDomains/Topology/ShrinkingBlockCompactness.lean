import OAI.Analysis.CircleDomains.Uniformization.ShrinkingJumpLimits
import OAI.Analysis.CircleDomains.Selection.FiniteJunctionBlock

namespace OAI

/-! One simultaneous subsequence for every true-piece and new-jump cost
in a finite block, retaining the full limiting budget. -/

open Set Function Filter Metric MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [CompactSpace X] [MetricSpace Y]
  [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace Y]
  [MeasurableSpace C(PathTime, X)]

omit [MeasurableSpace X] in
theorem exists_finite_shrinking_block_limits
    (d : PathCodeData X Y) (B : Set X) (hB : IsClosed B)
    (g : Y → ℝ≥0∞) (m : X → ℝ≥0∞) (ρ : ℝ≥0∞) {τ : ℝ} (hτ : 0 < τ)
    (n : ℕ) (Γ : Fin (n+2) → ℕ → TaggedPhysicalPath d)
    (V : Fin (n+1) → ℕ → Set X)
    (hleft : ∀i k, (Γ i.castSucc k).1.val ⊤ ∈ V i k)
    (hright : ∀i k, (Γ i.succ k).1.val ⊥ ∈ V i k)
    (hmeet : ∀i k, (V i k ∩ B).Nonempty)
    (hdiam : ∀i, Tendsto (fun k => diam (V i k)) atTop (𝓝 0))
    (M : ℝ≥0∞)
    (hbudget : ∀k, (∑i, physicalTollCost d g m (Γ i k).1) +
      (∑i, fixedWidthJumpToll B m ρ τ (V i k)) ≤ M) :
    ∃ (s : ℕ → ℕ) (p : Fin (n+1) → X)
      (A : Fin (n+2) → ℝ≥0∞) (J : Fin (n+1) → ℝ≥0∞),
      StrictMono s ∧ (∀i, p i ∈ B) ∧
      (∀i, Tendsto (fun k => (Γ i.castSucc (s k)).1.val ⊤) atTop (𝓝 (p i))) ∧
      (∀i, Tendsto (fun k => (Γ i.succ (s k)).1.val ⊥) atTop (𝓝 (p i))) ∧
      (∀i, Tendsto (fun k => physicalTollCost d g m (Γ i (s k)).1) atTop (𝓝 (A i))) ∧
      (∀i, Tendsto (fun k => fixedWidthJumpToll B m ρ τ (V i (s k))) atTop (𝓝 (J i))) ∧
      (∀i, m (p i) ≤ J i) ∧ (∑i, A i) + (∑i, J i) ≤ M := by
  let v : ℕ → (Fin (n+1) → X) × (Fin (n+2) → ℝ≥0∞) × (Fin (n+1) → ℝ≥0∞) :=
    fun k => (fun i => (Γ i.castSucc k).1.val ⊤,
      (fun i => physicalTollCost d g m (Γ i k).1),
      (fun i => fixedWidthJumpToll B m ρ τ (V i k)))
  obtain ⟨q, _, s, hs, hv⟩ := isCompact_univ.tendsto_subseq (fun k => mem_univ (v k))
  have hxs (i : Fin (n+1)) :
      Tendsto (fun k => (Γ i.castSucc (s k)).1.val ⊤) atTop (𝓝 (q.1 i)) :=
    ((continuous_apply i).tendsto q.1).comp ((continuous_fst.tendsto q).comp hv)
  have hAs (i : Fin (n+2)) :
      Tendsto (fun k => physicalTollCost d g m (Γ i (s k)).1) atTop (𝓝 (q.2.1 i)) :=
    ((continuous_apply i).tendsto q.2.1).comp
      ((continuous_fst.tendsto q.2).comp ((continuous_snd.tendsto q).comp hv))
  have hJs (i : Fin (n+1)) :
      Tendsto (fun k => fixedWidthJumpToll B m ρ τ (V i (s k))) atTop (𝓝 (q.2.2 i)) :=
    ((continuous_apply i).tendsto q.2.2).comp
      ((continuous_snd.tendsto q.2).comp ((continuous_snd.tendsto q).comp hv))
  have hclose (i : Fin (n+1)) (z : ℕ → X) (hz : ∀k, z k ∈ V i k) :
      Tendsto (fun k => dist ((Γ i.castSucc (s k)).1.val ⊤) (z (s k))) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => dist_nonneg) _ ((hdiam i).comp hs.tendsto_atTop)
    intro k
    exact dist_le_diam_of_mem
      ((isCompact_univ : IsCompact (univ : Set X)).isBounded.subset (subset_univ (V i (s k))))
      (hleft i (s k)) (hz (s k))
  have hpB (i : Fin (n+1)) : q.1 i ∈ B := by
    choose b hb using hmeet i
    exact hB.mem_of_tendsto ((hxs i).congr_dist (hclose i b (fun k => (hb k).1)))
      (Eventually.of_forall (fun k => (hb (s k)).2))
  have hys (i : Fin (n+1)) :
      Tendsto (fun k => (Γ i.succ (s k)).1.val ⊥) atTop (𝓝 (q.1 i)) :=
    (hxs i).congr_dist (hclose i (fun k => (Γ i.succ k).1.val ⊥) (hright i))
  have hpaid (i : Fin (n+1)) : m (q.1 i) ≤ q.2.2 i :=
    limiting_fixedWidthJumpToll_ge B m ρ hτ (hxs i) (fun k => hleft i (s k)) (hpB i) (hJs i)
  have htotal : Tendsto (fun k => (∑i, physicalTollCost d g m (Γ i (s k)).1) +
      (∑i, fixedWidthJumpToll B m ρ τ (V i (s k)))) atTop
      (𝓝 ((∑i, q.2.1 i) + (∑i, q.2.2 i))) :=
    (tendsto_finsetSum _ (fun i _ => hAs i)).add (tendsto_finsetSum _ (fun i _ => hJs i))
  exact ⟨s, q.1, q.2.1, q.2.2, hs, hpB, hxs, hys, hAs, hJs, hpaid,
    le_of_tendsto htotal (Eventually.of_forall (fun k => hbudget (s k)))⟩

end CircleDomainRigidity

end

end OAI

import OAI.Analysis.CircleDomains.Topology.ShrinkingBallNeighborhoods
import OAI.Analysis.CircleDomains.Rigidity.TracePrimitivePlateau

namespace OAI

/-! Closed component correspondence and shrinking balloon radii supply
the tail conditions in the continuity proof of the actual infinite mask. -/
open Set Function Filter Metric MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem correspondence_mask_continuousAt_singleton
    {X Y : Type*} [PseudoMetricSpace X] [TopologicalSpace Y] [CompactSpace Y]
    {R : X → Y → Prop} (hR : IsClosed {p : X × Y | R p.1 p.2})
    {s : X → Y} (hs : ∀ q, R q (s q)) {φ : Y → ℝ} (hφ : Continuous φ)
    {cutoff : ℕ → X → ℝ} (hc : ∀ j q, cutoff j q ∈ Icc (0:ℝ) 1)
    (hcc : ∀ j, Continuous (cutoff j)) (c : ℕ → X) {d ε : ℕ → ℝ}
    (hd : Tendsto d atTop (𝓝 0)) (hε : Tendsto ε atTop (𝓝 0))
    (hout : ∀ j q, d j ≤ dist q (c j) → cutoff j q = 1)
    {I : ℕ → Set ℝ} (hI : ∀ j, MeasurableSet (I j)) (hIf : ∀ j, volume (I j) ≠ ⊤)
    (hrep : ∀ j t, t ∈ I j → ∃ p, R (c j) p ∧ |t-φ p| ≤ ε j)
    {x : X} (hsingle : ∀ p, R x p → p = s x) (a : ℝ) :
    ContinuousAt (fun q => infiniteTracePrimitive cutoff I a q (φ (s q))) x := by
  have hb := hφ.continuousAt.comp (closed_relation_selection_continuousAt hR s hs hsingle)
  apply infinite_masked_scalar_continuousAt hc hcc hI hIf hb a
  intro δ hδ
  obtain ⟨V,hV,hxV,N,hN⟩ := closed_relation_shrinking_intervals hR hφ
    (K := {x}) isCompact_singleton (half_pos hδ)
    (a := φ (s x)-δ) (b := φ (s x)+δ) (by
      intro q hq p hp
      rw [mem_singleton_iff] at hq
      subst q
      rw [hsingle p hp]
      constructor <;> linarith) c hd hε I hrep
  refine ⟨N,?_⟩
  filter_upwards [hV.mem_nhds (hxV (mem_singleton x))] with q hq
  intro j hj t ht hnot
  by_contra hne
  have hball : q ∈ ball (c j) (d j) := by
    rw [mem_ball]
    exact lt_of_not_ge (fun hh => hne (hout j q hh))
  exact hnot (hN j hj q hq hball ht)

 theorem correspondence_mask_indexed_neighborhood
    {X Y : Type*} [PseudoMetricSpace X] [TopologicalSpace Y] [CompactSpace Y]
    {R : X → Y → Prop} (hR : IsClosed {p : X × Y | R p.1 p.2})
    {s : X → Y} (hs : ∀ q, R q (s q)) {φ : Y → ℝ} (hφ : Continuous φ)
    {cutoff : ℕ → X → ℝ} (hc : ∀ j q, cutoff j q ∈ Icc (0:ℝ) 1)
    (hcc : ∀ j, Continuous (cutoff j)) (c : ℕ → X) {d ε : ℕ → ℝ}
    (hd : Tendsto d atTop (𝓝 0)) (hε : Tendsto ε atTop (𝓝 0))
    (hout : ∀ j q, d j ≤ dist q (c j) → cutoff j q = 1)
    {I : ℕ → Set ℝ} (hI : ∀ j, MeasurableSet (I j)) (hIf : ∀ j, volume (I j) ≠ ⊤)
    (hrep : ∀ j t, t ∈ I j → ∃ p, R (c j) p ∧ |t-φ p| ≤ ε j)
    {K Z : Set X} (hK : IsCompact K) (hZ : IsOpen Z) (hKZ : K ⊆ Z)
    {j : ℕ} (hzero : ∀ q ∈ Z, cutoff j q = 0)
    {A B η β : ℝ} (hη : 0 < η) (hIj : I j = Ioo A B) (hβ : β ∈ I j)
    (hmargin : ∀ q ∈ K, ∀ p, R q p → φ p ∈ Ioo (A+η) (B-η)) (a : ℝ) :
    ∃ (N : ℕ) (V : Set X), IsOpen V ∧ K ⊆ V ∧
      ContinuousOn (fun q => infiniteTracePrimitive cutoff I a q (φ (s q))) V ∧
      ∀ q ∈ V, infiniteTracePrimitive cutoff I a q (φ (s q)) =
        finiteTracePrimitive cutoff I a q β N := by
  obtain ⟨T,hT,hKT,N,hN⟩ := closed_relation_shrinking_intervals hR hφ hK hη
    hmargin c hd hε I hrep
  obtain ⟨W,hW,hKW,hraw⟩ := closed_relation_neighborhood hR ((isOpen_Ioo : IsOpen (Ioo A B)).preimage hφ) (by
    intro q hq p hp
    have h := hmargin q hq p hp
    exact ⟨by linarith [h.1],by linarith [h.2]⟩)
  let V := Z ∩ T ∩ W
  let M := max N (j+1)
  have hV : IsOpen V := (hZ.inter hT).inter hW
  have hKV : K ⊆ V := fun q hq => ⟨⟨hKZ hq,hKT hq⟩,hKW hq⟩
  have hj : j < M := lt_of_lt_of_le (Nat.lt_succ_self j) (le_max_right _ _)
  have hdata (q : X) (hq : q ∈ V) : cutoff j q = 0 ∧ φ (s q) ∈ I j ∧
      ∀ k, M ≤ k → ∀ t ∈ I k, cutoff k q ≠ 1 → t ∈ I j := by
    refine ⟨hzero q hq.1.1,?_,?_⟩
    · rw [hIj]
      exact hraw q hq.2 _ (hs q)
    · intro k hk t ht hne
      rw [hIj]
      apply hN k ((le_max_left _ _).trans hk) q hq.1.2 _ ht
      rw [mem_ball]
      exact lt_of_not_ge (fun hh => hne (hout k q hh))
  refine ⟨M,V,hV,hKV,?_,?_⟩
  · intro q hq
    apply ContinuousAt.continuousWithinAt
    apply indexed_masked_scalar_continuousAt hc hcc hI hIf hj
      (hIj ▸ ordConnected_Ioo) hβ a
    filter_upwards [hV.mem_nhds hq] with z hz
    exact hdata z hz
  · intro q hq
    have h := hdata q hq
    rw [infiniteTracePrimitive_plateau hc hI (hIj ▸ ordConnected_Ioo) h.1 h.2.1 hβ a,
      infiniteTracePrimitive_absorbed_tail hc hj h.1 h.2.2 a β]

end CircleDomainRigidity

end

end OAI

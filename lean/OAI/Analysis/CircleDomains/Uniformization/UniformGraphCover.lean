import OAI.Analysis.CircleDomains.Sobolev.ColoredGridEnergy
import OAI.Analysis.CircleDomains.Selection.CountableGraphCover

namespace OAI

/-! Assemble local graph covers at one scale. The finite residue coloring
controls the cost by the energy of an open neighborhood. -/
open Set Function Filter MeasureTheory Metric
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma uniform_graph_cover {A O : Set GraphSpace} (μ : Measure GraphSpace)
    (K : ℝ≥0∞) {s : ℝ} (hs : 0 < s)
    (hsmall : ∀ x ∈ A, closedBall x (4*s) ⊆ O)
    (hlocal : ∀ x ∈ A, ∃ T : ℕ → Set GraphSpace,
      A ∩ closedBall x s ⊆ ⋃ n, T n ∧
      (∀ n, ediam (T n) ≤ ENNReal.ofReal (8*s)) ∧
      (∑' n, ediam (T n)^2) ≤ K*μ (closedBall x (4*s))) :
    ∃ (I : GraphGridColor → Set GraphGridIndex)
      (T : (r : GraphGridColor) → I r → ℕ → Set GraphSpace),
      A ⊆ ⋃ r, ⋃ i, ⋃ n, T r i n ∧
      (∀ r i n, ediam (T r i n) ≤ ENNReal.ofReal (8*s)) ∧
      (∑' r, ∑' i : I r, ∑' n, ediam (T r i n)^2) ≤ 4096*K*μ O := by
  classical
  let I : GraphGridColor → Set GraphGridIndex := fun r => {k | (A ∩ graphGridCell r k s).Nonempty}
  choose c hc using fun r (i : I r) => i.property
  choose T hT using fun r (i : I r) => hlocal (c r i) (hc r i).1
  refine ⟨I,T,?_,(fun r i n => (hT r i).2.1 n),?_⟩
  · intro x hx
    obtain ⟨r,k,hk⟩ := exists_graphGridCell hs x
    have hi : k ∈ I r := ⟨x,hx,hk⟩
    let i : I r := ⟨k,hi⟩
    have hd : dist x (c r i) ≤ s := graphGridCell_dist_le r k hk (hc r i).2
    obtain ⟨n,hn⟩ := mem_iUnion.mp ((hT r i).1 ⟨hx,hd⟩)
    exact mem_iUnion.mpr ⟨r,mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨n,hn⟩⟩⟩
  · calc
      _ ≤ ∑' r, ∑' i : I r, K*μ (closedBall (c r i) (4*s)) :=
        ENNReal.tsum_le_tsum (fun r => ENNReal.tsum_le_tsum (fun i => (hT r i).2.2))
      _ = K*(∑' r, ∑' i : I r, μ (closedBall (c r i) (4*s))) := by
        simp only [ENNReal.tsum_mul_left]
      _ ≤ K*(4096*μ O) := mul_le_mul' le_rfl
        (all_colored_grid_energy_sum μ hs I c (fun r i => (hc r i).2)
          (fun r i => hsmall (c r i) (hc r i).1))
      _ = _ := by ring

end CircleDomainRigidity

end

end OAI

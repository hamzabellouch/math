import OAI.MeasureTheory.Falconer.Recursion.ScalarTerminalPruning

namespace OAI

/-! Nonconcentration bounds the number of occupied scalar prefixes from
 below. This controls the ungrouped prefix left by the greedy ledger. -/
namespace Falconer.Regularization

 theorem scalar_prefix_ball_bound {N a : ℕ} (L : Finset (CellPath 1))
    (hL : L ⊆ cubePaths 1 N) (ha : a ≤ N) (p : CellPath 1) :
    ((prefixFiber L a p).card:ℝ) ≤
      scalarBallMass (L.image scalarPathCenter) (scalarPathCenter p) ((1/2:ℝ)^a) := by
  classical
  have hinj := scalarPathCenter_injOn (prefixFiber L a p) (fun q hq =>
    (mem_cubePaths 1 N q).mp (hL (Finset.mem_filter.mp hq).1))
  have hc := Finset.card_image_of_injOn hinj
  have hsub : (prefixFiber L a p).image scalarPathCenter ⊆
      (L.image scalarPathCenter).filter (fun x => |x-scalarPathCenter p| ≤ (1/2:ℝ)^a) := by
    intro x hx
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ (Finset.mem_filter.mp hq).1,
      scalar_prefix_leaf_center_dist hL ha hq⟩
  have hb := Finset.card_le_card hsub
  rw [hc] at hb
  unfold scalarBallMass
  exact_mod_cast hb

 theorem scalar_prefix_nonconcentration {N a : ℕ} (L : Finset (CellPath 1))
    (hL : L ⊆ cubePaths 1 N) (hne : L.Nonempty) (ha : a ≤ N) {K κ : ℝ}
    (hball : ∀ u t : ℝ, (1/2:ℝ)^N ≤ t → t ≤ 1 →
      scalarBallMass (L.image scalarPathCenter) u t ≤
        K*t^κ*((L.image scalarPathCenter).card:ℝ)) :
    1 ≤ ((L.image (List.take a)).card:ℝ)*K*((1/2:ℝ)^a)^κ := by
  classical
  have hcard : (L.image scalarPathCenter).card = L.card :=
    Finset.card_image_of_injOn (scalarPathCenter_injOn L (fun q hq =>
      (mem_cubePaths 1 N q).mp (hL hq)))
  have hbound : ∀ p ∈ L.image (List.take a), ((prefixFiber L a p).card:ℝ) ≤
      K*((1/2:ℝ)^a)^κ*(L.card:ℝ) := by
    intro p hp
    have hb := hball (scalarPathCenter p) ((1/2:ℝ)^a)
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) ha)
      (pow_le_one₀ (by norm_num) (by norm_num))
    rw [hcard] at hb
    exact (scalar_prefix_ball_bound L hL ha p).trans hb
  have hs : (L.card:ℝ) ≤ ((L.image (List.take a)).card:ℝ)*
      (K*((1/2:ℝ)^a)^κ*(L.card:ℝ)) := by
    calc
      _ = ∑ p ∈ L.image (List.take a), ((prefixFiber L a p).card:ℝ) := by
        exact_mod_cast prefixFiber_total_card L a
      _ ≤ ∑ _p ∈ L.image (List.take a), K*((1/2:ℝ)^a)^κ*(L.card:ℝ) :=
        Finset.sum_le_sum hbound
      _ = _ := by simp
  have hpos : 0 < (L.card:ℝ) := by exact_mod_cast hne.card_pos
  nlinarith

 theorem scalar_uniform_prefix_card {M : ℕ} (L : Finset (CellPath 1)) (hne : L.Nonempty)
    (d k : ℕ → ℕ) (hd : Monotone d) (hd0 : d 0 = 0)
    (hcard : ∀ i < M, ∀ p ∈ L.image (List.take (d i)),
      (prefixChildren L (d i) (d (i+1)) p).card = 2^(k i))
    {j : ℕ} (hj : j ≤ M) :
    (L.image (List.take (d j))).card = 2^(∑ i ∈ Finset.range j, k i) := by
  classical
  obtain ⟨q,hq⟩ := hne
  have hp : ([] : CellPath 1) ∈ L.image (List.take (d 0)) := by
    rw [hd0]
    exact Finset.mem_image.mpr ⟨q,hq,rfl⟩
  have hh := scalar_grouped_children_card L d k hd M hcard (Nat.zero_le j) hj [] hp
  simpa only [hd0,prefixChildren,prefixFiber_zero,Nat.Ico_zero_eq_range] using hh

end Falconer.Regularization

end OAI

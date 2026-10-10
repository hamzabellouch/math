import OAI.MeasureTheory.Falconer.Estimates.ScalarGroupedPaths

namespace OAI

/-! Exact masses of terminal fibers before bunching. -/
namespace Falconer.Regularization

 theorem scalar_uniform_terminal_mass {N M t : ℕ} (L : Finset (CellPath 1))
    (hL : L ⊆ cubePaths 1 N) (d k : ℕ → ℕ) (hd : Monotone d) (hdM : d M = N)
    (hcard : ∀ i < M, ∀ p ∈ L.image (List.take (d i)),
      (prefixChildren L (d i) (d (i+1)) p).card = 2^(k i))
    (ht : t ≤ M) : ∀ p ∈ L.image (List.take (d t)),
      (prefixFiber L (d t) p).card = 2^(∑ i ∈ Finset.Ico t M, k i) := by
  classical
  intro p hp
  have hc := scalar_grouped_children_card L d k hd M hcard ht le_rfl p hp
  rw [hdM] at hc
  have hi : (prefixFiber L (d t) p).image (List.take N) = prefixFiber L (d t) p := by
    calc
      _ = (prefixFiber L (d t) p).image id := Finset.image_congr (by
        intro q hq
        have hn := (mem_cubePaths 1 N q).mp (hL (Finset.mem_filter.mp hq).1)
        change q.take N = q
        rw [← hn,List.take_length])
      _ = _ := Finset.image_id
  change ((prefixFiber L (d t) p).image (List.take N)).card = _ at hc
  rwa [hi] at hc

end Falconer.Regularization

end OAI

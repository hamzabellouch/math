import Mathlib
import OAI.Computability.VertexCover.Analysis.ListMassHitMaximum

namespace OAI

section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
section
namespace VertexCover.LabelCover

theorem incidence_unused (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    (I : Finset (Φ.Coordinate d)) (j : Fin d) (k : Fin (Φ.WeightDimension d))
    (hk : ∀ a : (Φ.query seed j).LocalLabel, (Φ.query seed j).slot a ≠ k) :
    Φ.incidence seed I j k = 0 := by
  simp only [incidence, truthValue]
  rw [ite_eq_right (fun ⟨a, _, h⟩ => hk a h)]

theorem hull_block_bound (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    {g : Fin d → Fin (Φ.WeightDimension d) → ℝ}
    (hg : g ∈ Φ.incidenceHull seed) (j : Fin d) : ∑ k, |g j k| ≤ 1 := by
  classical
  have hc : Convex ℝ {g : Fin d → Fin (Φ.WeightDimension d) → ℝ |
      ∑ k, |g j k| ≤ 1} := by
    intro x hx y hy a b ha hb hab
    change ∑ k, |a*x j k+b*y j k| ≤ 1
    calc
      _ ≤ ∑ k, (a*|x j k|+b*|y j k|) := by
        apply Finset.sum_le_sum; intro k hk
        simpa only [abs_mul, abs_of_nonneg ha, abs_of_nonneg hb] using
          abs_add_le (a*x j k) (b*y j k)
      _ = a*(∑ k, |x j k|)+b*(∑ k, |y j k|) := by
        simp [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ a*1+b*1 := add_le_add (mul_le_mul_of_nonneg_left hx ha)
        (mul_le_mul_of_nonneg_left hy hb)
      _ = 1 := by simpa using hab
  apply convexHull_min (t := {g : Fin d → Fin (Φ.WeightDimension d) → ℝ |
    ∑ k, |g j k| ≤ 1}) ?_ hc hg
  rintro z ⟨I, hI, rfl | rfl⟩
  · exact Φ.incidence_block_bound seed hI j
  · simpa using Φ.incidence_block_bound seed hI j

theorem hull_unused (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d)
    {g : Fin d → Fin (Φ.WeightDimension d) → ℝ}
    (hg : g ∈ Φ.incidenceHull seed) (j : Fin d) (k : Fin (Φ.WeightDimension d))
    (hk : ∀ a : (Φ.query seed j).LocalLabel, (Φ.query seed j).slot a ≠ k) :
    g j k = 0 := by
  classical
  have hc : Convex ℝ {g : Fin d → Fin (Φ.WeightDimension d) → ℝ | g j k = 0} := by
    intro x hx y hy a b ha hb hab
    change a*x j k+b*y j k = 0
    change x j k = 0 at hx
    change y j k = 0 at hy
    rw [hx, hy]; ring
  apply convexHull_min (t := {g : Fin d → Fin (Φ.WeightDimension d) → ℝ |
    g j k = 0}) ?_ hc hg
  rintro z ⟨I, hI, rfl | rfl⟩
  · exact Φ.incidence_unused seed I j k hk
  · change -Φ.incidence seed I j k = 0
    rw [Φ.incidence_unused seed I j k hk, neg_zero]

theorem zero_mem_incidenceHull (Φ : LabelCover) {d : ℕ} (seed : Φ.Seeds d) :
    (0 : Fin d → Fin (Φ.WeightDimension d) → ℝ) ∈ Φ.incidenceHull seed := by
  classical
  apply subset_convexHull ℝ _
  refine ⟨∅, Φ.compatible_empty d, Or.inl ?_⟩
  ext j k
  simp [incidence, truthValue]

end VertexCover.LabelCover


end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end OAI

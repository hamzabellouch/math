import OAI.Analysis.LipschitzHilbert.Trees.FiniteLineGrid

namespace OAI

/-! Countably many actual finite line meshes cover a reference line. -/

noncomputable section

open Set MeasureTheory

namespace LipschitzHilbert

def tiledLineGrid (origin H : ℝ) (hH : 0 < H) (G N : ℕ) (hG : 0 < G)
    (k : ℤ) : FiniteLineGrid where
  branching := G
  branching_pos := hG
  origin := origin + k * H
  width := H
  width_pos := hH
  depth := N

theorem tiledLineGrid_root (origin H : ℝ) (hH : 0 < H) (G N : ℕ) (hG : 0 < G)
    (k : ℤ) :
    (tiledLineGrid origin H hH G N hG k).root =
      Ico (origin + k * H) (origin + (k + 1 : ℤ) * H) := by
  unfold FiniteLineGrid.root tiledLineGrid
  congr 1
  push_cast
  ring

theorem tiledLineGrid_measurable (origin H : ℝ) (hH : 0 < H) (G N : ℕ) (hG : 0 < G)
    (k : ℤ) : MeasurableSet (tiledLineGrid origin H hH G N hG k).root := measurableSet_Ico

theorem tiledLineGrid_pairwise_disjoint (origin H : ℝ) (hH : 0 < H) (G N : ℕ)
    (hG : 0 < G) :
    Pairwise fun i j => Disjoint (tiledLineGrid origin H hH G N hG i).root
      (tiledLineGrid origin H hH G N hG j).root := by
  intro i j hij
  simp only [tiledLineGrid_root]
  apply Set.disjoint_left.mpr
  intro x hi hj
  rcases lt_or_gt_of_ne hij with h | h
  · have hc : (i : ℝ) + 1 ≤ j := by exact_mod_cast (show i + 1 ≤ j by omega)
    push_cast at hi hj
    have hm := mul_le_mul_of_nonneg_right hc hH.le
    linarith [hi.2, hj.1]
  · have hc : (j : ℝ) + 1 ≤ i := by exact_mod_cast (show j + 1 ≤ i by omega)
    push_cast at hi hj
    have hm := mul_le_mul_of_nonneg_right hc hH.le
    linarith [hj.2, hi.1]

theorem tiledLineGrid_cover (origin H : ℝ) (hH : 0 < H) (G N : ℕ) (hG : 0 < G) :
    (⋃ k : ℤ, (tiledLineGrid origin H hH G N hG k).root) = univ := by
  apply Set.eq_univ_of_forall
  intro x
  apply Set.mem_iUnion.mpr
  refine ⟨⌊(x - origin) / H⌋, ?_⟩
  rw [tiledLineGrid_root]
  have hl := mul_le_mul_of_nonneg_right (Int.floor_le ((x - origin) / H)) hH.le
  have hr := mul_lt_mul_of_pos_right (Int.lt_floor_add_one ((x - origin) / H)) hH
  rw [div_mul_cancel₀ _ hH.ne'] at hl hr
  push_cast
  constructor <;> linarith

end LipschitzHilbert

end

end OAI

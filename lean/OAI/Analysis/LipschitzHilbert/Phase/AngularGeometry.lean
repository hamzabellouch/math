import OAI.Analysis.LipschitzHilbert.Phase.AngularGrid

namespace OAI

/-! Geometric separation in the actual translated angular grid. -/

noncomputable section

namespace LipschitzHilbert.AngularGrid

def width (g : AngularGrid) (level : ℕ) : ℝ := g.rootWidth / (g.branching : ℝ) ^ level

def left (g : AngularGrid) (level : ℕ) (cell : ℤ) : ℝ :=
  g.origin + g.width level * cell

def center (g : AngularGrid) (level : ℕ) (cell : ℤ) : ℝ :=
  g.left level cell + g.width level / 2

theorem width_pos (g : AngularGrid) (level : ℕ) : 0 < g.width level := by
  have hG : (0 : ℝ) < g.branching := by
    exact_mod_cast (show 0 < g.branching by have h := g.branching_ge_two; omega)
  exact div_pos g.rootWidth_pos (pow_pos hG level)

/-- The floor assignment is exactly the half-open translated interval. -/
theorem slope_mem_cell (g : AngularGrid) (level : ℕ) (slope : ℝ) :
    g.left level (g.index level slope) ≤ slope ∧
      slope < g.left level (g.index level slope) + g.width level := by
  let a := ((slope - g.origin) / g.rootWidth) * (g.branching : ℝ) ^ level
  have hlow := Int.floor_le a
  have hhigh := Int.lt_floor_add_one a
  have heq : g.width level * a = slope - g.origin := by
    unfold width a
    have hG : (g.branching : ℝ) ≠ 0 := by
      exact_mod_cast (show g.branching ≠ 0 by have h := g.branching_ge_two; omega)
    field_simp [g.rootWidth_pos.ne', pow_ne_zero level hG]
  have hlow' := mul_le_mul_of_nonneg_left hlow (g.width_pos level).le
  have hhigh' := mul_lt_mul_of_pos_left hhigh (g.width_pos level)
  rw [heq] at hlow' hhigh'
  change g.origin + g.width level * (⌊a⌋ : ℝ) ≤ slope ∧
    slope < g.origin + g.width level * (⌊a⌋ : ℝ) + g.width level
  constructor <;> nlinarith

theorem slope_dist_center_le (g : AngularGrid) (level : ℕ) (slope : ℝ) :
    |slope - g.center level (g.index level slope)| ≤ g.width level / 2 := by
  obtain ⟨hl, hr⟩ := g.slope_mem_cell level slope
  unfold center
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem same_cell_diameter (g : AngularGrid) (level : ℕ) {s t : ℝ}
    (hcell : g.index level s = g.index level t) : |s - t| ≤ g.width level := by
  obtain ⟨hs0, hs1⟩ := g.slope_mem_cell level s
  obtain ⟨ht0, ht1⟩ := g.slope_mem_cell level t
  rw [hcell] at hs0 hs1
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem eligible_iff_precision_le (g : AngularGrid) (cutoff precision : ℝ) (level : ℕ) :
    g.eligible cutoff precision level ↔ precision ≤ cutoff / (g.branching : ℝ) ^ level := by
  have hG : (0 : ℝ) < g.branching := by
    exact_mod_cast (show 0 < g.branching by have h := g.branching_ge_two; omega)
  exact (le_div_iff₀ (pow_pos hG level)).symm

def neighbors (g : AngularGrid) (level : ℕ) (gap : ℝ) (i j : ℤ) : Prop :=
  |g.center level i - g.center level j| < gap + g.width level

theorem neighbors_symmetric (g : AngularGrid) (level : ℕ) (gap : ℝ) :
    ∀ ⦃i j⦄, g.neighbors level gap i j → g.neighbors level gap j i := by
  intro i j h
  simpa only [neighbors, abs_sub_comm] using h

/-- Non-neighboring cells separate every pair of slopes they contain. -/
theorem slopes_separated_of_not_neighbors (g : AngularGrid) (level : ℕ)
    (gap s t : ℝ) (hfar : ¬g.neighbors level gap (g.index level s) (g.index level t)) :
    gap ≤ |s - t| := by
  have hcenters : gap + g.width level ≤
      |g.center level (g.index level s) - g.center level (g.index level t)| :=
    le_of_not_gt hfar
  have hs := g.slope_dist_center_le level s
  have ht := g.slope_dist_center_le level t
  have htriangle : |g.center level (g.index level s) - g.center level (g.index level t)| ≤
      |s - g.center level (g.index level s)| + |s - t| +
        |t - g.center level (g.index level t)| := by
    calc
      _ = |(g.center level (g.index level s) - s) + (s - t) +
          (t - g.center level (g.index level t))| := by congr 1; ring
      _ ≤ |(g.center level (g.index level s) - s) + (s - t)| +
          |t - g.center level (g.index level t)| := abs_add_le _ _
      _ ≤ (|g.center level (g.index level s) - s| + |s - t|) +
          |t - g.center level (g.index level t)| :=
        add_le_add (abs_add_le _ _) le_rfl
      _ = _ := by rw [abs_sub_comm (g.center level (g.index level s)) s]
  linarith

theorem centers_separated_of_not_neighbors (g : AngularGrid) (level : ℕ)
    (gap : ℝ) {i j : ℤ} (hfar : ¬g.neighbors level gap i j) :
    gap ≤ |g.center level i - g.center level j| := by
  have h := le_of_not_gt hfar
  have hw := g.width_pos level
  linarith

/-- The actual carrier frequencies inherit separation in each Hilbert
component from non-neighboring angular cells. -/
theorem carrier_frequency_separated (g : AngularGrid) (level : ℕ)
    {gap ηmin η s : ℝ} (hηmin : 0 ≤ ηmin) (hη : ηmin ≤ |η|)
    {i j : ℤ} (hfar : ¬g.neighbors level gap i j) :
    gap * ηmin ≤ |(s - g.center level i) * η - (s - g.center level j) * η| := by
  have hc := g.centers_separated_of_not_neighbors level gap hfar
  calc
    gap * ηmin ≤ |g.center level i - g.center level j| * |η| :=
      mul_le_mul hc hη hηmin (abs_nonneg _)
    _ = _ := by
      rw [← abs_mul]
      have heq : (s - g.center level i) * η - (s - g.center level j) * η =
          -((g.center level i - g.center level j) * η) := by ring
      rw [heq, abs_neg]

end LipschitzHilbert.AngularGrid

end

end OAI

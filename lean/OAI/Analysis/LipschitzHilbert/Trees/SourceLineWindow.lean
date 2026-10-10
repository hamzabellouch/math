import OAI.Analysis.LipschitzHilbert.Fourier.FiniteLineCells

namespace OAI

/-! An actual coarse line cell carries a local grid with exactly the same
fine partitions as the global line grid. This identifies the local
prediction factors before they are patched over coarse cells. -/

noncomputable section
open Set
namespace LipschitzHilbert.FiniteLineGrid

def lineWindow (g : FiniteLineGrid) (coarse i depth : ℕ) : FiniteLineGrid where
  branching := g.branching
  branching_pos := g.branching_pos
  origin := g.origin+g.meshWidth coarse*i
  width := g.meshWidth coarse
  width_pos := g.meshWidth_pos coarse
  depth := depth

theorem lineWindow_root (g : FiniteLineGrid) (coarse i depth : ℕ) :
    (g.lineWindow coarse i depth).root = g.cell coarse i := by
  change Ico (g.origin+g.meshWidth coarse*i)
      ((g.origin+g.meshWidth coarse*i)+g.meshWidth coarse) =
    Ico (g.origin+g.meshWidth coarse*i) (g.origin+g.meshWidth coarse*((i:ℝ)+1))
  congr 1
  ring

theorem lineWindow_meshWidth (g : FiniteLineGrid) (coarse i depth k : ℕ) :
    (g.lineWindow coarse i depth).meshWidth k = g.meshWidth (coarse+k) := by
  simp only [meshWidth,lineWindow,pow_add,div_div]

/-- The local normalized coordinate differs from the global one by an
integer number of fine cells, with the same integer branching power. -/
theorem lineWindow_coordinate (g : FiniteLineGrid) (coarse i depth k : ℕ) (x : ℝ) :
    ((x-(g.lineWindow coarse i depth).origin)/(g.lineWindow coarse i depth).width)*
        ((g.lineWindow coarse i depth).branching:ℝ)^k+
      ((i*g.branching^k:ℕ):ℝ) =
        ((x-g.origin)/g.width)*(g.branching:ℝ)^(coarse+k) := by
  have hG : (g.branching:ℝ) ≠ 0 := by exact_mod_cast g.branching_pos.ne'
  simp only [lineWindow,meshWidth,Nat.cast_mul,Nat.cast_pow,pow_add]
  field_simp [g.width_pos.ne',hG]
  ring

theorem lineWindow_rawIndex (g : FiniteLineGrid) (coarse i depth k : ℕ)
    (hi : i < g.branching^coarse) {x : ℝ} (hx : x ∈ g.cell coarse i) :
    (g.lineWindow coarse i depth).rawIndex k x+i*g.branching^k =
      g.rawIndex (coarse+k) x := by
  classical
  have hlocal : x ∈ (g.lineWindow coarse i depth).root := by
    rwa [g.lineWindow_root]
  have hglobal : x ∈ g.root := g.cell_subset_root coarse hi hx
  have hcoord : 0 ≤ ((x-(g.lineWindow coarse i depth).origin)/
      (g.lineWindow coarse i depth).width)*((g.lineWindow coarse i depth).branching:ℝ)^k := by
    exact mul_nonneg
      (div_nonneg (sub_nonneg.mpr hlocal.1) (g.lineWindow coarse i depth).width_pos.le)
      (pow_nonneg (Nat.cast_nonneg _) _)
  rw [rawIndex,ite_eq_left hlocal,rawIndex,ite_eq_left hglobal,
    ← Nat.floor_add_natCast hcoord,g.lineWindow_coordinate]

/-- On the coarse cell, equality of the actual global fine indices is
exactly strong enough to preserve a local prediction's constancy. -/
theorem lineWindow_index_of_global (g : FiniteLineGrid) (coarse i depth k : ℕ)
    (hi : i < g.branching^coarse) (hk : k ≤ depth) (hglobal : coarse+k ≤ g.depth)
    {x y : ℝ} (hx : x ∈ g.cell coarse i) (hy : y ∈ g.cell coarse i)
    (hxy : g.index (coarse+k) x = g.index (coarse+k) y) :
    (g.lineWindow coarse i depth).index k x = (g.lineWindow coarse i depth).index k y := by
  have hv := congrArg Fin.val hxy
  change g.rawIndex (min (coarse+k) g.depth) x =
    g.rawIndex (min (coarse+k) g.depth) y at hv
  rw [Nat.min_eq_left hglobal] at hv
  have hix := g.lineWindow_rawIndex coarse i depth k hi hx
  have hiy := g.lineWindow_rawIndex coarse i depth k hi hy
  apply Fin.ext
  change (g.lineWindow coarse i depth).rawIndex (min k depth) x =
    (g.lineWindow coarse i depth).rawIndex (min k depth) y
  rw [Nat.min_eq_left hk]
  omega

/-- The converse also holds, so local and global partitions agree exactly
after restricting them to the selected coarse cell. -/
theorem lineWindow_index_iff_global (g : FiniteLineGrid) (coarse i depth k : ℕ)
    (hi : i < g.branching^coarse) (hk : k ≤ depth) (hglobal : coarse+k ≤ g.depth)
    {x y : ℝ} (hx : x ∈ g.cell coarse i) (hy : y ∈ g.cell coarse i) :
    (g.lineWindow coarse i depth).index k x = (g.lineWindow coarse i depth).index k y ↔
      g.index (coarse+k) x = g.index (coarse+k) y := by
  refine ⟨?_,g.lineWindow_index_of_global coarse i depth k hi hk hglobal hx hy⟩
  intro hxy
  have hv := congrArg Fin.val hxy
  change (g.lineWindow coarse i depth).rawIndex (min k depth) x =
    (g.lineWindow coarse i depth).rawIndex (min k depth) y at hv
  rw [Nat.min_eq_left hk] at hv
  apply Fin.ext
  change g.rawIndex (min (coarse+k) g.depth) x = g.rawIndex (min (coarse+k) g.depth) y
  rw [Nat.min_eq_left hglobal]
  rw [← g.lineWindow_rawIndex coarse i depth k hi hx,
    ← g.lineWindow_rawIndex coarse i depth k hi hy,hv]

end LipschitzHilbert.FiniteLineGrid

end

end OAI

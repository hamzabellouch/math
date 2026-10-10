import OAI.Analysis.LipschitzHilbert.Estimates.NestedAverage
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Algebra.Order.Floor.Semifield

namespace OAI

/-! Actual finite line partitions, nested at an integer branching ratio. -/

noncomputable section

open Set MeasureTheory

namespace LipschitzHilbert

structure FiniteLineGrid where
  branching : ℕ
  branching_pos : 0 < branching
  origin : ℝ
  width : ℝ
  width_pos : 0 < width
  depth : ℕ

namespace FiniteLineGrid

attribute [local instance] Classical.propDecidable

def root (g : FiniteLineGrid) : Set ℝ := Ico g.origin (g.origin + g.width)

def rawIndex (g : FiniteLineGrid) (level : ℕ) (x : ℝ) : ℕ :=
  if x ∈ g.root then ⌊((x - g.origin) / g.width) * (g.branching : ℝ) ^ level⌋₊ else 0

theorem rawIndex_lt (g : FiniteLineGrid) {level : ℕ} (hlevel : level ≤ g.depth) (x : ℝ) :
    g.rawIndex level x < g.branching ^ g.depth := by
  classical
  have hG : 0 < (g.branching : ℝ) := by exact_mod_cast g.branching_pos
  by_cases hx : x ∈ g.root
  · have hzero : 0 ≤ (x - g.origin) / g.width :=
      div_nonneg (sub_nonneg.mpr hx.1) g.width_pos.le
    have hone : (x - g.origin) / g.width < 1 := by
      rw [div_lt_one g.width_pos]
      exact sub_lt_iff_lt_add.mpr (by simpa only [add_comm] using hx.2)
    have hp : 0 < (g.branching : ℝ) ^ level := pow_pos hG _
    have hlt : ⌊((x - g.origin) / g.width) * (g.branching : ℝ) ^ level⌋₊ <
        g.branching ^ level := by
      rw [Nat.floor_lt (mul_nonneg hzero hp.le), Nat.cast_pow]
      simpa only [one_mul] using mul_lt_mul_of_pos_right hone hp
    rw [rawIndex, ite_eq_left hx]
    exact hlt.trans_le (Nat.pow_le_pow_right g.branching_pos hlevel)
  · simpa only [rawIndex, ite_eq_right hx] using pow_pos g.branching_pos g.depth

def index (g : FiniteLineGrid) (level : ℕ) (x : ℝ) : Fin (g.branching ^ g.depth) :=
  ⟨g.rawIndex (min level g.depth) x, g.rawIndex_lt (Nat.min_le_right _ _) x⟩

def parent (g : FiniteLineGrid) (i : Fin (g.branching ^ g.depth)) :
    Fin (g.branching ^ g.depth) :=
  ⟨i.val / g.branching, (Nat.div_le_self _ _).trans_lt i.isLt⟩

theorem rawIndex_parent (g : FiniteLineGrid) (level : ℕ) (x : ℝ) :
    g.rawIndex (level + 1) x / g.branching = g.rawIndex level x := by
  classical
  by_cases hx : x ∈ g.root
  · simp only [rawIndex, ite_eq_left hx]
    rw [← Nat.floor_div_natCast]
    congr 1
    rw [pow_succ]
    have hG : (g.branching : ℝ) ≠ 0 := by exact_mod_cast g.branching_pos.ne'
    field_simp
  · simp [rawIndex, hx]

/-- The partitions refine on the entire line, including outside the root. -/
theorem index_parent (g : FiniteLineGrid) {level : ℕ} (hlevel : level < g.depth) (x : ℝ) :
    g.index level x = g.parent (g.index (level + 1) x) := by
  apply Fin.ext
  change g.rawIndex (min level g.depth) x =
    g.rawIndex (min (level + 1) g.depth) x / g.branching
  rw [Nat.min_eq_left hlevel.le, Nat.min_eq_left (Nat.succ_le_of_lt hlevel)]
  exact (g.rawIndex_parent level x).symm

theorem measurable_rawIndex (g : FiniteLineGrid) (level : ℕ) : Measurable (g.rawIndex level) := by
  have h : Measurable (fun x : ℝ =>
      ⌊((x - g.origin) / g.width) * (g.branching : ℝ) ^ level⌋₊) := by fun_prop
  exact Measurable.ite (show MeasurableSet g.root from measurableSet_Ico) h measurable_const

theorem measurable_index_fiber (g : FiniteLineGrid) (level : ℕ)
    (i : Fin (g.branching ^ g.depth)) : MeasurableSet {x | g.index level x = i} := by
  have heq : {x | g.index level x = i} =
      {x | g.rawIndex (min level g.depth) x = i.val} := by
    ext x
    exact ⟨fun h => congrArg Fin.val h, fun h => Fin.ext h⟩
  rw [heq]
  exact (g.measurable_rawIndex _) (measurableSet_singleton _)

/-- Two points of one finer cell differ by at most its mesh width. -/
theorem same_index_distance (g : FiniteLineGrid) {level : ℕ} (hlevel : level ≤ g.depth)
    {x y : ℝ} (hx : x ∈ g.root) (hy : y ∈ g.root)
    (hxy : g.index level x = g.index level y) :
    |x - y| ≤ g.width / (g.branching : ℝ) ^ level := by
  have hG : 0 < (g.branching : ℝ) := by exact_mod_cast g.branching_pos
  have hp : 0 < (g.branching : ℝ) ^ level := pow_pos hG _
  have hxn : 0 ≤ ((x - g.origin) / g.width) * (g.branching : ℝ) ^ level :=
    mul_nonneg (div_nonneg (sub_nonneg.mpr hx.1) g.width_pos.le) hp.le
  have hyn : 0 ≤ ((y - g.origin) / g.width) * (g.branching : ℝ) ^ level :=
    mul_nonneg (div_nonneg (sub_nonneg.mpr hy.1) g.width_pos.le) hp.le
  have hf : ⌊((x - g.origin) / g.width) * (g.branching : ℝ) ^ level⌋₊ =
      ⌊((y - g.origin) / g.width) * (g.branching : ℝ) ^ level⌋₊ := by
    have h := congrArg Fin.val hxy
    simpa only [index, Nat.min_eq_left hlevel, rawIndex, ite_eq_left hx, ite_eq_left hy] using h
  have hxlo := Nat.floor_le hxn
  have hylo := Nat.floor_le hyn
  have hxhi := Nat.lt_floor_add_one (((x - g.origin) / g.width) * (g.branching : ℝ) ^ level)
  have hyhi := Nat.lt_floor_add_one (((y - g.origin) / g.width) * (g.branching : ℝ) ^ level)
  rw [hf] at hxlo hxhi
  have hnorm : |((x - g.origin) / g.width) * (g.branching : ℝ) ^ level -
      ((y - g.origin) / g.width) * (g.branching : ℝ) ^ level| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  have heq : ((x - g.origin) / g.width) * (g.branching : ℝ) ^ level -
      ((y - g.origin) / g.width) * (g.branching : ℝ) ^ level =
      (x - y) * ((g.branching : ℝ) ^ level / g.width) := by ring
  rw [heq, abs_mul, abs_of_pos (div_pos hp g.width_pos)] at hnorm
  apply (le_div_iff₀ hp).mpr
  have h := mul_le_mul_of_nonneg_right hnorm g.width_pos.le
  calc
    |x - y| * (g.branching : ℝ) ^ level =
        (|x - y| * ((g.branching : ℝ) ^ level / g.width)) * g.width := by
          field_simp [g.width_pos.ne']
    _ ≤ 1 * g.width := h
    _ = g.width := one_mul _

end FiniteLineGrid
end LipschitzHilbert

end

end OAI

import OAI.Analysis.LipschitzHilbert.Phase.AngularGeometry
import Mathlib.Algebra.Field.NegOnePow
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace OAI

/-! The nested alternating one-third grids in the line-counting argument. -/

noncomputable section

open Set

namespace LipschitzHilbert.DyadicLineGrid

def scale (k : ℤ) : ℝ := (2 : ℝ) ^ k

def shift (q k : ℤ) : ℝ := ((k.negOnePow : ℤ) * q : ℤ) / (3 : ℝ)

def left (q k j : ℤ) : ℝ := scale k * (j + shift q k)

def cell (q k j : ℤ) : Set ℝ := Ico (left q k j) (left q k (j + 1))

def parent (q k j : ℤ) : ℤ := (j + (k.negOnePow : ℤ) * q) / 2

def index (q k : ℤ) (x : ℝ) : ℤ := ⌊x / scale k - shift q k⌋

theorem scale_pos (k : ℤ) : 0 < scale k := zpow_pos (by norm_num) k

theorem scale_succ (k : ℤ) : scale (k + 1) = 2 * scale k := by
  simp only [scale, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
  ring

theorem shift_succ (q k : ℤ) : shift q (k + 1) = -shift q k := by
  simp only [shift, Int.negOnePow_succ, Units.val_neg, Int.cast_neg, Int.cast_mul]
  ring

/-- Every point has the usual unique half-open floor cell. -/
theorem mem_index_cell (q k : ℤ) (x : ℝ) : x ∈ cell q k (index q k x) := by
  have hl := Int.floor_le (x / scale k - shift q k)
  have hr := Int.lt_floor_add_one (x / scale k - shift q k)
  have hs := scale_pos k
  have hmul := mul_le_mul_of_nonneg_left hl hs.le
  have hmul' := mul_lt_mul_of_pos_left hr hs
  have heq : scale k * (x / scale k - shift q k) = x - scale k * shift q k := by
    field_simp [hs.ne']
  rw [heq] at hmul hmul'
  change scale k * (index q k x + shift q k) ≤ x ∧
    x < scale k * ((index q k x + 1 : ℤ) + shift q k)
  push_cast
  dsimp only [index]
  constructor <;> nlinarith

/-- The alternating shift gives actual nesting at successive dyadic scales. -/
theorem cell_subset_parent (q k j : ℤ) : cell q k j ⊆ cell q (k + 1) (parent q k j) := by
  have hmod0 := Int.emod_nonneg (j + (k.negOnePow : ℤ) * q) (by norm_num : (2 : ℤ) ≠ 0)
  have hmod2 := Int.emod_lt_of_pos (j + (k.negOnePow : ℤ) * q) (by norm_num : (0 : ℤ) < 2)
  have hdiv := Int.emod_add_ediv_mul (j + (k.negOnePow : ℤ) * q) 2
  have hlo : 2 * parent q k j ≤ j + (k.negOnePow : ℤ) * q := by
    unfold parent
    omega
  have hhi : j + (k.negOnePow : ℤ) * q + 1 ≤ 2 * parent q k j + 2 := by
    unfold parent
    omega
  have hlo' : (2 : ℝ) * parent q k j ≤ (j : ℝ) + ((k.negOnePow : ℤ) * q : ℤ) := by
    exact_mod_cast hlo
  have hhi' : (j : ℝ) + ((k.negOnePow : ℤ) * q : ℤ) + 1 ≤ 2 * parent q k j + 2 := by
    exact_mod_cast hhi
  push_cast at hlo' hhi'
  have hs := scale_pos k
  have hmlo := mul_le_mul_of_nonneg_left hlo' hs.le
  have hmhi := mul_le_mul_of_nonneg_left hhi' hs.le
  have hleft : left q (k + 1) (parent q k j) ≤ left q k j := by
    unfold left
    rw [scale_succ, shift_succ]
    unfold shift
    push_cast
    nlinarith
  have hright : left q k (j + 1) ≤ left q (k + 1) (parent q k j + 1) := by
    unfold left
    rw [scale_succ, shift_succ]
    unfold shift
    push_cast
    nlinarith
  intro x hx
  exact ⟨hleft.trans hx.1, hx.2.trans_le hright⟩

theorem cells_disjoint (q k : ℤ) {i j : ℤ} (hij : i ≠ j) :
    Disjoint (cell q k i) (cell q k j) := by
  apply Set.disjoint_left.mpr
  intro x hi hj
  have hs := scale_pos k
  change scale k * ((i : ℝ) + shift q k) ≤ x ∧
    x < scale k * (((i + 1 : ℤ) : ℝ) + shift q k) at hi
  change scale k * ((j : ℝ) + shift q k) ≤ x ∧
    x < scale k * (((j + 1 : ℤ) : ℝ) + shift q k) at hj
  rcases lt_or_gt_of_ne hij with h | h
  · have hc : (i : ℝ) + 1 ≤ j := by exact_mod_cast (show i + 1 ≤ j by omega)
    push_cast at hi hj
    nlinarith
  · have hc : (j : ℝ) + 1 ≤ i := by exact_mod_cast (show j + 1 ≤ i by omega)
    push_cast at hi hj
    nlinarith

theorem cell_measurable (q k j : ℤ) : MeasurableSet (cell q k j) := measurableSet_Ico

theorem cell_length (q k j : ℤ) : MeasureTheory.volume.real (cell q k j) = scale k := by
  rw [cell, Real.volume_real_Ico_of_le]
  · unfold left
    push_cast
    ring
  · unfold left
    have hs := scale_pos k
    push_cast
    nlinarith

end LipschitzHilbert.DyadicLineGrid

end

end OAI

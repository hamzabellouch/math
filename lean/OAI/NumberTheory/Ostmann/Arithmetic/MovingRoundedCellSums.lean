import Mathlib.Data.List.Forall2
import OAI.NumberTheory.Ostmann.Arithmetic.MovingCompensationTargets

namespace OAI

/-! # The endpoint loss of rounded top and compensation cells -/

namespace Ostmann

/-- A compensation type occurs four times in the full initial list. -/
noncomputable def movingSmallCellCenters (top compensation : List ℝ) : List ℝ :=
  top ++ compensation.flatMap (List.replicate 4)

theorem movingSmallCellCenters_length (top compensation : List ℝ) :
    (movingSmallCellCenters top compensation).length = top.length + 4 * compensation.length := by
  induction compensation with
  | nil => simp [movingSmallCellCenters]
  | cons c cs ih =>
    simp only [movingSmallCellCenters, List.flatMap_cons, List.length_append,
      List.length_replicate, List.length_cons] at *
    omega

theorem movingSmallCellCenters_sum (top compensation : List ℝ) :
    (movingSmallCellCenters top compensation).sum = top.sum + 4 * compensation.sum := by
  induction compensation with
  | nil => simp [movingSmallCellCenters]
  | cons c cs ih =>
    simp only [movingSmallCellCenters, List.flatMap_cons, List.sum_append,
      List.sum_replicate, List.sum_cons, nsmul_eq_mul] at *
    norm_num at *
    linarith

theorem movingCompensationCenters_error (E : ℝ) (centers targets : List ℝ)
    (h : List.Forall₂ (fun c w => |4 * c - w| ≤ 4 * E) centers targets) :
    |4 * centers.sum - targets.sum| ≤ 4 * E * centers.length := by
  induction h with
  | nil => simp
  | @cons c w cs ws hcw hrest ih =>
    simp only [List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    calc
      |4 * (c + cs.sum) - (w + ws.sum)| =
          |(4 * c - w) + (4 * cs.sum - ws.sum)| := by congr 1; ring
      _ ≤ |4 * c - w| + |4 * cs.sum - ws.sum| := abs_add_le _ _
      _ ≤ 4 * E * ((cs.length : ℝ) + 1) := by linarith

/-- Replacing each center by the bottom of its width-two cell loses exactly
one per slot, in addition to the top and compensation rounding errors. -/
theorem movingSmallCellCenters_lower (J cb E et : ℝ)
    (top centers targets : List ℝ)
    (htop : J - et ≤ top.sum + cb)
    (hcomp : List.Forall₂ (fun c w => |4 * c - w| ≤ 4 * E) centers targets) :
    J + targets.sum - (et + 4 * E * centers.length +
      (top.length + 4 * centers.length : ℕ) + 1) ≤
      ((movingSmallCellCenters top centers).map (fun c => c - 1)).sum + (cb - 1) := by
  have hc := (abs_le.mp (movingCompensationCenters_error E centers targets hcomp)).1
  have hmap (l : List ℝ) : (l.map (fun c => c - 1)).sum = l.sum - l.length := by
    induction l with
    | nil => simp
    | cons c cs ih => simp only [List.map_cons, List.sum_cons, List.length_cons,
        Nat.cast_add, Nat.cast_one, ih]; ring
  rw [hmap, movingSmallCellCenters_sum, movingSmallCellCenters_length]
  linarith

/-- One-sided rounding has no accumulated center error in the lower bound. -/
theorem movingSmallCellCenters_lower_of_le (J cb : ℝ)
    (top centers targets : List ℝ)
    (htop : J ≤ top.sum + cb)
    (hcomp : List.Forall₂ (fun c w => w ≤ 4 * c) centers targets) :
    J + targets.sum - ((top.length + 4 * centers.length : ℕ) + 1) ≤
      ((movingSmallCellCenters top centers).map (fun c => c - 1)).sum + (cb - 1) := by
  have hs : targets.sum ≤ 4 * centers.sum := by
    induction hcomp with
    | nil => simp
    | cons hcw hrest ih => simp only [List.sum_cons]; linarith
  have hmap (l : List ℝ) : (l.map (fun c => c - 1)).sum = l.sum - l.length := by
    induction l with
    | nil => simp
    | cons c cs ih => simp only [List.map_cons, List.sum_cons, List.length_cons,
        Nat.cast_add, Nat.cast_one, ih]; ring
  rw [hmap, movingSmallCellCenters_sum, movingSmallCellCenters_length]
  linarith

/-- The actual repeated cell endpoints satisfy the diagonal gap after paying
for excluded integer centers and one unit per cell endpoint. -/
theorem moving_rounded_cell_diagonal_gap (k n : ℕ)
    (BD Bz C L J cb w b cg : ℝ) (top centers targets : List ℝ)
    (D : Finset ℤ)
    (hC : 0 ≤ C) (hk : 16 * C + 20 ≤ (k : ℝ) ^ 4)
    (hL : (top.length + 4 * centers.length : ℕ) + 9 ≤ L)
    (hD : (D.card : ℝ) ≤ C * L)
    (hcg : cg ≤ (91 / 100 : ℝ) * L)
    (htop : J ≤ top.sum + cb)
    (hcomp : List.Forall₂ (fun c t => t ≤ 4 * c) centers targets)
    (hupper : 4 * b ≤ w + 4 * (D.card + 2))
    (hbalance : (2 ^ n : ℕ) * w = (2 ^ n : ℕ) * (J + targets.sum) -
      spectatorStepGap BD Bz ((k : ℝ) ^ 4) (2 ^ n : ℕ) (spectatorBulkCount k L)) :
    2 * cg + 1 + ((2 ^ n : ℕ) * 4) * b -
        ((2 ^ n : ℕ) * ((movingSmallCellCenters top centers).map (fun c => c - 1)).sum +
          (2 ^ n : ℕ) * (cb - 1)) ≤
      -spectatorStepGap (BD - 1) Bz ((k : ℝ) ^ 4) (2 ^ n : ℕ)
        (spectatorBulkCount k L) := by
  have hL1 : 1 ≤ L := by have h := Nat.cast_nonneg (α := ℝ) (top.length + 4 * centers.length); linarith
  have hr : (0 : ℝ) ≤ (2 ^ n : ℕ) := Nat.cast_nonneg _
  apply moving_cell_diagonal_gap BD Bz ((k : ℝ) ^ 4) (2 ^ n : ℕ)
    (spectatorBulkCount k L) J targets.sum w b cb
    ((2 ^ n : ℕ) * ((movingSmallCellCenters top centers).map (fun c => c - 1)).sum)
    cg (4 * (D.card + 2)) ((top.length + 4 * centers.length : ℕ) + 1)
    hr hbalance hupper
  · have h := mul_le_mul_of_nonneg_left
      (movingSmallCellCenters_lower_of_le J cb top centers targets htop hcomp) hr
    nlinarith only [h]
  · apply moving_linear_cell_error_budget k n (4 * C + 1) L cg
      (4 * (D.card + 2)) ((top.length + 4 * centers.length : ℕ) + 1)
      (by linarith) (by linarith) hL1 hcg
    nlinarith only [hL, hD]

end Ostmann

end OAI

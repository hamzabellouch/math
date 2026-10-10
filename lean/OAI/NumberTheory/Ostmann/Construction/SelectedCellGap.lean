import OAI.NumberTheory.Ostmann.Construction.SelectedCompensationCells
import OAI.NumberTheory.Ostmann.Arithmetic.MovingIndexedCellLower

namespace OAI

/-! # The selected actual cells discharge the diagonal's geometric gap -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def tailCellLinearRate (a C : ℝ) : ℝ :=
  20 + |4 * C + 4 * Real.log 2 + 2 * Real.log 4 / a|

theorem tailCellLinearRate_nonneg (a C : ℝ) : 0 ≤ tailCellLinearRate a C := by
  unfold tailCellLinearRate
  positivity

theorem tailDefectBudget_linear (a C L X : ℝ) (hL : 1 ≤ L)
    (hX : 0 < X) (hXupper : X ≤ Real.exp L) :
    tailDefectBudget a C X ≤ tailCellLinearRate a C * L := by
  have hlog : Real.log X ≤ L := by
    have h := Real.log_le_log hX hXupper
    rwa [Real.log_exp] at h
  have hc := le_abs_self (4 * C + 4 * Real.log 2 + 2 * Real.log 4 / a)
  have hcl := mul_le_mul_of_nonneg_left hL
    (abs_nonneg (4 * C + 4 * Real.log 2 + 2 * Real.log 4 / a))
  unfold tailDefectBudget tailCellLinearRate
  nlinarith only [hlog, hc, hcl]

theorem SelectedSmallTailCell.compensation_upper
    {A B : Set ℕ} {N hi j : ℕ} {a C L X w : ℝ} {D : Finset ℕ}
    (h : SelectedSmallTailCell A B N a C L X hi D (w / 4) j) :
    4 * ((j : ℝ) + 1) ≤ w + 256 * tailDefectBudget a C X + 8 := by
  have hh := h.2.1
  linarith

theorem selected_centers_lower {A B : Set ℕ} {N hi : ℕ}
    {a C L X : ℝ} {D : Finset ℕ} {centers : List ℕ} {targets : List ℝ}
    (h : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L X hi D (w / 4) j) centers targets) :
    List.Forall₂ (fun c w => w ≤ 4 * c) (centers.map (fun (j : ℕ) => (j : ℝ))) targets := by
  induction h with
  | nil => exact .nil
  | cons h hrest ih =>
    apply List.Forall₂.cons _ ih
    have hh := h.1
    dsimp only
    linarith

theorem selected_cell_diagonal_gap
    {A B : Set ℕ} {N hi top pivot : ℕ} {a C L X J cb w cg BD Bz : ℝ}
    {D : Finset ℕ} {centers : List ℕ} {targets : List ℝ} (k n : ℕ)
    (hL : 1 ≤ L) (hX : 0 < X) (hXupper : X ≤ Real.exp L)
    (hk : 1024 * tailCellLinearRate a C + 52 ≤ (k : ℝ) ^ 4)
    (hcount : (7 + 4 * centers.length : ℕ) ≤ L)
    (hcg : cg ≤ (91 / 100 : ℝ) * L)
    (htop : SelectedSmallTailCell A B N a C L X hi D ((J - cb) / 6) top)
    (hpivot : SelectedSmallTailCell A B N a C L X hi D (w / 4) pivot)
    (hcenters : List.Forall₂
      (fun j t => SelectedSmallTailCell A B N a C L X hi D (t / 4) j) centers targets)
    (hbalance : (2 ^ n : ℕ) * w = (2 ^ n : ℕ) * (J + targets.sum) -
      spectatorStepGap BD Bz ((k : ℝ) ^ 4) (2 ^ n : ℕ) (spectatorBulkCount k L)) :
    let small := movingSmallCellCenters (List.replicate 6 (top : ℝ))
      (centers.map (fun (j : ℕ) => (j : ℝ)))
    2 * cg + 1 + ((2 ^ n : ℕ) * 4) * ((pivot : ℝ) + 1) -
        ((∑ i, movingCellLower n small i) + (2 ^ n : ℕ) * (cb - 1)) ≤
      -spectatorStepGap (BD - 1) Bz ((k : ℝ) ^ 4) (2 ^ n : ℕ)
        (spectatorBulkCount k L) := by
  intro small
  rw [movingCellLower_sum]
  have hr : (0 : ℝ) ≤ (2 ^ n : ℕ) := Nat.cast_nonneg _
  have htopSum : J ≤ (List.replicate 6 (top : ℝ)).sum + cb := by
    have hh := htop.1
    simp only [List.sum_replicate, nsmul_eq_mul]
    norm_num
    linarith
  have hlow := movingSmallCellCenters_lower_of_le J cb (List.replicate 6 (top : ℝ))
    (centers.map (fun (j : ℕ) => (j : ℝ))) targets htopSum (selected_centers_lower hcenters)
  simp only [List.length_replicate, List.length_map] at hlow
  apply moving_cell_diagonal_gap BD Bz ((k : ℝ) ^ 4) (2 ^ n : ℕ)
    (spectatorBulkCount k L) J targets.sum w ((pivot : ℝ) + 1) cb
    ((2 ^ n : ℕ) * (small.map (fun c => c - 1)).sum) cg
    (256 * tailDefectBudget a C X + 8) (7 + 4 * centers.length : ℕ)
    hr hbalance (by simpa only [add_assoc] using hpivot.compensation_upper)
  · have hlow' := mul_le_mul_of_nonneg_left hlow hr
    dsimp only [small]
    push_cast at hlow' ⊢
    nlinarith only [hlow']
  · apply moving_linear_cell_error_budget k n (256 * tailCellLinearRate a C + 9) L cg
      (256 * tailDefectBudget a C X + 8) (7 + 4 * centers.length : ℕ)
      (by linarith [tailCellLinearRate_nonneg a C]) (by linarith) hL hcg
    have hE := tailDefectBudget_linear a C L X hL hX hXupper
    nlinarith only [hE, hcount, hL]

end Ostmann

end OAI

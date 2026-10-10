import OAI.NumberTheory.Ostmann.Construction.ScheduledSelectedGaps
import OAI.NumberTheory.Ostmann.Construction.SelectedInitialProductWindow
import OAI.NumberTheory.Ostmann.Arithmetic.MovingProductFrequency

namespace OAI

/-! # The recursive product budget of the actual selected cells -/
namespace Ostmann
open scoped Classical BigOperators

theorem nat_cell_drop_sum (cs : List ℕ) (n : ℕ) :
    ((cs.drop n).map (fun j : ℕ => (j : ℝ))).sum =
      ((cs.drop n).headD 0 : ℝ) + ((cs.drop (n + 1)).map (fun j : ℕ => (j : ℝ))).sum := by
  induction cs generalizing n with
  | nil => simp
  | cons c cs ih =>
    cases n with
    | zero => simp
    | succ n => simpa only [List.drop_succ_cons] using ih n

theorem selected_cell_pivot_exponent (G : ℝ) (cs : List ℕ) (n : ℕ) :
    movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs) n =
      G - 1 + (2 : ℝ) ^ n * 4 * ((cs.drop n).headD 0 : ℝ) := by
  simp only [movingCellPivotExponent, selectedCompensationCenter, add_sub_cancel_right,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

theorem selectedProductExponent_eq (G Y cb cd width Dlog : ℝ) (top : ℕ) (cs : List ℕ) (n : ℕ) :
    movingProductExponent (movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs))
      (Y + selectedInitialLogCenter G Y cb cd top cs + width - Dlog) n =
    2 * (G - 1) + (2 : ℝ) ^ n *
      (2 * cb + 2 * cd - Dlog + 6 * top +
        4 * ((cs.drop n).map (fun j : ℕ => (j : ℝ))).sum + width + 2) := by
  induction n with
  | zero =>
    simp only [movingProductExponent, pow_zero, one_mul, List.drop_zero,
      selectedInitialLogCenter]
    ring
  | succ n ih =>
    rw [movingProductExponent, ih, selected_cell_pivot_exponent, nat_cell_drop_sum cs n,
      pow_succ]
    ring

theorem selectedProductExponent_gap (G Y cb cd width Dlog : ℝ) (top : ℕ) (cs : List ℕ) (n : ℕ) :
    movingProductExponent (movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs))
        (Y + selectedInitialLogCenter G Y cb cd top cs + width - Dlog) n -
      2 * movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs) n =
    (2 : ℝ) ^ n * (2 * cb + 2 * cd - Dlog + 6 * top + width + 2 +
      4 * ((cs.drop (n + 1)).map (fun j : ℕ => (j : ℝ))).sum -
      4 * ((cs.drop n).headD 0 : ℝ)) := by
  rw [selectedProductExponent_eq, selected_cell_pivot_exponent, nat_cell_drop_sum cs n]
  ring

theorem selectedProductExponent_gap_from_diagonal
    (G Y cb cd width Dlog : ℝ) (top : ℕ) (cs : List ℕ) (n : ℕ)
    (hD : Dlog ≤ 2 * cd + 2) (hwidth : 0 ≤ width)
    (hgap : 1 + ((2 ^ n : ℕ) * 4) * (((cs.drop n).headD 0 : ℝ) + 1) -
      ((∑ i, scheduledSmallLower top (cs.drop (n + 1)) n i) +
        (2 ^ n : ℕ) * (2 * cb - 2)) ≤ 0) :
    2 * movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs) n ≤
      movingProductExponent (movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs))
        (Y + selectedInitialLogCenter G Y cb cd top cs + width - Dlog) n := by
  have he := selectedProductExponent_gap G Y cb cd width Dlog top cs n
  rw [scheduledSmallLower_sum] at hgap
  have hs := list_sum_sub_one ((cs.drop (n + 1)).map (fun j : ℕ => (j : ℝ)))
  simp only [List.map_map, Function.comp_def, List.length_map] at hs
  rw [hs] at hgap
  push_cast at hgap
  have hr : 0 ≤ (2 : ℝ) ^ n := by positivity
  have hd := mul_nonneg hr (show 0 ≤ 2 * cd - Dlog + 2 by linarith only [hD])
  have hw := mul_nonneg hr hwidth
  have hl := mul_nonneg hr (Nat.cast_nonneg (cs.drop (n + 1)).length (α := ℝ))
  nlinarith only [he, hgap, hd, hw, hl, hr]

theorem selectedProductExponent_budget
    (G Y cb cd width Dlog : ℝ) (top : ℕ) (cs : List ℕ)
    (hcb : 0 ≤ cb) (hD : Dlog ≤ 2 * cd + 2) (hwidth : 0 ≤ width)
    (hgap : ∀ n < cs.length,
      1 + ((2 ^ n : ℕ) * 4) * (((cs.drop n).headD 0 : ℝ) + 1) -
        ((∑ i, scheduledSmallLower top (cs.drop (n + 1)) n i) +
          (2 ^ n : ℕ) * (2 * cb - 2)) ≤ 0) :
    ∀ n, 2 * movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs) n ≤
      movingProductExponent (movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs))
        (Y + selectedInitialLogCenter G Y cb cd top cs + width - Dlog) n := by
  intro n
  by_cases hn : n < cs.length
  · exact selectedProductExponent_gap_from_diagonal G Y cb cd width Dlog top cs n hD hwidth (hgap n hn)
  · have he := selectedProductExponent_gap G Y cb cd width Dlog top cs n
    have hdrop : cs.drop n = [] := List.drop_eq_nil_of_le (by omega)
    have hdrop' : cs.drop (n + 1) = [] := List.drop_eq_nil_of_le (by omega)
    simp only [hdrop, hdrop', List.map_nil, List.sum_nil, List.headD_nil, Nat.cast_zero,
      mul_zero, add_zero, sub_zero] at he
    have hterm : 0 ≤ 2 * cb + 2 * cd - Dlog + 6 * top + width + 2 := by
      nlinarith only [hD, hcb, hwidth, Nat.cast_nonneg top (α := ℝ)]
    have hnonneg := mul_nonneg (show 0 ≤ (2 : ℝ) ^ n by positivity) hterm
    linarith only [he, hnonneg]

/-- The chosen compensation cells give the actual recursive product budget. -/
theorem selectedProductExponent_budget_of_cells
    {A B : Set ℕ} {N hi top : ℕ} {a C L X J G Y cb cd width Dlog BD Bz : ℝ}
    {D : Finset ℕ} {cs : List ℕ} (k : ℕ)
    (hk0 : 1 ≤ k) (hL : 1 ≤ L) (hX : 0 < X) (hXupper : X ≤ Real.exp L)
    (hk : 1024 * tailCellLinearRate a C + 52 ≤ (k : ℝ) ^ 4)
    (hcount : (8 + 4 * cs.length : ℕ) ≤ L)
    (hcb : 0 ≤ cb) (hD : Dlog ≤ 2 * cd + 2) (hwidth : 0 ≤ width)
    (hBD : 1 ≤ BD) (hBz : 0 ≤ Bz)
    (htop : SelectedSmallTailCell A B N a C L X hi D ((J - 2 * cb) / 6) top)
    (hcs : List.Forall₂
      (fun j t => SelectedSmallTailCell A B N a C L X hi D (t / 4) j)
      cs (movingCompensationTargets J (movingCompensationGaps k BD Bz L))) :
    ∀ n, 2 * movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs) n ≤
      movingProductExponent (movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs))
        (Y + selectedInitialLogCenter G Y cb cd top cs + width - Dlog) n := by
  apply selectedProductExponent_budget G Y cb cd width Dlog top cs hcb hD hwidth
  intro n hn
  have hlen : cs.length = k := by
    simpa only [movingCompensationTargets_length, movingCompensationGaps_length] using
      hcs.length_eq
  have h := selected_scheduled_drop_diagonal_gap k n (by omega) hL hX hXupper hk
    hcount (cg := 0) (by linarith) htop hcs
  have hz : 0 ≤ Real.log ((k : ℝ) ^ 4) :=
    Real.log_nonneg (one_le_pow₀ (by exact_mod_cast hk0))
  have hr : 0 ≤ Real.log (2 ^ n : ℕ) :=
    Real.log_nonneg (by exact_mod_cast (one_le_pow₀ (by norm_num : 1 ≤ (2 : ℕ))))
  have hm : 0 ≤ (spectatorBulkCount k L : ℝ) := Nat.cast_nonneg _
  have hstep : 0 ≤ spectatorStepGap (BD - 1) Bz ((k : ℝ) ^ 4)
      (2 ^ n : ℕ) (spectatorBulkCount k L) := by
    unfold spectatorStepGap
    have hBD' : 0 ≤ BD - 1 := by linarith
    positivity
  simpa only [mul_zero, zero_add] using h.trans (neg_nonpos.mpr hstep)

theorem selected_cell_pivot_nonneg (G : ℝ) (hG : 1 ≤ G) (cs : List ℕ) (n : ℕ) :
    0 ≤ movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs) n := by
  rw [selected_cell_pivot_exponent]
  have hg : 0 ≤ G - 1 := by linarith
  positivity

end Ostmann

end OAI

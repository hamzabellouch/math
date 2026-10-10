import OAI.NumberTheory.Ostmann.Construction.SelectedScheduledProduct
import OAI.NumberTheory.Ostmann.Arithmetic.MovingProductInitialCutoff

namespace OAI

/-! # The actual product schedule satisfies the finite frequency budget -/
namespace Ostmann
open scoped Classical BigOperators

theorem selectedProductExponent_gap_upper
    {A B : Set ℕ} {N hi top : ℕ} {a C L X J G Y cb cd width Dlog BD Bz : ℝ}
    {D : Finset ℕ} {cs : List ℕ} (k n : ℕ) (hn : n < k)
    (hD : 2 * cd - 2 ≤ Dlog)
    (htop : SelectedSmallTailCell A B N a C L X hi D ((J - 2 * cb) / 6) top)
    (hcs : List.Forall₂
      (fun j t => SelectedSmallTailCell A B N a C L X hi D (t / 4) j)
      cs (movingCompensationTargets J (movingCompensationGaps k BD Bz L))) :
    movingProductExponent (movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs))
        (Y + selectedInitialLogCenter G Y cb cd top cs + width - Dlog) n -
      2 * movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs) n ≤
    spectatorStepGap BD Bz ((k : ℝ) ^ 4) (2 ^ n : ℕ) (spectatorBulkCount k L) +
      (2 : ℝ) ^ n * ((6 + 4 * (cs.drop (n + 1)).length) *
        (64 * tailDefectBudget a C X + 1) + width + 4) := by
  have hlen : cs.length = k := by
    simpa only [movingCompensationTargets_length, movingCompensationGaps_length] using
      hcs.length_eq
  have hpivot := (forall₂_headD_drop hcs n (by omega)).1
  have htail := (selected_compensation_centers_sum_bounds
    (List.forall₂_drop (n + 1) hcs)).2
  have htop' := htop.2.1
  have hbalance := movingCompensationTargets_drop_balance J BD Bz L k n hn
  dsimp only at hbalance
  have he := selectedProductExponent_gap G Y cb cd width Dlog top cs n
  have hr : 0 ≤ (2 : ℝ) ^ n := by positivity
  have hp := mul_le_mul_of_nonneg_left hpivot (show 0 ≤ (2 : ℝ) ^ n * 4 by positivity)
  have ht := mul_le_mul_of_nonneg_left htail hr
  have hu := mul_le_mul_of_nonneg_left htop' (show 0 ≤ (2 : ℝ) ^ n * 6 by positivity)
  have hd := mul_le_mul_of_nonneg_left hD hr
  push_cast at hp ht hu hd hbalance ⊢
  nlinarith only [he, hp, ht, hu, hd, hbalance]

/-- Each rounding loss is paid once, in the fixed per-step reserve. -/
theorem selectedProductExponent_gap_budget
    {A B : Set ℕ} {N hi top : ℕ} {a C L X J G Y cb cd width Dlog BD Bz R : ℝ}
    {D : Finset ℕ} {cs : List ℕ} (k n : ℕ) (hk : 2 ≤ k) (hn : n < k)
    (hL : 1 ≤ L) (hR : 0 ≤ R) (hdef0 : 0 ≤ tailDefectBudget a C X)
    (hdef : tailDefectBudget a C X ≤ R * L)
    (hlarge : 14 * (64 * R + 3) ≤ (k : ℝ) ^ 3)
    (hscale : 4 ≤ (k : ℝ) ^ 4 * L)
    (hm : 4 ≤ (spectatorBulkCount k L : ℝ))
    (hwidth : width = 2 * ((initialSmallCellList top cs).length + 3))
    (hD : 2 * cd - 2 ≤ Dlog)
    (htop : SelectedSmallTailCell A B N a C L X hi D ((J - 2 * cb) / 6) top)
    (hcs : List.Forall₂
      (fun j t => SelectedSmallTailCell A B N a C L X hi D (t / 4) j)
      cs (movingCompensationTargets J (movingCompensationGaps k BD Bz L))) :
    movingProductExponent (movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs))
        (Y + selectedInitialLogCenter G Y cb cd top cs + width - Dlog) n -
      2 * movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs) n ≤
    spectatorStepGap (BD + 2) Bz ((k : ℝ) ^ 4) (2 ^ n : ℕ) (spectatorBulkCount k L) := by
  have hlen : cs.length = k := by
    simpa only [movingCompensationTargets_length, movingCompensationGaps_length] using
      hcs.length_eq
  have hround := initial_cell_rounding_budget k R (tailDefectBudget a C X) L
    hk hR hL hdef hlarge hscale
  have hdrop : ((cs.drop (n + 1)).length : ℝ) ≤ k := by
    exact_mod_cast (show (cs.drop (n + 1)).length ≤ k by simp only [List.length_drop, hlen]; omega)
  have hwidth' : width = 2 * ((3 + 2 * k : ℕ) + 3) := by
    rw [hwidth, initialSmallCellList_length, hlen]
  have hsmall : (6 + 4 * (cs.drop (n + 1)).length) *
      (64 * tailDefectBudget a C X + 1) + width + 4 ≤ 2 * spectatorBulkCount k L := by
    rw [hwidth']
    nlinarith only [hround, hm, mul_le_mul_of_nonneg_right hdrop
      (show 0 ≤ 4 * (64 * tailDefectBudget a C X + 1) by positivity)]
  have hu := selectedProductExponent_gap_upper (G := G) (Y := Y) (width := width) k n hn hD htop hcs
  have hh := mul_le_mul_of_nonneg_left hsmall (show 0 ≤ (2 : ℝ) ^ n by positivity)
  unfold spectatorStepGap at hu ⊢
  push_cast at hu ⊢
  nlinarith only [hu, hh]

theorem movingProductFrequency_le_movingCutoff (T : ℕ → ℝ) (W Y Bs BD Bz z m : ℝ)
    (k : ℕ) (hzero : W - Y ≤ spectatorBaseGap Bs z m)
    (hsteps : ∀ j < k, movingProductExponent T W j - 2 * T j ≤
      spectatorStepGap BD Bz z ((2 : ℝ) ^ j) m) :
    ∀ n ≤ k, movingProductFrequencyExponent T W Y (m / 4) n ≤
      movingCutoffExponent Bs BD Bz z m n := by
  have hs : Real.sqrt (4 * (m / 4)) ≤ Real.sqrt (4 * m) := by
    rw [show 4 * (m / 4) = m by ring]
    by_cases hm : 0 ≤ m
    · exact Real.sqrt_le_sqrt (by linarith)
    · rw [Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hm),
        Real.sqrt_eq_zero_of_nonpos (by linarith)]
  intro n hn
  induction n with
  | zero =>
    rw [movingCutoffExponent_zero]
    simp only [movingProductFrequencyExponent, movingProductExponent, pow_zero, one_mul]
    linarith
  | succ n ih =>
    have hi := ih (by omega)
    have hj := hsteps n (by omega)
    have he := movingProductFrequency_reserve T W Y (m / 4) n
    have hr := mul_le_mul_of_nonneg_left hs (show 0 ≤ (2 : ℝ) ^ n by positivity)
    rw [movingCutoffExponent_succ]
    linarith only [hi, hj, he, hr]

end Ostmann

end OAI

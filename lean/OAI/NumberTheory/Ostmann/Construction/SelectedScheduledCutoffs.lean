import OAI.NumberTheory.Ostmann.Construction.SelectedProductFrequency
import OAI.NumberTheory.Ostmann.Construction.SelectedInitialWindowRate
import OAI.NumberTheory.Ostmann.Construction.SelectedProductSchedule

namespace OAI

/-! # Numerical cutoff data for the literal scheduled cell priors -/
namespace Ostmann
open scoped Classical BigOperators

theorem selected_scheduled_cutoff_data
    {A B : Set ℕ} {N hi top : ℕ} {a C L Y G cb cd width Dlog Bs BD Bz R : ℝ}
    {D : Finset ℕ} {cs : List ℕ} (k : ℕ) (hk : 2 ≤ k)
    (hL : 1 ≤ L) (hY : 0 < Y) (hYupper : Y ≤ Real.exp L)
    (hR : 0 ≤ R) (hdef0 : 0 ≤ tailDefectBudget a C Y)
    (hdef : tailDefectBudget a C Y ≤ R * L)
    (hlarge : 14 * (64 * R + 3) ≤ (k : ℝ) ^ 3)
    (hscale : 4 ≤ (k : ℝ) ^ 4 * L)
    (hcell : 1024 * tailCellLinearRate a C + 52 ≤ (k : ℝ) ^ 4)
    (hcount : (8 + 4 * cs.length : ℕ) ≤ L)
    (hm : 256 ≤ (spectatorBulkCount k L : ℝ))
    (hG : 1 ≤ G) (hcb : 0 ≤ cb) (hD : |Dlog - 2 * cd| ≤ 2)
    (hwidth : width = 2 * ((initialSmallCellList top cs).length + 3))
    (hBs : 0 ≤ Bs) (hBD : 1 ≤ BD) (hBz : 0 ≤ Bz)
    (htop : SelectedSmallTailCell A B N a C L Y hi D
      ((movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L) - 2 * cb) / 6) top)
    (hcs : List.Forall₂
      (fun j t => SelectedSmallTailCell A B N a C L Y hi D (t / 4) j)
      cs (movingCompensationTargets
        (movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L))
        (movingCompensationGaps k BD Bz L))) :
    let m : ℝ := spectatorBulkCount k L
    let T := movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs)
    let W := Y + selectedInitialLogCenter G Y cb cd top cs + width - Dlog
    let V := movingProductNaturalCutoff T W (Y - Dlog) (m / 4)
    Monotone V ∧ Y - Dlog ≤ W ∧
      (∀ n, 0 ≤ movingProductExponent T W n - T n) ∧
      (∀ n ≤ k,
        (V n : ℝ) ≤ Real.exp (movingFrequencyRate (Bs + 1) (BD + 2) Bz ((k : ℝ) ^ 4) n * m) ∧
        ((transferFrequencyRange (V n)).card : ℝ) ≤
          Real.exp (movingFrequencyRate (Bs + 1) (BD + 2) Bz ((k : ℝ) ^ 4) n * m)) := by
  intro m T W V
  have hlen : cs.length = k := by
    simpa only [movingCompensationTargets_length, movingCompensationGaps_length] using hcs.length_eq
  have hDl : 2 * cd - 2 ≤ Dlog := by linarith only [(abs_le.mp hD).1]
  have hDu : Dlog ≤ 2 * cd + 2 := by linarith only [(abs_le.mp hD).2]
  have hwidth0 : 0 ≤ width := by rw [hwidth]; positivity
  have hb := selectedProductExponent_budget_of_cells (G := G) (Y := Y) k (by omega)
    hL hY hYupper hcell hcount hcb hDu hwidth0 hBD hBz htop hcs
  change ∀ n, 2 * T n ≤ movingProductExponent T W n at hb
  have hwin := selected_initial_window_rate k hk hL hR hdef hlarge hscale htop hcs hlen
  have hz : 1 ≤ (k : ℝ) ^ 4 := one_le_pow₀ (by exact_mod_cast (show 1 ≤ k by omega))
  have hzlog := Real.log_nonneg hz
  have hcenter := (selected_initial_center_bounds k htop hcs).1
  have hcenter0 : 0 ≤ selectedInitialLogCenter G Y cb cd top cs := by
    have hbase0 : 0 ≤ spectatorBaseGap Bs ((k : ℝ) ^ 4) m := by
      unfold spectatorBaseGap
      positivity
    exact hbase0.trans hcenter
  have hzero : W - (Y - Dlog) ≤ spectatorBaseGap (Bs + 1) ((k : ℝ) ^ 4) m := by
    dsimp only [W]
    rw [hwidth]
    dsimp only [spectatorBaseGap, m]
    linarith only [hwin.2]
  refine ⟨movingProductNaturalCutoff_monotone T W (Y - Dlog) (m / 4) hb, ?_, ?_, ?_⟩
  · dsimp only [W]
    linarith
  · intro n
    have ht := selected_cell_pivot_nonneg G hG cs n
    change 0 ≤ T n at ht
    linarith [hb n]
  · intro n hn
    have hsteps : ∀ j < k, movingProductExponent T W j - 2 * T j ≤
        spectatorStepGap (BD + 2) Bz ((k : ℝ) ^ 4) ((2 : ℝ) ^ j) m := by
      intro j hj
      have hh := selectedProductExponent_gap_budget (G := G) (Y := Y) k j hk hj hL hR
        hdef0 hdef hlarge hscale (by linarith) hwidth hDl htop hcs
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using hh
    have hfreq := movingProductFrequency_le_movingCutoff T W (Y - Dlog)
      (Bs + 1) (BD + 2) Bz ((k : ℝ) ^ 4) m k hzero hsteps n hn
    have hVle : V n ≤ movingNaturalCutoff (Bs + 1) (BD + 2) Bz ((k : ℝ) ^ 4) m n :=
      Nat.floor_mono (Real.exp_le_exp.mpr hfreq)
    have hbound := movingNaturalCutoff_frequency_bound (Bs + 1) (BD + 2) Bz
      ((k : ℝ) ^ 4) m n (by linarith) (by linarith) hBz hz (by linarith)
    have hVreal : (V n : ℝ) ≤
        movingNaturalCutoff (Bs + 1) (BD + 2) Bz ((k : ℝ) ^ 4) m n := by exact_mod_cast hVle
    refine ⟨hVreal.trans hbound.1, ?_⟩
    apply le_trans _ hbound.2
    rw [card_transferFrequencyRange, card_transferFrequencyRange]
    exact_mod_cast (show 2 * V n + 1 ≤ 2 * movingNaturalCutoff (Bs + 1) (BD + 2) Bz
      ((k : ℝ) ^ 4) m n + 1 by omega)

theorem selected_scheduled_rigidity_margin
    {A B : Set ℕ} {N hi top : ℕ} {a C L Y G cb cd width Dlog Bs BD Bz : ℝ}
    {D : Finset ℕ} {cs : List ℕ} (k n : ℕ) (hn : n < k)
    (hk : 1 ≤ k) (hm : 64 ≤ (spectatorBulkCount k L : ℝ))
    (hD : Dlog ≤ 2 * cd + 2)
    (herror : 256 * tailDefectBudget a C Y + 9 ≤ (spectatorBulkCount k L : ℝ) / 40)
    (hBD : Bs + 1 ≤ BD) (hBz : 8 ≤ Bz)
    (hcs : List.Forall₂
      (fun j t => SelectedSmallTailCell A B N a C L Y hi D (t / 4) j)
      cs (movingCompensationTargets
        (movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L))
        (movingCompensationGaps k BD Bz L))) :
    let m : ℝ := spectatorBulkCount k L
    let T := movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs)
    let W := Y + selectedInitialLogCenter G Y cb cd top cs + width - Dlog
    (1 / 20 : ℝ) * (2 : ℝ) ^ n * m ≤
      (movingProductExponent T W n - 2 * T n) -
        movingProductFrequencyExponent T W (Y - Dlog) (m / 4) n := by
  intro m T W
  let J := movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L)
  have htotal := moving_protected_and_compensation_total k BD Bz L Y G cd
    (spectatorBaseGap Bs ((k : ℝ) ^ 4) m)
  have hbase : 2 * G + J +
      (movingCompensationTargets J (movingCompensationGaps k BD Bz L)).sum - (Y - 2 * cd) =
      spectatorBaseGap Bs ((k : ℝ) ^ 4) m := by
    change 2 * G + 2 * cd + J +
      (movingCompensationTargets J (movingCompensationGaps k BD Bz L)).sum = _ at htotal
    linarith only [htotal]
  have herr := (abs_le.mp (selectedCompensation_pivot_error hcs n
    (by simpa only [movingCompensationTargets_length, movingCompensationGaps_length] using hn) G)).2
  have hideal := movingProductFrequency_prescribed_margin G J (Y - 2 * cd) Bs BD Bz L k n hn
    T W (256 * tailDefectBudget a C Y + 9) hbase
    (by dsimp only [T, J]; linarith only [herr]) herror hBD hBz
    (one_le_pow₀ (by exact_mod_cast hk)) hm
  rw [movingProductFrequency_gap] at hideal ⊢
  have hroot := Real.sqrt_le_sqrt (show 4 * (m / 4) ≤ 4 * m by dsimp only [m] at *; linarith only [hm])
  have hr : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hr0 : 0 ≤ (2 : ℝ) ^ n := by positivity
  have hs := mul_le_mul_of_nonneg_left hroot hr0
  have hreserve := mul_le_mul_of_nonneg_left hm hr0
  nlinarith only [hideal, hs, hD, hr, hreserve]

end Ostmann

end OAI

import OAI.NumberTheory.Ostmann.Construction.SelectedScheduledCutoffs
import OAI.NumberTheory.Ostmann.Arithmetic.MovingProductInitialCutoff
import OAI.NumberTheory.Ostmann.Arithmetic.MovingFrequencyRateMonotone

namespace OAI

namespace Ostmann
open scoped Classical BigOperators

theorem selected_initial_unshifted_cutoff
    {A B : Set ℕ} {N hi top : ℕ} {a C L Y G cb cd Bs BD Bz R : ℝ}
    {D : Finset ℕ} {cs : List ℕ} (k : ℕ) (hk : 2 ≤ k)
    (hL : 1 ≤ L) (hY : 0 < Y) (hYupper : Y ≤ Real.exp L)
    (hR : 0 ≤ R) (hdef0 : 0 ≤ tailDefectBudget a C Y)
    (hdef : tailDefectBudget a C Y ≤ R * L)
    (hlarge : 14 * (64 * R + 3) ≤ (k : ℝ) ^ 3)
    (hscale : 4 ≤ (k : ℝ) ^ 4 * L)
    (hcell : 1024 * tailCellLinearRate a C + 52 ≤ (k : ℝ) ^ 4)
    (hcount : (8 + 4 * cs.length : ℕ) ≤ L)
    (hm : 256 ≤ (spectatorBulkCount k L : ℝ))
    (hG : 1 ≤ G) (hcb : 0 ≤ cb)
    (hBs : 0 ≤ Bs) (hBD : 1 ≤ BD) (hBz : 0 ≤ Bz)
    (htop : SelectedSmallTailCell A B N a C L Y hi D
      ((movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L) - 2 * cb) / 6) top)
    (hcs : List.Forall₂ (fun j t => SelectedSmallTailCell A B N a C L Y hi D (t / 4) j)
      cs (movingCompensationTargets
        (movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L))
        (movingCompensationGaps k BD Bz L))) :
    let m : ℝ := spectatorBulkCount k L
    let T := movingCellPivotExponent (fun _ => G) (selectedCompensationCenter cs)
    let W := Y + selectedInitialLogCenter G Y cb cd top cs +
      2 * ((initialSmallCellList top cs).length + 3)
    let V₀ := movingProductNaturalCutoff T W Y (m / 4) 0
    (V₀ : ℝ) ≤ Real.exp (movingFrequencyRate (Bs + 1) (BD + 2) Bz ((k : ℝ) ^ 4) 0 * m) ∧
    ((transferFrequencyRange V₀).card : ℝ) ≤
      Real.exp (movingFrequencyRate (Bs + 1) (BD + 2) Bz ((k : ℝ) ^ 4) 0 * m) := by
  intro m T W V₀
  have hdata := selected_scheduled_cutoff_data (Dlog := 2 * cd) k hk hL hY hYupper
    hR hdef0 hdef hlarge hscale hcell hcount hm hG hcb
    (by simp) rfl hBs hBD hBz htop hcs
  dsimp only at hdata
  have hzero := hdata.2.2.2 0 (Nat.zero_le k)
  rw [movingProductNaturalCutoff_zero_translate] at hzero
  exact hzero

theorem movingFrequencyRate_uniform_bounds (Bs BD Bz z m : ℝ) (k : ℕ) (V : ℕ → ℕ)
    (hBs : 0 ≤ Bs) (hBD : 0 ≤ BD) (hBz : 0 ≤ Bz) (hz : 1 ≤ z) (hm : 0 ≤ m)
    (hV : ∀ n ≤ k,
      (V n : ℝ) ≤ Real.exp (movingFrequencyRate Bs BD Bz z n * m) ∧
      ((transferFrequencyRange (V n)).card : ℝ) ≤
        Real.exp (movingFrequencyRate Bs BD Bz z n * m)) :
    ∀ n ≤ k,
      (V n : ℝ) ≤ Real.exp (movingFrequencyRate Bs BD Bz z k * m) ∧
      ((transferFrequencyRange (V n)).card : ℝ) ≤
        Real.exp (movingFrequencyRate Bs BD Bz z k * m) := by
  intro n hn
  have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
    (movingFrequencyRate_monotone Bs BD Bz z hBs hBD hBz hz hn) hm)
  exact ⟨(hV n hn).1.trans he, (hV n hn).2.trans he⟩

theorem frozen_spectator_window (P : ℝ) (hP : 0 < P) (Y center width : ℝ) :
    0 < Real.exp Y / P ∧
      Real.exp Y / P * Real.exp (center + width) =
        Real.exp (Y + center + width - Real.log P) := by
  refine ⟨div_pos (Real.exp_pos Y) hP, ?_⟩
  rw [Real.exp_sub, Real.exp_log hP]
  simp only [Real.exp_add, div_eq_mul_inv]
  ring

end Ostmann

end OAI

import OAI.NumberTheory.Ostmann.Construction.SelectedInitialWindowRate
import OAI.NumberTheory.Ostmann.Arithmetic.MovingProductInitialCutoff

namespace OAI

/-! # The measured initial window meets the energy and cutoff budgets -/
namespace Ostmann
open Filter

theorem eventual_selected_initial_energy_window (k : ℕ) (hk : 2 ≤ k)
    (Bs BD Bz R : ℝ) (hBs : 1 ≤ Bs) (hR : 0 ≤ R)
    (hlarge : 14 * (64 * R + 3) ≤ (k : ℝ) ^ 3) :
    ∀ᶠ L : ℝ in atTop, ∀ {A B : Set ℕ} {N hi top : ℕ}
      {a C Y G cb cd : ℝ} {D : Finset ℕ} {cs : List ℕ},
      tailDefectBudget a C Y ≤ R * L →
      SelectedSmallTailCell A B N a C L Y hi D
        ((movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L) - 2 * cb) / 6) top →
      List.Forall₂ (fun j w => SelectedSmallTailCell A B N a C L Y hi D (w / 4) j)
        cs (movingCompensationTargets
          (movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L))
          (movingCompensationGaps k BD Bz L)) → cs.length = k →
      let m := (spectatorBulkCount k L : ℝ)
      let center := selectedInitialLogCenter G Y cb cd top cs
      let width : ℝ := 2 * ((initialSmallCellList top cs).length + 3)
      let Δ := center - width
      64 ≤ m / 4 ∧ 0 ≤ Δ ∧ Δ ≤ spectatorBaseGap (Bs + 1) ((k : ℝ) ^ 4) m ∧
      Real.exp Δ ≤ Real.exp (center + width) ∧
      Real.exp (center + width) - Real.exp Δ ≤
        Real.exp ((Bs + 1 + 8 * Real.log ((k : ℝ) ^ 4)) * m) ∧
      Y ≤ Y + center + width ∧
      ∀ T : ℕ → ℝ,
        (movingProductNaturalCutoff T (Y + center + width) Y (m / 4) 0 : ℝ) ≤
          Real.exp (Δ + Real.sqrt (4 * m)) := by
  have hk0 : 0 < k := by omega
  have hreserve := (spectatorBulkCount_tendsto k hk0).eventually
    (eventually_initial_product_reserve (4 * (((3 + 2 * k : ℕ) : ℝ) + 3)))
  filter_upwards [hreserve, eventually_ge_atTop (1 : ℝ)] with L hreserve hL
  intro A B N hi top a C Y G cb cd D cs hdef htop hcs hlen m center width Δ
  have hscale : 4 ≤ (k : ℝ) ^ 4 * L := by
    have hkr : (2 : ℝ) ≤ k := by exact_mod_cast hk
    have hk4 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hkr 4
    norm_num at hk4
    nlinarith
  have hwin := selected_initial_window_rate k hk hL hR hdef hlarge hscale htop hcs hlen
  have hwidth : 0 ≤ width := by dsimp only [width]; positivity
  have hwidth2 : 2 * width ≤ Real.sqrt m := by
    have he : 2 * width = 4 * (((3 + 2 * k : ℕ) : ℝ) + 3) := by
      dsimp only [width]
      rw [initialSmallCellList_length, hlen]
      push_cast
      ring
    rw [he]
    exact hreserve.2
  have hlog : 0 ≤ Real.log ((k : ℝ) ^ 4) := by
    apply Real.log_nonneg
    exact one_le_pow₀ (by exact_mod_cast hk0)
  have hΔ : 0 ≤ Δ := by
    have hm : 0 ≤ m := Nat.cast_nonneg _
    have hbase : 0 ≤ (Bs - 1 + 8 * Real.log ((k : ℝ) ^ 4)) * m := by positivity
    exact hbase.trans hwin.1
  have hupper : center + width ≤ spectatorBaseGap (Bs + 1) ((k : ℝ) ^ 4) m := hwin.2
  refine ⟨hreserve.1, hΔ, ?_, Real.exp_le_exp.mpr (by dsimp only [Δ]; linarith), ?_, ?_, ?_⟩
  · dsimp only [Δ]
    linarith
  · have hh := Real.exp_le_exp.mpr hupper
    dsimp only [spectatorBaseGap] at hh
    linarith [Real.exp_pos Δ]
  · dsimp only [Δ] at hΔ
    linarith
  · intro T
    exact movingProductNaturalCutoff_zero_window T (Y + center + width) Y Δ m (2 * width)
      (by dsimp only [Δ]; linarith) hwidth2

end Ostmann

end OAI

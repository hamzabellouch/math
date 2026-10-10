import OAI.NumberTheory.Ostmann.Construction.SelectedInitialProductWindow
import OAI.NumberTheory.Ostmann.Construction.InitialMixedNormalizer

namespace OAI

/-! # The selected product center fits the original one-unit gap reserve -/
namespace Ostmann

theorem selected_initial_window_rate
    {A B : Set ℕ} {N hi top : ℕ} {a C L Y G cb cd Bs BD Bz R : ℝ}
    {D : Finset ℕ} {centers : List ℕ} (k : ℕ) (hk : 2 ≤ k)
    (hL : 1 ≤ L) (hR : 0 ≤ R) (hD : tailDefectBudget a C Y ≤ R * L)
    (hlarge : 14 * (64 * R + 3) ≤ (k : ℝ) ^ 3)
    (hscale : 4 ≤ (k : ℝ) ^ 4 * L)
    (htop : SelectedSmallTailCell A B N a C L Y hi D
      ((movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L) - 2 * cb) / 6) top)
    (hcenters : List.Forall₂ (fun j w => SelectedSmallTailCell A B N a C L Y hi D (w / 4) j)
      centers (movingCompensationTargets
        (movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L))
        (movingCompensationGaps k BD Bz L))) (hlen : centers.length = k) :
    let m := spectatorBulkCount k L
    let Δ := selectedInitialLogCenter G Y cb cd top centers
    let W : ℝ := 2 * ((initialSmallCellList top centers).length + 3)
    (Bs - 1 + 8 * Real.log ((k : ℝ) ^ 4)) * m ≤ Δ - W ∧
      Δ + W ≤ (Bs + 1 + 8 * Real.log ((k : ℝ) ^ 4)) * m := by
  intro m Δ W
  have hbound := selected_initial_center_bounds k htop hcenters
  have hround := initial_cell_rounding_budget k R (tailDefectBudget a C Y) L
    hk hR hL hD hlarge hscale
  have hW : W = 2 * (((3 + 2 * k : ℕ) : ℝ) + 3) := by
    dsimp only [W]
    rw [initialSmallCellList_length, hlen]
  rw [← hW] at hround
  dsimp only [spectatorBaseGap] at hbound
  constructor <;> dsimp only [Δ, m] at * <;> linarith only [hbound.1, hbound.2, hround]

theorem selected_initial_normalizer_rate (k : ℕ) (hk : 2 ≤ k) (L : ℝ)
    (hL : 0 < L) (hscale : 4 ≤ (k : ℝ) ^ 4 * L)
    (top : ℕ) (centers : List ℕ) (hlen : centers.length = k) :
    let m := spectatorBulkCount k L
    let C := initialHalfNormalizer (m / 2) (m / 2)
      (initialSmallCellList top centers).length (1 / 320000) L (91 / 100)
    (∏ i, Fin.append C C i) * L ^ (2 * m) ≤
      Real.exp ((4 - 2 * Real.log (1 / 320000)) * m) := by
  intro m C
  have heven : m / 2 + m / 2 = m := by
    obtain ⟨t, ht⟩ := spectatorBulkCount_even k L
    dsimp only [m]
    omega
  have hcell := initial_cell_normalizer_budget k hk L (91 / 100) hL.le (by norm_num) hscale
  have hlen' : (initialSmallCellList top centers).length = 3 + 2 * k := by
    rw [initialSmallCellList_length, hlen]
  have hh := initial_mixed_normalizer_bound (m / 2) (m / 2)
    (initialSmallCellList top centers).length (1 / 320000) L (91 / 100)
    (by norm_num) hL (by simpa only [hlen', heven] using hcell)
  simpa only [heven] using hh

end Ostmann

end OAI

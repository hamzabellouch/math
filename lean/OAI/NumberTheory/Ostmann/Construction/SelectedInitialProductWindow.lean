import OAI.NumberTheory.Ostmann.Construction.InitialCellPriors
import OAI.NumberTheory.Ostmann.Construction.InitialSampledProductWindow
import OAI.NumberTheory.Ostmann.Construction.InitialCellRoundingBudget
import OAI.NumberTheory.Ostmann.Construction.SmoothGiantActiveSupport

namespace OAI

/-! # The exact product center of the original selected mixed prior -/
namespace Ostmann
open scoped Classical BigOperators

noncomputable def selectedInitialLogCenter (G Y cb cd : ℝ) (top : ℕ)
    (centers : List ℕ) : ℝ :=
  2 * (G + cb + cd + 3 * top + 2 * (centers.map (fun j : ℕ => (j : ℝ))).sum) - Y

theorem selected_initial_center_bounds
    {A B : Set ℕ} {N hi top : ℕ} {a C L Y G cb cd Bs BD Bz : ℝ}
    {D : Finset ℕ} {centers : List ℕ} (k : ℕ)
    (htop : SelectedSmallTailCell A B N a C L Y hi D
      ((movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L) - 2 * cb) / 6) top)
    (hcenters : List.Forall₂ (fun j w => SelectedSmallTailCell A B N a C L Y hi D (w / 4) j)
      centers (movingCompensationTargets
        (movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L))
        (movingCompensationGaps k BD Bz L))) :
    let Δ := spectatorBaseGap Bs ((k : ℝ) ^ 4) (spectatorBulkCount k L)
    Δ ≤ selectedInitialLogCenter G Y cb cd top centers ∧
      selectedInitialLogCenter G Y cb cd top centers ≤
        Δ + (6 + 4 * k) * (64 * tailDefectBudget a C Y + 1) := by
  intro Δ
  have herror := selected_initial_total_error k htop hcenters
  have hsum := selected_compensation_centers_sum_bounds hcenters
  have htotal := moving_protected_and_compensation_total k BD Bz L Y G cd Δ
  have ht := htop.1
  change (movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L) - 2 * cb) / 6 ≤
    (top : ℝ) at ht
  change 2 * G + 2 * cd + movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L) +
    (movingCompensationTargets (movingProtectedTarget k Y G cd (movingInitialGapTotal k Bs BD Bz L))
      (movingCompensationGaps k BD Bz L)).sum = Y + Δ at htotal
  constructor
  · dsimp only [selectedInitialLogCenter]
    linarith only [ht, hsum.1, htotal]
  · have hh := (abs_le.mp herror).2
    dsimp only [selectedInitialLogCenter]
    linarith only [hh]

theorem selectedInitialCellCenter_sum (top : ℕ) (centers : List ℕ) :
    (∑ i : Fin (initialSmallCellList top centers).length,
      ((initialSmallCellList top centers).get i : ℝ)) =
        3 * top + 2 * (centers.map (fun j : ℕ => (j : ℝ))).sum := by
  rw [← List.sum_ofFn]
  have he : (List.ofFn (fun i : Fin (initialSmallCellList top centers).length =>
      ((initialSmallCellList top centers).get i : ℝ))) =
      (initialSmallCellList top centers).map (fun j : ℕ => (j : ℝ)) := by
    change List.ofFn ((fun j : ℕ => (j : ℝ)) ∘ (initialSmallCellList top centers).get) = _
    rw [← List.map_ofFn, List.ofFn_get]
  rw [he]
  exact initialSmallCellList_sum top centers

/-- The narrow window is centered at the actual selected total. Its width
depends only on the number of fixed cell roles, including the giant. -/
theorem selected_initial_product_window
    {A B : Set ℕ} {N endpoint top : ℕ} {a C L Y G cb cd target : ℝ}
    {D : Finset ℕ} {centers : List ℕ} {targets : List ℝ}
    (htop : SelectedSmallTailCell A B N a C L Y endpoint D target top)
    (hcenters : List.Forall₂
      (fun j w => SelectedSmallTailCell A B N a C L Y endpoint D (w / 4) j) centers targets)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (b d : ℕ)
    (μb : Fin b → P → ℝ) (μd : Fin d → P → ℝ) :
    let cells := initialSmallCellList top centers
    let μc := fun i : Fin cells.length => primeSubsetPrior P
      (selectedTailCellPrimes A B N Y endpoint D (cells.get i))
    let ν := Fin.cons (smoothGiantPrior P logCellProfile G)
      (Fin.append μb (Fin.append μd μc))
    let Δ := selectedInitialLogCenter G Y cb cd top centers
    ∀ x : Fin (((b + (d + cells.length)) + 1) + ((b + (d + cells.length)) + 1)) → P,
      productPrior (Fin.append ν ν) x ≠ 0 →
      doubledHalfWeight (fun y : Fin ((b + (d + cells.length)) + 1) → P =>
        (initialHalfCutoffWeight (fun q : P => (q : ℕ)) b d cells.length cb cd (Fin.tail y) : ℂ)) x ≠ 0 →
      Real.exp Y * Real.exp (Δ - 2 * (cells.length + 3)) ≤ ∏ i, (x i : ℝ) ∧
        (∏ i, (x i : ℝ)) ≤ Real.exp Y * Real.exp (Δ + 2 * (cells.length + 3)) := by
  intro cells μc ν Δ x hprior hw
  have hgiant (p : P) (hp : smoothGiantPrior P logCellProfile G p ≠ 0) :
      |Real.log (p : ℝ) - G| ≤ 1 := by
    have hh := smoothGiantPrior_active_bounds P hP logCellProfile G logCellProfile_zero_outside p hp
    have hp0 : 0 < (p : ℝ) := by exact_mod_cast (hP p p.property).pos
    have hlo := (Real.lt_log_iff_exp_lt hp0).mpr hh.1
    have hhi := (Real.log_lt_iff_lt_exp hp0).mpr hh.2
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hcell (i : Fin cells.length) (p : P) (hp : μc i p ≠ 0) :
      |Real.log (p : ℝ) - (cells.get i : ℝ)| ≤ 1 := by
    have hmem := primeSubsetPrior_support P _ p hp
    obtain ⟨t, ht⟩ := initial_selected_cells_valid htop hcenters _ (List.get_mem cells i)
    obtain ⟨_, _, _, _, _, _, hsupport⟩ := ht
    have hs := hsupport p hmem
    have hp0 : 0 < (p : ℝ) := by exact_mod_cast hs.1.pos
    have hlo := (Real.lt_log_iff_exp_lt hp0).mpr hs.2.1
    have hhi := (Real.log_le_iff_le_exp hp0).mpr hs.2.2.1
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have htarget : |2 * (G + cb + cd + ∑ i : Fin cells.length, (cells.get i : ℝ)) -
      (Real.log (Real.exp Y) + Δ)| ≤ 0 := by
    rw [Real.log_exp]
    change |2 * (G + cb + cd + ∑ i : Fin (initialSmallCellList top centers).length,
      ((initialSmallCellList top centers).get i : ℝ)) -
        (Y + selectedInitialLogCenter G Y cb cd top centers)| ≤ 0
    rw [selectedInitialCellCenter_sum]
    simp only [selectedInitialLogCenter]
    ring_nf
    simp
  simpa only [zero_add] using initial_doubled_product_window P hP b d cells.length
    (smoothGiantPrior P logCellProfile G) μb μd μc G cb cd (fun i => (cells.get i : ℝ))
    hgiant hcell (Real.exp Y) Δ 0 (Real.exp_pos _) htarget x hprior hw

end Ostmann

end OAI

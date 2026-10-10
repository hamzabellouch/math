import Mathlib.Data.Int.Interval
import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterZeroMultiplicity

namespace OAI

/-! # Covering the right critical half-strip by Jensen disks -/

namespace Ostmann

open Metric Set
open scoped BigOperators Classical

theorem character_strip_mem_disk (z : ℂ) (t : ℝ)
    (hr : 1 / 2 ≤ z.re) (hr' : z.re ≤ 1) (hi : |z.im - t| ≤ 1 / 2) :
    z ∈ closedBall (characterZeroCenter t) (13 / 8 : ℝ) := by
  rw [mem_closedBall, dist_eq_norm]
  have hs : ‖z - characterZeroCenter t‖ ^ 2 = (z.re - 2) ^ 2 + (z.im - t) ^ 2 := by
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, pow_two]
  have hire := abs_le.mp hi
  have hprod := mul_nonneg (show 0 ≤ z.re - 1 / 2 by linarith)
    (show 0 ≤ 1 - z.re by linarith)
  have hiprod := mul_nonneg (show 0 ≤ 1 / 2 - (z.im - t) by linarith)
    (show 0 ≤ 1 / 2 + (z.im - t) by linarith)
  nlinarith [norm_nonneg (z - characterZeroCenter t)]

noncomputable def characterOrdinateBins (T : ℝ) : Finset ℤ :=
  Finset.Icc ⌊-T⌋ ⌊T⌋

theorem characterOrdinateBins_mem (T : ℝ) (z : ℂ) (hz : |z.im| ≤ T) :
    ⌊z.im⌋ ∈ characterOrdinateBins T := by
  exact Finset.mem_Icc.mpr ⟨Int.floor_mono (abs_le.mp hz).1, Int.floor_mono (abs_le.mp hz).2⟩

theorem characterOrdinateBins_card (T : ℝ) (hT : 0 ≤ T) :
    ((characterOrdinateBins T).card : ℝ) ≤ 2 * T + 2 := by
  have hle : ⌊-T⌋ ≤ ⌊T⌋ + 1 := by
    have h := Int.floor_mono (show -T ≤ T by linarith)
    omega
  have hc := Int.card_Icc_of_le _ _ hle
  have hc' : ((characterOrdinateBins T).card : ℝ) = (⌊T⌋ : ℝ) + 1 - (⌊-T⌋ : ℝ) := by
    exact_mod_cast hc
  rw [hc']
  linarith [Int.floor_le T, Int.lt_floor_add_one (-T)]

theorem characterOrdinateBins_center_bound (T : ℝ) (n : ℤ)
    (hn : n ∈ characterOrdinateBins T) : |(n : ℝ) + 1 / 2| ≤ T + 1 := by
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hn
  have hlo' : (⌊-T⌋ : ℝ) ≤ n := by exact_mod_cast hlo
  have hhi' : (n : ℝ) ≤ ⌊T⌋ := by exact_mod_cast hhi
  exact abs_le.mpr ⟨by linarith [Int.lt_floor_add_one (-T)], by linarith [Int.floor_le T]⟩

theorem character_floor_mem_disk (z : ℂ) (hr : 1 / 2 ≤ z.re) (hr' : z.re ≤ 1) :
    z ∈ closedBall (characterZeroCenter ((⌊z.im⌋ : ℝ) + 1 / 2)) (13 / 8 : ℝ) := by
  apply character_strip_mem_disk z _ hr hr'
  exact abs_le.mpr ⟨by linarith [Int.floor_le z.im], by linarith [Int.lt_floor_add_one z.im]⟩

end Ostmann

end OAI

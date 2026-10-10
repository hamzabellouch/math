import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.TailInitialEventuallyBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.OwnProbabilityTailTiltBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set
open scoped Topology

namespace CoulombAtom
open CoulombBarrier

 def tinyProbabilityFloor (Z u : ℝ) : ℝ := min 1 (u^80)/(1+Z)

lemma tinyProbabilityFloor_pos {Z u : ℝ} (hZ : 0 ≤ Z) (hu : 0 < u) :
    0 < tinyProbabilityFloor Z u := by unfold tinyProbabilityFloor; positivity

lemma tinyProbabilityFloor_le_polynomial {Z u : ℝ} (hZ : 0 ≤ Z) (hu : 0 ≤ u) :
    tinyProbabilityFloor Z u ≤ min 1 (u^40) := by
  have hn : 0 ≤ min (1:ℝ) (u^80) := le_min (by norm_num) (pow_nonneg hu _)
  have hd : 1 ≤ 1+Z := by linarith
  apply (div_le_self hn hd).trans
  by_cases h : u ≤ 1
  · apply min_le_min_left 1
    have h40 := pow_le_one₀ hu h (n := 40)
    have hpow : u^80 = (u^40)^2 := by ring
    rw [hpow]
    nlinarith [pow_nonneg hu 40]
  · have h40 : 1 ≤ u^40 := one_le_pow₀ (by linarith)
    rw [min_eq_left h40]
    exact min_le_left _ _

lemma tinyProbabilityFloor_nuclear_bound {Z u v : ℝ}
    (hZ : 0 ≤ Z) (hu : 0 < u) (huv : u ≤ v) :
    tinyProbabilityFloor Z u*(Z/v) ≤ u^79 := by
  have hv : 0 < v := hu.trans_le huv
  have hden : 0 < 1+Z := by linarith
  have hZr : Z/(1+Z) ≤ 1 := (div_le_one hden).mpr (by linarith)
  have hn : 0 ≤ Z/(1+Z) := div_nonneg hZ hden.le
  calc
    _ = (Z/(1+Z))*min 1 (u^80)/v := by unfold tinyProbabilityFloor; ring
    _ ≤ (Z/(1+Z))*u^80/v := by gcongr; exact min_le_right _ _
    _ ≤ u^80/v := div_le_div_of_nonneg_right
      (le_trans (mul_le_mul_of_nonneg_right hZr (pow_nonneg hu.le _)) (by simp)) hv.le
    _ ≤ u^80/u := div_le_div_of_nonneg_left (by positivity) hu huv
    _ = u^79 := by field_simp

theorem exists_actual_tiny_floor_state {Z lam r : ℝ} (hZ : 0 ≤ Z) (hr : 0 < r)
    {N : ℕ} (hN : PriceMinimizes (energy Z) lam N) (K : ℕ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ F : fermionGraph N,
      OwnProbabilityTailTiltState Z lam r K
        (fun j => tinyProbabilityFloor Z ((2:ℝ)^j.val*r)) δ F ∧
      TailTiltState Z lam r K (tailPolynomialThreshold r) δ F := by
  obtain ⟨F,hF⟩ := exists_actual_own_probability_tail_tilt_state hZ hr hN K
    (fun j => tinyProbabilityFloor Z ((2:ℝ)^j.val*r))
    (fun _ => tinyProbabilityFloor_pos hZ (by positivity)) hδ
  exact ⟨F,hF,hF.to_tailTiltState hr (tailPolynomialThreshold_pos hr)
    (fun _ => tinyProbabilityFloor_le_polynomial hZ (by positivity))⟩

end CoulombAtom

end

end OAI

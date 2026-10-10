import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.DetectorTiming

namespace OAI

/-! Exact isolation of each burst and the following heat-only waiting
interval. The endpoints are included because the smooth pulses vanish there. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set

theorem detectorSourceTerm_before_closed (C L n : ℕ) (y : ℝ × Plane)
    (hy : y.1 ≤ 2 * ((n : ℝ) + 1)) : detectorSourceTerm C L n y = 0 := by
  have hd : (0 : ℝ) < duration C L n := by exact_mod_cast duration_pos C L n
  have hh : (y.1 - 2 * ((n : ℝ) + 1)) / (duration C L n : ℝ) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le
  simp only [detectorSourceTerm, smoothPulse_before (by norm_num : (0 : ℝ) < 1) hh,
    mul_zero, zero_mul]

theorem detectorDriftTerm_before_closed (V : ℝ → Plane → Plane) (C L n : ℕ)
    (y : ℝ × Plane) (hy : y.1 ≤ 2 * ((n : ℝ) + 1)) :
    detectorDriftTerm V C L n y = 0 := by
  have hd : (0 : ℝ) < duration C L n := by exact_mod_cast duration_pos C L n
  rw [detectorDriftTerm, detectorSpeed_before C L n (by linarith), zero_smul]

theorem detectorDriftTerm_after (V : ℝ → Plane → Plane) (C L n : ℕ)
    (y : ℝ × Plane)
    (hy : 2 * ((n : ℝ) + 1) + 2 * (duration C L n : ℝ) ≤ y.1) :
    detectorDriftTerm V C L n y = 0 := by
  rw [detectorDriftTerm, detectorSpeed_after C L n hy, zero_smul]

theorem detector_duration_real_le (C L n : ℕ) : (duration C L n : ℝ) ≤ 1 / 100 := by
  have h := (Rat.cast_le (K := ℝ)).mpr (duration_le C L n)
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at h
  exact h

theorem detector_other_block_inactive (C L n m : ℕ) (hm : m ≠ n) {t : ℝ}
    (ht : t ∈ Icc (2 * ((n : ℝ) + 1)) (2 * ((n : ℝ) + 2))) :
    t ≤ 2 * ((m : ℝ) + 1) ∨
      2 * ((m : ℝ) + 1) + 2 * (duration C L m : ℝ) ≤ t := by
  rcases lt_or_gt_of_ne hm with hm | hm
  · right
    have hmn : (m : ℝ) + 1 ≤ n := by exact_mod_cast (Nat.add_one_le_iff.mpr hm)
    have hd := detector_duration_real_le C L m
    linarith [ht.1]
  · left
    have hnm : (n : ℝ) + 1 ≤ m := by exact_mod_cast (Nat.add_one_le_iff.mpr hm)
    linarith [ht.2]

theorem detectorDrift_eq_term (V : ℝ → Plane → Plane) (C L n : ℕ) {t : ℝ}
    (ht : t ∈ Icc (2 * ((n : ℝ) + 1)) (2 * ((n : ℝ) + 2))) (x : Plane) :
    detectorDrift V C L t x = detectorDriftTerm V C L n (t, x) := by
  unfold detectorDrift detectorBlockSum
  apply tsum_eq_single n
  intro m hm
  rcases detector_other_block_inactive C L n m hm ht with hb | ha
  · exact detectorDriftTerm_before_closed V C L m (t, x) hb
  · exact detectorDriftTerm_after V C L m (t, x) ha

theorem detectorSource_eq_term (C L n : ℕ) {t : ℝ}
    (ht : t ∈ Icc (2 * ((n : ℝ) + 1)) (2 * ((n : ℝ) + 2))) (x : Plane) :
    detectorSource C L t x = detectorSourceTerm C L n (t, x) := by
  unfold detectorSource detectorBlockSum
  apply tsum_eq_single n
  intro m hm
  rcases detector_other_block_inactive C L n m hm ht with hb | ha
  · exact detectorSourceTerm_before_closed C L m (t, x) hb
  · have hd : (0 : ℝ) < duration C L m := by exact_mod_cast duration_pos C L m
    exact detectorSourceTerm_after C L m (t, x) (by linarith)

theorem detector_wait_coefficients_zero (V : ℝ → Plane → Plane) (C L n : ℕ) {t : ℝ}
    (ht : t ∈ Icc (2 * ((n : ℝ) + 1) + 2 * (duration C L n : ℝ))
      (2 * ((n : ℝ) + 2))) (x : Plane) :
    detectorDrift V C L t x = 0 ∧ detectorSource C L t x = 0 := by
  have hd : (0 : ℝ) < duration C L n := by exact_mod_cast duration_pos C L n
  have hi : t ∈ Icc (2 * ((n : ℝ) + 1)) (2 * ((n : ℝ) + 2)) :=
    ⟨by linarith [ht.1], ht.2⟩
  constructor
  · rw [detectorDrift_eq_term V C L n hi]
    exact detectorDriftTerm_after V C L n (t, x) ht.1
  · rw [detectorSource_eq_term C L n hi]
    exact detectorSourceTerm_after C L n (t, x) (by linarith [ht.1])

end ForcedComputation.VelocityDetector

end

end OAI

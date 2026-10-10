import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.DetectorStirring

namespace OAI

/-! Exact endpoints of the scheduled injection and stirring clocks. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows

theorem detectorPhase_before (C L n : ℕ) {t : ℝ}
    (ht : t ≤ 2 * ((n : ℝ) + 1) + (duration C L n : ℝ)) :
    detectorPhase C L n t = 0 := by
  have hd : (0 : ℝ) < duration C L n := by exact_mod_cast duration_pos C L n
  have hh : (t - 2 * ((n : ℝ) + 1) - (duration C L n : ℝ)) /
      (duration C L n : ℝ) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le
  simp only [detectorPhase, smoothRamp_before (by norm_num : (0 : ℝ) < 1) hh, mul_zero]

theorem detectorPhase_after (C L n : ℕ) {t : ℝ}
    (ht : 2 * ((n : ℝ) + 1) + 2 * (duration C L n : ℝ) ≤ t) :
    detectorPhase C L n t = (n : ℝ) + 1 := by
  have hd : (0 : ℝ) < duration C L n := by exact_mod_cast duration_pos C L n
  have hh : 1 ≤ (t - 2 * ((n : ℝ) + 1) - (duration C L n : ℝ)) /
      (duration C L n : ℝ) := by
    apply (le_div_iff₀ hd).mpr
    linarith
  simp only [detectorPhase, smoothRamp_after (by norm_num : (0 : ℝ) < 1) hh, mul_one]

theorem detectorPhase_hasDerivAt (C L n : ℕ) (t : ℝ) :
    HasDerivAt (detectorPhase C L n) (detectorSpeed C L n t) t := by
  change HasDerivAt (fun r => ((n : ℝ) + 1) * smoothRamp 0 1
    ((r - 2 * ((n : ℝ) + 1) - (duration C L n : ℝ)) / (duration C L n : ℝ))) _ t
  have hr := ((smoothRamp_smooth 0 1).differentiable (by simp)
    ((t - 2 * ((n : ℝ) + 1) - (duration C L n : ℝ)) /
      (duration C L n : ℝ))).hasDerivAt
  have ha := (((hasDerivAt_id t).sub_const (2 * ((n : ℝ) + 1))).sub_const
    (duration C L n : ℝ)).div_const (duration C L n : ℝ)
  convert (hr.comp t ha).const_mul ((n : ℝ) + 1) using 1 <;>
    simp only [detectorSpeed, smoothPulse, Function.comp_def, id_eq,
      div_eq_mul_inv, one_mul, mul_assoc, mul_comm]

theorem detectorSourceTerm_after (C L n : ℕ) (y : ℝ × Plane)
    (hy : 2 * ((n : ℝ) + 1) + (duration C L n : ℝ) ≤ y.1) :
    detectorSourceTerm C L n y = 0 := by
  have hd : (0 : ℝ) < duration C L n := by exact_mod_cast duration_pos C L n
  have hh : 1 ≤ (y.1 - 2 * ((n : ℝ) + 1)) / (duration C L n : ℝ) := by
    apply (le_div_iff₀ hd).mpr
    linarith
  simp only [detectorSourceTerm, smoothPulse_after (by norm_num : (0 : ℝ) < 1) hh,
    mul_zero, zero_mul]

theorem detector_wait_length (C L n : ℕ) :
    1 < 2 * (((n + 1 : ℕ) : ℝ) + 1) -
      (2 * ((n : ℝ) + 1) + 2 * (duration C L n : ℝ)) := by
  have h : (1 : ℝ) < 2 - 2 * (duration C L n : ℝ) := by
    have hh := (Rat.cast_lt (K := ℝ)).mpr (heat_wait_long C L n)
    norm_num only [Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_one] at hh
    exact hh
  push_cast
  linarith

end ForcedComputation.VelocityDetector

end

end OAI

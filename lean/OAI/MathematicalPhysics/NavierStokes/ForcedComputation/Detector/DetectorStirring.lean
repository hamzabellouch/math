import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.DetectorInjection

namespace OAI

/-! The prescribed stirring schedule replays the same smooth processor for
successively longer computational times. All coefficients are explicit. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows
open scoped ContDiff

def detectorPhase (C L n : ℕ) (t : ℝ) : ℝ :=
  letI := ShearFlows.twoAtLeastTwo
  ((n : ℝ) + 1) * smoothRamp 0 1
    ((t - 2 * ((n : ℝ) + 1) - (duration C L n : ℝ)) / (duration C L n : ℝ))

def detectorSpeed (C L n : ℕ) (t : ℝ) : ℝ :=
  letI := ShearFlows.twoAtLeastTwo
  (((n : ℝ) + 1) / (duration C L n : ℝ)) * smoothPulse 0 1
    ((t - 2 * ((n : ℝ) + 1) - (duration C L n : ℝ)) / (duration C L n : ℝ))

def detectorDriftTerm (V : ℝ → Plane → Plane) (C L n : ℕ) (y : ℝ × Plane) : Plane :=
  detectorSpeed C L n y.1 • V (detectorPhase C L n y.1) y.2

def detectorDrift (V : ℝ → Plane → Plane) (C L : ℕ) (t : ℝ) (x : Plane) : Plane :=
  detectorBlockSum (detectorDriftTerm V C L) (t, x)

theorem detectorPhase_smooth (C L n : ℕ) : ContDiff ℝ ∞ (detectorPhase C L n) :=
  contDiff_const.mul ((smoothRamp_smooth 0 1).comp
    (((contDiff_id.sub contDiff_const).sub contDiff_const).div_const _))

theorem detectorSpeed_smooth (C L n : ℕ) : ContDiff ℝ ∞ (detectorSpeed C L n) :=
  contDiff_const.mul ((smoothPulse_smooth 0 1).comp
    (((contDiff_id.sub contDiff_const).sub contDiff_const).div_const _))

theorem detectorSpeed_before (C L n : ℕ) {t : ℝ}
    (ht : t ≤ 2 * ((n : ℝ) + 1) + (duration C L n : ℝ)) :
    detectorSpeed C L n t = 0 := by
  have hd : (0 : ℝ) < duration C L n := by exact_mod_cast duration_pos C L n
  have harg : (t - 2 * ((n : ℝ) + 1) - (duration C L n : ℝ)) /
      (duration C L n : ℝ) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hd.le
  simp only [detectorSpeed, smoothPulse_before (by norm_num : (0 : ℝ) < 1) harg,
    mul_zero]

theorem detectorSpeed_after (C L n : ℕ) {t : ℝ}
    (ht : 2 * ((n : ℝ) + 1) + 2 * (duration C L n : ℝ) ≤ t) :
    detectorSpeed C L n t = 0 := by
  have hd : (0 : ℝ) < duration C L n := by exact_mod_cast duration_pos C L n
  have harg : 1 ≤ (t - 2 * ((n : ℝ) + 1) - (duration C L n : ℝ)) /
      (duration C L n : ℝ) := by
    apply (le_div_iff₀ hd).mpr
    linarith
  simp only [detectorSpeed, smoothPulse_after (by norm_num : (0 : ℝ) < 1) harg,
    mul_zero]

theorem detectorDriftTerm_smooth {V : ℝ → Plane → Plane}
    (hV : ContDiff ℝ ∞ (Function.uncurry V)) (C L n : ℕ) :
    ContDiff ℝ ∞ (detectorDriftTerm V C L n) :=
  ((detectorSpeed_smooth C L n).comp contDiff_fst).smul
    (hV.comp (((detectorPhase_smooth C L n).comp contDiff_fst).prodMk contDiff_snd))

theorem detectorDriftTerm_before (V : ℝ → Plane → Plane) (C L n : ℕ)
    (y : ℝ × Plane) (hy : y.1 < 2 * ((n : ℝ) + 1)) :
    detectorDriftTerm V C L n y = 0 := by
  have hd : (0 : ℝ) < duration C L n := by exact_mod_cast duration_pos C L n
  rw [detectorDriftTerm, detectorSpeed_before C L n (by linarith), zero_smul]

theorem detectorDrift_smooth {V : ℝ → Plane → Plane}
    (hV : ContDiff ℝ ∞ (Function.uncurry V)) (C L : ℕ) :
    ContDiff ℝ ∞ (Function.uncurry (detectorDrift V C L)) :=
  detectorBlockSum_smooth _ (detectorDriftTerm_smooth hV C L)
    (detectorDriftTerm_before V C L)

theorem detectorDrift_periodic {V : ℝ → Plane → Plane}
    (hV : ∀ s, PlanePeriodic (V s)) (C L : ℕ) (t : ℝ) :
    PlanePeriodic (detectorDrift V C L t) := by
  intro x k
  unfold detectorDrift detectorBlockSum
  apply tsum_congr
  intro n
  simp only [detectorDriftTerm, hV _ x k]

theorem detectorDrift_before (V : ℝ → Plane → Plane) (C L : ℕ)
    {t : ℝ} (ht : t ≤ 0) (x : Plane) : detectorDrift V C L t x = 0 := by
  change (∑' n, detectorDriftTerm V C L n (t, x)) = 0
  trans (∑' _ : ℕ, (0 : Plane))
  swap
  · exact tsum_zero
  apply tsum_congr
  intro n
  apply detectorDriftTerm_before
  change t < 2 * ((n : ℝ) + 1)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

end ForcedComputation.VelocityDetector

end

end OAI

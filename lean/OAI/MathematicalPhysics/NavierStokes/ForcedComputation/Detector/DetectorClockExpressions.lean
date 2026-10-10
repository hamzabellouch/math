import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.DetectorReference
import OAI.MathematicalPhysics.NavierStokes.ShearFlows.EffectiveProfiles

namespace OAI

/-! The injection and stirring clocks are finite rational profile
expressions. Their symbolic derivatives give the prescribed rates. -/

namespace ForcedComputation.VelocityDetector
open ShearFlows

def blockStart (n : ℕ) : ℚ := 2 * ((n : ℚ) + 1)

def injectionExpression (C L n : ℕ) : ProfileExpr :=
  .ramp (blockStart n) (blockStart n + duration C L n)

def phaseExpression (C L n : ℕ) : ProfileExpr :=
  .mul (.const ((n : ℚ) + 1))
    (.ramp (blockStart n + duration C L n)
      (blockStart n + 2 * duration C L n))

theorem smoothRamp_window (a δ t : ℝ) :
    smoothRamp a (a + δ) t = smoothRamp 0 1 ((t - a) / δ) := by
  simp only [smoothRamp]
  rw [show a + δ - a = δ by ring]
  norm_num

theorem injectionExpression_val (C L n : ℕ) :
    (injectionExpression C L n).val = detectorInjectionFraction C L n := by
  funext t
  rw [injectionExpression, ProfileExpr.val_ramp]
  simp only [Rat.cast_add]
  rw [smoothRamp_window]
  simp only [blockStart, Rat.cast_mul, Rat.cast_add, Rat.cast_natCast,
    Rat.cast_ofNat, Rat.cast_one, detectorInjectionFraction]

theorem phaseExpression_val (C L n : ℕ) :
    (phaseExpression C L n).val = detectorPhase C L n := by
  funext t
  simp only [phaseExpression, ProfileExpr.val, ProfileExpr.val_ramp,
    Rat.cast_add, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_one]
  have he : (blockStart n : ℝ) + 2 * (duration C L n : ℝ) =
      ((blockStart n : ℝ) + (duration C L n : ℝ)) + (duration C L n : ℝ) := by ring
  rw [he, smoothRamp_window]
  unfold detectorPhase
  congr 2
  simp only [blockStart, Rat.cast_mul, Rat.cast_add, Rat.cast_natCast,
    Rat.cast_ofNat, Rat.cast_one]
  ring

theorem injectionExpression_diff_val (C L n : ℕ) (t : ℝ) :
    (injectionExpression C L n).diff.val t = detectorInjectionRate C L n t := by
  have hd := (injectionExpression C L n).hasDerivAt t
  rw [injectionExpression_val] at hd
  exact hd.unique (detectorInjectionFraction_hasDerivAt C L n t)

theorem phaseExpression_diff_val (C L n : ℕ) (t : ℝ) :
    (phaseExpression C L n).diff.val t = detectorSpeed C L n t := by
  have hd := (phaseExpression C L n).hasDerivAt t
  rw [phaseExpression_val] at hd
  exact hd.unique (detectorPhase_hasDerivAt C L n t)

end ForcedComputation.VelocityDetector

end OAI

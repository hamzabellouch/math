import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTestPrimitive
import Mathlib.Analysis.Calculus.BumpFunction.Normed

namespace OAI

/-! A unit-integral smooth test strictly inside each nonempty radial interval. -/

open Set MeasureTheory
open scoped ContDiff
namespace DefocusingNLS

theorem spectralUnitTest (a b : ℝ) (hab : a < b) :
    ∃ β : ℝ → ℝ, ContDiff ℝ ∞ β ∧ HasCompactSupport β ∧
      tsupport β ⊆ Ioo a b ∧ ∫ x, β x = 1 := by
  let f : ContDiffBump ((a+b)/2) :=
    { rIn := (b-a)/8
      rOut := (b-a)/4
      rIn_pos := by linarith
      rIn_lt_rOut := by linarith }
  refine ⟨f.normed volume,f.contDiff_normed,f.hasCompactSupport_normed,?_,f.integral_normed⟩
  rw [f.tsupport_normed_eq]
  intro x hx
  have hx' : |x-(a+b)/2| ≤ (b-a)/4 := by
    simpa only [Metric.mem_closedBall,Real.dist_eq,f] using hx
  constructor <;> linarith [(abs_le.mp hx').1,(abs_le.mp hx').2]

end DefocusingNLS

end OAI

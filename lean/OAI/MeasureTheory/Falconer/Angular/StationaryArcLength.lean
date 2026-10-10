import OAI.MeasureTheory.Falconer.Fourier.ActualSymbolEstimates
import OAI.MeasureTheory.Falconer.Angular.CircleLocalIntegral

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

 theorem sourceUnitDirection_periodic : Function.Periodic sourceUnitDirection (2*Real.pi) := by
  intro θ
  rw [show θ+2*Real.pi = (θ+Real.pi)+Real.pi by ring,
    sourceUnitDirection_add_pi,sourceUnitDirection_add_pi]
  apply Subtype.ext
  simp [circleAntipode]

 theorem sourceArcLength_integral_period {F : UnitCircle → ℂ}
    (hF : AEStronglyMeasurable F sourceArcLength) :
    (∫ ω, F ω ∂sourceArcLength) = ∫ θ in (-Real.pi)..Real.pi, F (sourceUnitDirection θ) := by
  have he : (∫ ω, F ω ∂sourceArcLength) = ∫ θ in (0:ℝ)..2*Real.pi, F (sourceUnitDirection θ) := by
    rw [sourceArcLength,integral_map continuous_sourceUnitDirection.measurable.aemeasurable hF]
    exact (intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 2*Real.pi)).symm
  rw [he]
  have hp : Function.Periodic (fun θ => F (sourceUnitDirection θ)) (2*Real.pi) :=
    fun θ => congrArg F (sourceUnitDirection_periodic θ)
  have hh := hp.intervalIntegral_add_eq 0 (-Real.pi)
  have he' : -Real.pi+2*Real.pi = Real.pi := by ring
  simpa only [zero_add,he'] using hh

end PlanarFalconer

end OAI

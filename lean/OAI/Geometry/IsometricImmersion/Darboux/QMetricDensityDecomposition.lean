import OAI.Geometry.IsometricImmersion.Darboux.SixVariableQ
import OAI.Geometry.IsometricImmersion.Pulses.ActualForcingCoefficient
import OAI.Geometry.IsometricImmersion.Pulses.PulseActualDensity

namespace OAI

noncomputable section
open Set Filter
open scoped ContDiff Topology BigOperators

namespace SmoothLocal.Pulse
open SmoothLocal.Geometry SmoothLocal.HighEquation

def qMetricDensityFactor (g : MetricField) (w : DarbouxState) : ℝ :=
  stateEnergy g w / ((g (statePoint w)).det*stateQDenominator g w)

def qMetricFirstLower (g : MetricField) (w : DarbouxState) : ℝ :=
  stateConnection g 1 1 w+(stateMixed g w)^2/stateQDenominator g w

def qMetricFirstError (gTau gStar : MetricField) (w : DarbouxState) : ℝ :=
  curvatureDensity gTau (statePoint w)*(qMetricDensityFactor gTau w-qMetricDensityFactor gStar w)+
    (qMetricFirstLower gTau w-qMetricFirstLower gStar w)

theorem sixVariableQ_density_split {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (hU : IsOpen U) {w : DarbouxState}
    (hw : statePoint w ∈ U) (hxx : stateQDenominator g w ≠ 0) :
    sixVariableQ g w = qMetricFirstLower g w+
      curvatureDensity g (statePoint w)*qMetricDensityFactor g w := by
  have hraw : sixVariableQ g w = stateConnection g 1 1 w+
      ((stateMixed g w)^2+gaussianCurvature g (statePoint w)*stateEnergy g w)/
        stateQDenominator g w := by
    rw [sixVariableQ_explicit hg hU hw]
    rfl
  rw [hraw]
  unfold qMetricFirstLower qMetricDensityFactor curvatureDensity
  have hdet := metricDet_ne_zero hg hw
  field_simp [hdet,hxx]
  ring

theorem sixVariableQ_metric_density_difference
    {gTau gStar : MetricField} {U : Set Coord}
    (hgTau : SmoothPositiveOn gTau U) (hgStar : SmoothPositiveOn gStar U)
    (hU : IsOpen U) {w : DarbouxState} (hw : statePoint w ∈ U)
    (hxxTau : stateQDenominator gTau w ≠ 0) (hxxStar : stateQDenominator gStar w ≠ 0) :
    sixVariableQ gTau w-sixVariableQ gStar w =
      (curvatureDensity gTau (statePoint w)-curvatureDensity gStar (statePoint w))*
        qMetricDensityFactor gStar w+qMetricFirstError gTau gStar w := by
  rw [sixVariableQ_density_split hgTau hU hw hxxTau,
    sixVariableQ_density_split hgStar hU hw hxxStar]
  unfold qMetricFirstError
  ring

theorem qMetricDensityFactor_at_height {g : MetricField} {U : Set Coord}
    (hg : SmoothPositiveOn g U) (z : Coord → ℝ) {p : Coord} (hp : p ∈ U)
    (hxx : covHessian g z p 0 0 ≠ 0) :
    qMetricDensityFactor g (qSolutionJet z p) = 2*forcingCoefficient g z p := by
  unfold qMetricDensityFactor
  rw [stateQDenominator_qSolutionJet]
  unfold stateEnergy
  rw [statePoint_qSolutionJet,stateGradient_qSolutionJet,jetEnergy_at_height hg hp z,
    forcingCoefficient_eq_energy hg z hp]
  have hdet := metricDet_ne_zero hg hp
  field_simp [hdet,hxx]

theorem actual_Q_metric_forcing_decomposition
    {gTau gStar : MetricField} {U : Set Coord}
    (hgTau : SmoothPositiveOn gTau U) (hgStar : SmoothPositiveOn gStar U)
    (hU : IsOpen U) (z : Coord → ℝ) {p : Coord} (hp : p ∈ U)
    (hxxTau : covHessian gTau z p 0 0 ≠ 0) (hxxStar : covHessian gStar z p 0 0 ≠ 0) :
    sixVariableQ gTau (qSolutionJet z p)-sixVariableQ gStar (qSolutionJet z p) =
      2*forcingCoefficient gStar z p*(curvatureDensity gTau p-curvatureDensity gStar p)+
        qMetricFirstError gTau gStar (qSolutionJet z p) := by
  rw [sixVariableQ_metric_density_difference hgTau hgStar hU
    (by simpa only [statePoint_qSolutionJet] using hp)
    (by simpa only [stateQDenominator_qSolutionJet] using hxxTau)
    (by simpa only [stateQDenominator_qSolutionJet] using hxxStar),
    statePoint_qSolutionJet,qMetricDensityFactor_at_height hgStar z hp hxxStar]
  ring

theorem actual_Q_metric_forcing_leading_identity
    {gTau gStar : MetricField} {U : Set Coord}
    (hgTau : SmoothPositiveOn gTau U) (hgStar : SmoothPositiveOn gStar U)
    (hU : IsOpen U) (z : Coord → ℝ) {p : Coord} (hp : p ∈ U)
    (hxxTau : covHessian gTau z p 0 0 ≠ 0) (hxxStar : covHessian gStar z p 0 0 ≠ 0)
    (leading : ℝ) :
    (sixVariableQ gTau (qSolutionJet z p)-sixVariableQ gStar (qSolutionJet z p))-
        2*forcingCoefficient gStar z p*leading =
      2*forcingCoefficient gStar z p*((curvatureDensity gTau p-curvatureDensity gStar p)-leading)+
        qMetricFirstError gTau gStar (qSolutionJet z p) := by
  rw [actual_Q_metric_forcing_decomposition hgTau hgStar hU z hp hxxTau hxxStar]
  ring

end SmoothLocal.Pulse

end

end OAI

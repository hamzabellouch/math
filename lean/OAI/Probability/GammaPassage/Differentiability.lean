import OAI.Probability.GammaPassage.ActualNoCorner
import OAI.Probability.GammaPassage.AnalyticSpecialization
import OAI.Probability.GammaPassage.ActualTimeConstant
import OAI.Probability.GammaPassage.Target

namespace OAI

/-!
# Differentiability for Gamma weights

Theorem `thm:gamma-differentiability` of
*Strict convexity and differentiability of the planar exponential first-passage limit shape*.
The almost-sure passage-time limit is asserted for each fixed real direction.
-/

namespace GammaFPP
open PlanarFPP MeasureTheory

/-- Differentiability and regular C¹ boundary charts for planar Gamma first-passage percolation. -/
theorem gamma_differentiability : GammaDifferentiabilityTarget := by
  intro shape rate hs hr Ω _ P τ h
  have hnc : Analytic.NoCornerWedge (gammaMeanNorm h hs hr) := by
    intro b hb
    simpa [PlanarFPP.extremeSlope] using
      CrossingBridge.gamma_no_corner h hs hr b hb
  exact Analytic.gammaMeanNorm_target_conjunction_of_inputs h hs hr
    (h.isTimeConstant hs hr) hnc

end GammaFPP

end OAI

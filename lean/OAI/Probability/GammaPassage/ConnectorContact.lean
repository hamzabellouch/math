import OAI.Probability.FirstPassage.SupportContactEstimate
import OAI.Probability.GammaPassage.MeanNorm

namespace OAI

namespace GammaFPP.CrossingBridge
open PlanarFPP MeasureTheory Set
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

theorem gamma_connector_support_gap
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (b : ℝ) (plus : Bool) (ε C : ℝ) (hε : 0 < ε) (hC : 0 < C) :
    ∃ D0 : ℝ, 1 ≤ D0 ∧ ∀ s : ℝ, 0 < s → ∀ z : Plane,
      D0*s ≤ xCoord z → rCoord b z ∈ contactSide plus → |rCoord b z| ≤ 3*C*s →
      gammaMeanNorm h hs hr z -
        (gammaMeanNorm h hs hr (direction b)*xCoord z +
          extremeSlope (gammaMeanNorm h hs hr) b plus*rCoord b z) ≤ ε*s/4 :=
  connector_support_gap _ (gammaMeanNorm_laws h hs hr) b plus ε C hε hC

end GammaFPP.CrossingBridge

end OAI

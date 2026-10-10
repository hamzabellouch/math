import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFluxRobin
import Mathlib.Analysis.Analytic.Constructions

namespace OAI

/-! Fixed profile gauges and flux weights preserve boundary holomorphy. -/

namespace DefocusingNLS

theorem spectralGaugeRobin_analyticAt (q dq : ℂ)
    (M : ℂ → ℂ × ℂ →L[ℂ] ℂ × ℂ) (z : ℂ) (hM : AnalyticAt ℂ M z) :
    AnalyticAt ℂ (fun t => spectralGaugeRobin q dq (M t)) z := by
  let A := (ContinuousLinearMap.compL ℂ (ℂ × ℂ) (ℂ × ℂ) (ℂ × ℂ)).flip
    (spectralGaugeColumns q)
  let B := ContinuousLinearMap.compL ℂ (ℂ × ℂ) (ℂ × ℂ) (ℂ × ℂ)
    (spectralGaugeInverse q)
  have hA : AnalyticAt ℂ (fun t => A (M t)) z := (A.analyticAt (M z)).comp hM
  have hs : AnalyticAt ℂ (fun t => A (M t)-spectralGaugeColumns dq) z :=
    hA.sub analyticAt_const
  exact (B.analyticAt (A (M z)-spectralGaugeColumns dq)).comp
    (f := fun t : ℂ => A (M t)-spectralGaugeColumns dq) hs

theorem spectralFluxBoundary_analyticAt (R μ A : ℝ)
    (M : ℂ → ℂ × ℂ →L[ℂ] ℂ × ℂ) (z : ℂ) (hM : AnalyticAt ℂ M z) :
    AnalyticAt ℂ (fun t => spectralFluxBoundary R μ A (M t)) z := by
  exact ((hM.const_smul (c := (μ : ℂ))).sub analyticAt_const).const_smul (c := ((R : ℂ)^11))

end DefocusingNLS

end OAI

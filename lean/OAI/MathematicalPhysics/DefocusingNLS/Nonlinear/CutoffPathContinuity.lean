import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingPerturbationContinuity
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffStepForcing

namespace OAI

/-! # Scale continuity of the actual sampled cutoff histories

The smooth profile and exact cutoff residual vary continuously in the
finite-time path norm.  This supplies the concrete parameter hypotheses
for the nonlinear step continuity theorem.
-/

open Set
open scoped SchwartzMap ContDiff

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem continuous_sampledCutoffProfilePath (a k T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) :
    Continuous (fun L : {L : ℝ // 1 ≤ L} =>
      sampledCutoffProfilePath a k L.1 T ha ha1 hk L.2 χ hχ Q hQ) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (continuous_cutoffProfile_sample a k ha ha1 hk χ hχ Q hQ).comp
    (continuous_expandingRadiusCurve_family T id continuous_id)

theorem continuous_sampledCutoffResidualPath (a k T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (χ : 𝓢(E, ℝ)) (hχ : HasCompactSupport (χ : E → ℝ))
    (hχone : ∀ x : E, ‖x‖ < 1 / 2 → χ x = 1)
    (hχzero : ∀ x : E, 2 < ‖x‖ → χ x = 0)
    (m : ℕ) (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) :
    Continuous (fun L : {L : ℝ // 1 ≤ L} =>
      sampledCutoffResidualPath a k L.1 T ha ha1 hk L.2 χ hχ hχone hχzero m Q hQ) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact (continuous_cutoffResidual_sample a k ha ha1 hk χ hχ hχone hχzero m Q hQ).comp
    (continuous_expandingRadiusCurve_family T id continuous_id)

theorem continuous_sampledCutoffDefectPath (a k T : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (χ : 𝓢(E, ℝ)) (hχ : HasCompactSupport (χ : E → ℝ))
    (hχone : ∀ x : E, ‖x‖ < 1 / 2 → χ x = 1)
    (hχzero : ∀ x : E, 2 < ‖x‖ → χ x = 0)
    (m : ℕ) (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) :
    Continuous (fun L : {L : ℝ // 1 ≤ L} =>
      sampledCutoffDefectPath a k L.1 T ha ha1 hk L.2 χ hχ hχone hχzero m Q hQ) :=
  (continuous_sampledCutoffResidualPath a k T ha ha1 hk χ hχ hχone hχzero m Q hQ).const_smul
    (-Complex.I : ℂ)

end DefocusingNLS

end OAI

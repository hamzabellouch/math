import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffProfileEndpoint
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffPathContinuity
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingProfileContinuity

namespace OAI

/-! # Strong continuity of the actual cutoff linear endpoint -/

open scoped SchwartzMap ContDiff NNReal

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "Radius" => {L : ℝ // 1 ≤ L}

attribute [local irreducible] cutoffProfileEndpoint expandingProfileTrajectory

theorem continuous_cutoffProfileEndpoint (a b k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (m : ℕ) (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (Qp : E → ℂ) (hQp : ContDiff ℝ ∞ Qp) (Q : ℝ) (hQ : 0 ≤ Q)
    (hqb : ∀ L : Radius, ‖cutoffProfileCoefficient a k ha1 hk χ hχ Qp hQp L‖ ≤ Q)
    (T : ℝ≥0) :
    Continuous (fun p : Radius × FourierL2 =>
      cutoffProfileEndpoint a b k ha ha1 hk m χ hχ Qp hQp Q hQ hqb T p.1 p.2) := by
  have hq := (continuous_sampledCutoffProfilePath a k T ha ha1 hk χ hχ Qp hQp).comp
    (continuous_fst : Continuous (fun p : Radius × FourierL2 => p.1))
  have hc := continuous_expandingProfileTrajectory_family a b k T Q ha ha1 hk T.2 m hQ
    (fun p : Radius × FourierL2 => p.1) continuous_fst
    (fun p : Radius × FourierL2 => sampledCutoffProfilePath a k p.1.1 T ha ha1 hk p.1.2 χ hχ Qp hQp)
    hq (fun p t => hqb (expandingRadiusCurve p.1.1 T p.1.2 t))
    (fun p : Radius × FourierL2 => p.2) continuous_snd
  simpa only [cutoffProfileEndpoint_apply, Function.comp_def] using
    (continuous_eval_const ⟨T, T.2, le_rfl⟩).comp hc

end DefocusingNLS

end OAI

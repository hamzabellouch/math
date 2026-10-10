import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.FixedCutoffProfileBound

namespace OAI

/-! # The fixed-norm profile agrees with physical sampling at its own radius -/

open scoped SchwartzMap ContDiff
namespace DefocusingNLS
local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "Radius" => {L : ℝ // 1 ≤ L}

theorem fixedCutoffProfile_self (a k : ℝ) (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k)
    (L : Radius) (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) :
    fixedCutoffProfile a k ha ha1 hk L χ hχ Q hQ L.1 =
      physicalSchwartzTorusSamplingCLM a k L.1 ha1 hk L.2
        (cutoffProfileSchwartz L.1 (by linarith [L.2]) χ hχ Q hQ) := by
  rw [fixedCutoffProfile_eq_transfer]
  ext n
  rw [expandingNearbyTransfer_apply, div_self (expandingSobolevWeight_pos a k L.1 L.2 n).ne']
  simp

end DefocusingNLS

end OAI

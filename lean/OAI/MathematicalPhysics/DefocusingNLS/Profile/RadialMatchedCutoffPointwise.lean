import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffPointwiseBound
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialProfileDerivativeBounds
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedProfileBounds

namespace OAI

/-! # The matched profile has one cutoff amplitude bound for every Sobolev order -/

open scoped SchwartzMap ContDiff

namespace DefocusingNLS
open ProfileCertificate

local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "T" => UnitAddTorus (Fin 12)

theorem radialMatchedCartesian_bounded (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n + radialInnerShootingThreshold) z)
      (n + radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z = 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y : E, ‖radialMatchedCartesian n z y‖ ≤ M := by
  obtain ⟨M, hM, hb⟩ := radialMatchedEvenProfile_bounded n z hX hz
  refine ⟨M, hM, fun y => ?_⟩
  have he : radialMatchedEvenProfile n z ‖y‖ = radialMatchedCartesian n z y := by
    rw [radialMatchedEvenProfile_nonneg n z _ (norm_nonneg y)]
    rfl
  simpa only [he] using hb ‖y‖

theorem radialMatchedCutoff_pointwise_bound (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n + radialInnerShootingThreshold) z)
      (n + radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z = 0)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (hχzero : ∀ y : E, 1 ≤ ‖y‖ → χ y = 0) (m : ℕ) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ (k : ℝ) (hk : 8 < k) (L : ℝ) (hL : 1 ≤ L) (x : T),
      ‖expandingUnitTorusFunction (radialShootingA n) k L
        (schwartzTorusSample (radialShootingA n) k L
          (radialShootingA_bounds n (profileMatchingParameter z)).2 hk hL
          (radianFourierKernel (cutoffProfileSchwartz L (by linarith) χ hχ
            (radialMatchedCartesian n z) (radialMatchedCartesian_contDiff n z hX hz)))) x‖ ^ (2 * m) ≤ P := by
  obtain ⟨M, hM, hMb⟩ := radialMatchedCartesian_bounded n z hX hz
  refine ⟨(SchwartzMap.seminorm ℝ 0 0 χ * M) ^ (2 * m), by positivity, ?_⟩
  intro k hk L hL x
  apply pow_le_pow_left₀ (norm_nonneg _) _ (2 * m)
  exact sampledCutoff_pointwise_bound (radialShootingA n) k L
    (radialShootingA_bounds n (profileMatchingParameter z)).1
    (radialShootingA_bounds n (profileMatchingParameter z)).2 hk hL χ hχ hχzero
    (radialMatchedCartesian n z) (radialMatchedCartesian_contDiff n z hX hz) M hM hMb x

end DefocusingNLS

end OAI

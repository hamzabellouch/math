import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffContinuousLinearization
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedProfileBounds
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialCartesianEquation

namespace OAI

/-! # Continuous nonlinear cutoff steps for the actual matched stationary profile -/

open scoped SchwartzMap ContDiff NNReal

namespace DefocusingNLS
open ProfileCertificate

local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "Radius" => {L : ℝ // 1 ≤ L}

theorem radialMatched_continuous_nonlinear_steps (n : ℕ) (z : ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n + radialInnerShootingThreshold) z)
      (n + radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z = 0) (k : ℝ) (hk : 8 < k)
    (χ : 𝓢(E, ℝ)) (hχ : HasCompactSupport (χ : E → ℝ))
    (hχone : ∀ x : E, ‖x‖ < 1 / 2 → χ x = 1)
    (hχzero : ∀ x : E, 1 ≤ ‖x‖ → χ x = 0) (T : ℝ≥0) :
    let a := radialShootingA n
    let ha := (radialShootingA_bounds n (profileMatchingParameter z)).1
    let ha1 := (radialShootingA_bounds n (profileMatchingParameter z)).2
    let b := radialShootingB (profileMatchingParameter z)
    let Qp := radialMatchedCartesian n z
    let hQp := radialMatchedCartesian_contDiff n z hX hz
    ∀ (Q : ℝ) (hQ : 0 ≤ Q),
    ∀ hqb : ∀ L : Radius, ‖cutoffProfileCoefficient a k ha1 hk
      (χ.postcompCLM Complex.ofRealCLM) (hasCompactSupport_complexCutoff χ hχ) Qp hQp L‖ ≤ Q,
    HasContinuousCutoffNonlinearSteps a b k ha ha1 hk (n + radialInnerShootingThreshold)
      (χ.postcompCLM Complex.ofRealCLM) (hasCompactSupport_complexCutoff χ hχ) Qp hQp Q hQ hqb T := by
  intro a ha ha1 b Qp hQp Q hQ hqb
  have hm : (n + radialInnerShootingThreshold : ℝ) ≠ 0 := by
    exact_mod_cast (radialShootingInner_power_pos n (profileMatchingParameter z)).ne'
  have ham : 2 * a * ((n + radialInnerShootingThreshold : ℕ) : ℝ) = 1 := by
    dsimp [a, radialShootingA]
    push_cast
    field_simp
  obtain ⟨N, hN⟩ := exists_cutoffContinuousNonlinear_steps_order a b k ha ha1 hk
    (n + radialInnerShootingThreshold) ham χ hχ hχone hχzero T
  obtain ⟨B, hB, hb⟩ := radialMatchedCartesian_finite_symbol n z hX hz N
  exact hN Qp hQp B hB hb (radialMatchedCartesian_stationary n z hX hz) Q hQ hqb

end DefocusingNLS

end OAI

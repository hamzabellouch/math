import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPrincipalPotential
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialUniformExteriorPressure

namespace OAI

/-! # The k-independent principal bound for the constructed profile

The proved global pressure bound supplies the actual L² principal
potential, with the manuscript's constant 1+1/a.
-/

open MeasureTheory Filter

namespace DefocusingNLS
open ProfileCertificate

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem radialMatched_principal_bound :
    ∀ᶠ n in atTop, ∀ z : ProfileMatchingBall,
      (hX : HasRadialExterior (radialShootingNu (n + radialInnerShootingThreshold) z)
        (n + radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius)) →
      (hz : radialMatchingMap n z = 0) →
      ∃ B : Lp ℂ 2 (volume : Measure E) →L[ℝ] Lp ℂ 2 (volume : Measure E),
        ‖B‖ ≤ 1 + 1 / radialShootingA n ∧
        ∀ f : Lp ℂ 2 (volume : Measure E), B f =ᵐ[volume]
          (fun x => -Complex.I * oddPowerDerivative (n + radialInnerShootingThreshold)
            (radialMatchedCartesian n z x) (f x)) := by
  filter_upwards [radialMatched_global_pressure_bound] with n hn z hX hz
  have hQ := (radialMatchedCartesian_contDiff n z hX hz).continuous
  have hQB (x : E) : ‖radialMatchedCartesian n z x‖ ^
      (2 * (n + radialInnerShootingThreshold)) ≤ 1 :=
    hn z ‖x‖ (norm_nonneg x)
  refine ⟨homogeneousPrincipalPotential (n + radialInnerShootingThreshold)
    (radialMatchedCartesian n z) hQ 1 zero_le_one hQB, ?_, ?_⟩
  · have hA := (radialShootingA_bounds n (profileMatchingParameter z)).1
    have hp := radialShootingA_power n (profileMatchingParameter z)
    have hc : 2 * ((n + radialInnerShootingThreshold : ℕ) : ℝ) + 1 =
        1 + 1 / radialShootingA n := by
      have hquot : 2 * ((n + radialInnerShootingThreshold : ℕ) : ℝ) =
          1 / radialShootingA n := (eq_div_iff hA.ne').mpr (by nlinarith)
      rw [hquot, add_comm]
    simpa only [mul_one, hc] using homogeneousPrincipalPotential_norm_le
      (n + radialInnerShootingThreshold) (radialMatchedCartesian n z) hQ 1 zero_le_one hQB
  · intro f
    exact homogeneousPrincipalAction_ae (n + radialInnerShootingThreshold)
      (radialMatchedCartesian n z) hQ 1 zero_le_one hQB f

end DefocusingNLS

end OAI

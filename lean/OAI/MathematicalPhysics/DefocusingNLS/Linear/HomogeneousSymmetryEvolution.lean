import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousPhysicalEigenvector
import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousProfileSymmetries
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPhaseMode
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialTranslationMode
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialMatchedSymbol

namespace OAI

/-! # The physical phase, translation and time directions are actual eigenvectors -/

open scoped ContDiff ZeroAtInfty NNReal

namespace DefocusingNLS
open ProfileCertificate
local notation "E" => EuclideanSpace ℝ (Fin 12)

attribute [local irreducible] homogeneousLinearizedStep

section
variable (n : ℕ) (z : ProfileCertificate.ProfileMatchingBall)
    (hX : HasRadialExterior (radialShootingNu (n + radialInnerShootingThreshold) z)
      (n + radialInnerShootingThreshold) (radialShootingM z) (Real.log innerBoundaryRadius))
    (hz : radialMatchingMap n z = 0) (k : ℝ)
    (ha : 0 < radialShootingA n) (ha1 : radialShootingA n < 1) (hk : 8 < k)
    (q : HomogeneousY (radialShootingA n) k)
    (hq : ∀ y, homogeneousPhysicalCLM (radialShootingA n) k ha ha1 hk q y =
      radialMatchedCartesian n z y)

local notation "a" => radialShootingA n
local notation "b" => radialShootingB (profileMatchingParameter z)
local notation "m" => n + radialInnerShootingThreshold
local notation "Q" => radialMatchedCartesian n z
local notation "S" => homogeneousLinearizedStep a b k ha ha1 hk m q

include hX hz

private theorem symbol : ∀ j : ℕ, ∃ D : ℝ, ∀ y : E, 1 ≤ ‖y‖ →
    ‖iteratedFDeriv ℝ j Q y‖ ≤ D * ‖y‖ ^ (-2 * a - (j : ℝ)) := by
  intro j
  obtain ⟨D, _, hD⟩ := radialMatchedCartesian_symbol n z hX hz j
  exact ⟨D, hD⟩

include hq

theorem radialMatched_phase_evolution (u : HomogeneousY a k)
    (hu : ∀ y, homogeneousPhysicalCLM a k ha ha1 hk u y = Complex.I * Q y)
    (s : ℝ≥0) : S s u = u := by
  obtain ⟨qH, hH⟩ := radialMatchedCartesian_homogeneous n z hX hz (k + 2) ha ha1 (by linarith)
  have h := homogeneousLinearized_eigenvector_of_physical a b k ha ha1 hk m q u
    (Complex.I • qH) 0 (fun x => by
      rw [map_smul]
      change Complex.I * homogeneousPhysicalCLM a (k + 2) ha ha1 (by linarith) qH x = _
      rw [hH, hu]) (fun x => by
      rw [show (fun y : E => homogeneousPhysicalCLM a k ha ha1 hk q y) = Q from funext hq,
        show (fun y : E => homogeneousPhysicalCLM a k ha ha1 hk u y) =
          (fun y => Complex.I * Q y) from funext hu]
      simpa only [Complex.ofReal_zero, zero_mul] using radialMatched_phaseMode n z hX hz x) s
  simpa only [zero_mul, Real.exp_zero, one_smul] using h

theorem radialMatched_translation_evolution (v : E) (u : HomogeneousY a k)
    (hu : ∀ y, homogeneousPhysicalCLM a k ha ha1 hk u y = cartesianDerivative v Q y)
    (s : ℝ≥0) : S s u = Real.exp ((1 / 2 : ℝ) * s) • u := by
  obtain ⟨uH, hH⟩ := homogeneous_profile_directional_derivative a (k + 2) ha ha1
    (by linarith) Q (radialMatchedCartesian_contDiff n z hX hz) (symbol n z hX hz) v
  apply homogeneousLinearized_eigenvector_of_physical a b k ha ha1 hk m q u uH (1 / 2)
    (fun x => (hH x).trans (hu x).symm)
  intro x
  rw [show (fun y : E => homogeneousPhysicalCLM a k ha ha1 hk q y) = Q from funext hq,
    show (fun y : E => homogeneousPhysicalCLM a k ha ha1 hk u y) =
      cartesianDerivative v Q from funext hu]
  simpa only [hu, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
    radialMatched_translationMode n z hX hz v x

theorem radialMatched_time_evolution (u : HomogeneousY a k)
    (hu : ∀ y, homogeneousPhysicalCLM a k ha ha1 hk u y =
      ((a : ℂ) - Complex.I * (b : ℂ)) * Q y + cartesianTransport Q y)
    (s : ℝ≥0) : S s u = Real.exp (s : ℝ) • u := by
  obtain ⟨qH, hqH⟩ := radialMatchedCartesian_homogeneous n z hX hz (k + 2) ha ha1 (by linarith)
  obtain ⟨uH, hH⟩ := homogeneous_profile_time_direction a b (k + 2) ha ha1
    (by linarith) m Q (radialMatchedCartesian_contDiff n z hX hz) (symbol n z hX hz)
    qH hqH (radialMatchedCartesian_stationary n z hX hz)
  have h := homogeneousLinearized_eigenvector_of_physical a b k ha ha1 hk m q u uH 1
    (fun x => (hH x).trans (hu x).symm) (fun x => by
      rw [show (fun y : E => homogeneousPhysicalCLM a k ha ha1 hk q y) = Q from funext hq,
        show (fun y : E => homogeneousPhysicalCLM a k ha ha1 hk u y) =
          (fun y => ((a : ℂ) - Complex.I * (b : ℂ)) * Q y + cartesianTransport Q y) from funext hu]
      simpa only [hu, Complex.ofReal_one, one_mul] using radialMatched_timeMode n z hX hz x) s
  simpa only [one_mul] using h

end
end DefocusingNLS

end OAI

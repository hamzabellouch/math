import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffProfileModeDerivative
import OAI.MathematicalPhysics.DefocusingNLS.Linear.FourierCoordinateDerivative
import OAI.MathematicalPhysics.DefocusingNLS.Profile.CartesianTransportCalculus

namespace OAI

/-! # Strong differentiation of the cutoff profile in a fixed torus norm -/

open Set Filter Topology
open scoped SchwartzMap ContDiff
namespace DefocusingNLS
local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "Radius" => {L : ℝ // 1 ≤ L}

noncomputable def fixedCutoffProfile (a k : ℝ) (ha : 0 < a)
    (ha1 : a < 1) (hk : 8 < k) (M : Radius)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (R : ℝ) : FourierL2 :=
  expandingScaleTransfer a k 1 M.1 ha hk le_rfl M.2
    (physicalSchwartzTorusSamplingCLM a k 1 ha1 hk le_rfl
      (compactDilationFamily χ hχ Q hQ R))

theorem fixedCutoffProfile_coordinate (a k : ℝ) (ha : 0 < a)
    (ha1 : a < 1) (hk : 8 < k) (M : Radius)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (R : ℝ) (n : frequencyLattice) :
    fixedCutoffProfile a k ha ha1 hk M χ hχ Q hQ R n =
      (expandingSobolevWeight a k M.1 n : ℂ) *
        schwartzLatticeCoefficient 1 (radianFourierKernel (compactDilationFamily χ hχ Q hQ R)) n := by
  change (expandingScaleRatio a k 1 M.1 n : ℂ) *
    ((expandingSobolevWeight a k 1 n : ℂ) * _) = _
  unfold expandingScaleRatio
  rw [Complex.ofReal_div, ← mul_assoc, div_mul_cancel₀ _
    (Complex.ofReal_ne_zero.mpr (expandingSobolevWeight_pos a k 1 le_rfl n).ne')]
  rfl

theorem continuous_fixedCutoffProfile (a k : ℝ) (ha : 0 < a)
    (ha1 : a < 1) (hk : 8 < k) (M : Radius)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) :
    Continuous (fixedCutoffProfile a k ha ha1 hk M χ hχ Q hQ) :=
  (expandingScaleTransfer a k 1 M.1 ha hk le_rfl M.2).continuous.comp
    ((physicalSchwartzTorusSamplingCLM a k 1 ha1 hk le_rfl).continuous.comp
      (continuous_compactDilationFamily χ hχ Q hQ))

attribute [local irreducible] fixedCutoffProfile expandingScaleTransfer

theorem hasDerivAt_fixedCutoffProfile_logRadius (a k : ℝ) (ha : 0 < a)
    (ha1 : a < 1) (hk : 8 < k) (M : Radius)
    (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (L s : ℝ) (hL : 0 < L) :
    HasDerivAt (fun t => fixedCutoffProfile a k ha ha1 hk M χ hχ Q hQ (expandingRadius L t))
      (fixedCutoffProfile a k ha ha1 hk M χ hχ (cartesianTransport Q)
        (cartesianTransport_contDiff Q hQ) (expandingRadius L s)) s := by
  let u := fun t => fixedCutoffProfile a k ha ha1 hk M χ hχ Q hQ (expandingRadius L t)
  let v := fun t => fixedCutoffProfile a k ha ha1 hk M χ hχ (cartesianTransport Q)
    (cartesianTransport_contDiff Q hQ) (expandingRadius L t)
  have hRc : Continuous (expandingRadius L) := by unfold expandingRadius; fun_prop
  have hv : Continuous v := (continuous_fixedCutoffProfile a k ha ha1 hk M χ hχ
    (cartesianTransport Q) (cartesianTransport_contDiff Q hQ)).comp hRc
  apply hasDerivAt_fourierL2_of_coordinates u v (s - 1) (s + 1) s hv.continuousOn _
    (by constructor <;> linarith)
  intro t _ n
  have hc := (hasDerivAt_cutoffProfile_coefficient L t hL χ hχ Q hQ n).const_mul
    (expandingSobolevWeight a k M.1 n : ℂ)
  have he (r : ℝ) : schwartzLatticeCoefficient (expandingRadius L r)
      (radianFourierKernel (cutoffProfileSchwartz (expandingRadius L r)
        (mul_pos hL (Real.exp_pos _)) χ hχ Q hQ)) n =
      schwartzLatticeCoefficient 1 (radianFourierKernel
        (compactDilationFamily χ hχ Q hQ (expandingRadius L r))) n :=
    cutoffProfile_coefficient_fixed_scale _ _ χ hχ Q hQ n
  have hd : (((2 * Real.pi) ^ (12 : ℕ))⁻¹ : ℝ) *
      radianFourierIntegral (fun x => χ x * fderiv ℝ Q (expandingRadius L t • x)
        ((expandingRadius L t / 2) • x)) (n : E) =
      schwartzLatticeCoefficient 1 (radianFourierKernel
        (compactDilationFamily χ hχ (cartesianTransport Q)
          (cartesianTransport_contDiff Q hQ) (expandingRadius L t))) n := by
    have harg (x : E) : (expandingRadius L t / 2) • x =
        (1 / 2 : ℝ) • (expandingRadius L t • x) := by
      rw [smul_smul]
      congr 1
      ring
    simp only [schwartzLatticeCoefficient, mul_one, inv_one, one_smul,
      radianFourierKernel_apply, harg]
    rfl
  simpa only [he, hd, u, v, fixedCutoffProfile_coordinate] using hc

end DefocusingNLS

end OAI

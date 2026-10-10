import OAI.MathematicalPhysics.DefocusingNLS.Linear.SobolevTranslation
import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzSamplingContinuity
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadianFourierDerivatives
import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingPhysicalLocalization
import OAI.MathematicalPhysics.DefocusingNLS.Linear.FourierCoordinateDerivative
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.NormedCurveTaylor

namespace OAI

/-! # Differentiation and Taylor expansion of normalized sampled translations -/

open Set
open scoped SchwartzMap LineDeriv RealInnerProductSpace
namespace DefocusingNLS
local notation "E" => EuclideanSpace ℝ (Fin 12)

private theorem continuous_normalizedTranslation (L : ℝ) (v : E) :
    Continuous (fun t : ℝ => euclideanToTorus ((t / L) • v)) := by
  unfold euclideanToTorus
  apply continuous_pi
  intro j
  exact (AddCircle.continuous_mk' (2 * Real.pi)).comp (by fun_prop)

attribute [local irreducible] sobolevTranslation

/-- Translation by `t*v/L` of the sampled vector differentiates to the sample
of the physical directional derivative. -/
theorem hasDerivAt_translated_schwartzSample (a k L : ℝ) (ha1 : a < 1)
    (hk : 8 < k) (hL : 1 ≤ L) (ψ : 𝓢(E, ℂ)) (v : E) (s : ℝ) :
    HasDerivAt (fun t : ℝ => sobolevTranslation (euclideanToTorus ((t / L) • v))
      (physicalSchwartzTorusSamplingCLM a k L ha1 hk hL ψ))
      (sobolevTranslation (euclideanToTorus ((s / L) • v))
        (physicalSchwartzTorusSamplingCLM a k L ha1 hk hL (∂_{v} ψ))) s := by
  let u := fun t : ℝ => sobolevTranslation (euclideanToTorus ((t / L) • v))
    (physicalSchwartzTorusSamplingCLM a k L ha1 hk hL ψ)
  let d := fun t : ℝ => sobolevTranslation (euclideanToTorus ((t / L) • v))
    (physicalSchwartzTorusSamplingCLM a k L ha1 hk hL (∂_{v} ψ))
  have hc : Continuous d := (continuous_sobolevTranslation _).comp
    (continuous_normalizedTranslation L v)
  apply hasDerivAt_fourierL2_of_coordinates u d (s - 1) (s + 1) s hc.continuousOn _
    (by constructor <;> linarith)
  intro t _ n
  have ht := (((((hasDerivAt_id t).div_const L).mul_const ⟪v, (n : E)⟫).ofReal_comp.mul_const Complex.I).cexp).mul_const
      (physicalSchwartzTorusSamplingCLM a k L ha1 hk hL ψ n)
  simp only [id_eq, one_div] at ht
  convert ht using 1
  · ext r
    simp only [u, sobolevTranslation_apply, torusCharacter_euclidean,
      spatialFourierCharacter, real_inner_smul_left]
  · simp only [d, sobolevTranslation_apply, torusCharacter_euclidean,
      spatialFourierCharacter, real_inner_smul_left, physicalSchwartzTorusSamplingCLM_apply]
    change _ * ((expandingSobolevWeight a k L n : ℂ) *
      schwartzLatticeCoefficient L (radianFourierKernel (∂_{v} ψ)) n) = _
    simp only [schwartzLatticeCoefficient, radianFourierKernel_lineDeriv,
      real_inner_smul_left, real_inner_comm (n : E) v, Complex.ofReal_mul]
    change _ = _ * ((expandingSobolevWeight a k L n : ℂ) *
      schwartzLatticeCoefficient L (radianFourierKernel ψ) n)
    simp only [schwartzLatticeCoefficient]
    ring

theorem translated_schwartzSample_taylor (a k L : ℝ) (ha1 : a < 1)
    (hk : 8 < k) (hL : 1 ≤ L) (ψ : 𝓢(E, ℂ)) (v : E) :
    ‖sobolevTranslation (euclideanToTorus ((1 / L) • v))
        (physicalSchwartzTorusSamplingCLM a k L ha1 hk hL ψ) -
      physicalSchwartzTorusSamplingCLM a k L ha1 hk hL ψ -
      physicalSchwartzTorusSamplingCLM a k L ha1 hk hL (∂_{v} ψ)‖ ≤
        ‖physicalSchwartzTorusSamplingCLM a k L ha1 hk hL (∂_{v} (∂_{v} ψ))‖ := by
  have h := normedCurve_firstOrder_bound
    (fun t : ℝ => sobolevTranslation (euclideanToTorus ((t / L) • v))
      (physicalSchwartzTorusSamplingCLM a k L ha1 hk hL ψ))
    (fun t : ℝ => sobolevTranslation (euclideanToTorus ((t / L) • v))
      (physicalSchwartzTorusSamplingCLM a k L ha1 hk hL (∂_{v} ψ)))
    (fun t : ℝ => sobolevTranslation (euclideanToTorus ((t / L) • v))
      (physicalSchwartzTorusSamplingCLM a k L ha1 hk hL (∂_{v} (∂_{v} ψ))))
    1 ‖physicalSchwartzTorusSamplingCLM a k L ha1 hk hL (∂_{v} (∂_{v} ψ))‖
    (norm_nonneg _)
    (fun t _ => hasDerivAt_translated_schwartzSample a k L ha1 hk hL ψ v t)
    (fun t _ => hasDerivAt_translated_schwartzSample a k L ha1 hk hL (∂_{v} ψ) v t)
    (fun t _ => (sobolevTranslation _).norm_map _ |>.le) 1 (by norm_num)
  have hzero : euclideanToTorus ((0 / L) • v) = 0 := by
    ext j
    simp [euclideanToTorus]
  simpa only [hzero, sobolevTranslation_zero, one_smul, abs_one, one_pow, mul_one] using h

end DefocusingNLS

end OAI

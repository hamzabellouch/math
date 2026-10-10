import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzSampleDerivativeBound
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffSymbolSampling

namespace OAI

/-! # A uniform quadratic translation remainder for cutoff profiles -/

open scoped SchwartzMap LineDeriv ContDiff
namespace DefocusingNLS
local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem cutoffProfile_translation_taylor (a k : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (hk : 8 < k) (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (hχzero : ∀ y : E, 1 ≤ ‖y‖ → χ y = 0)
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q)
    (hsymbol : ∀ n : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ y : E, y ≠ 0 →
      ‖iteratedFDeriv ℝ n Q y‖ ≤ D * ‖y‖ ^ (-2 * a - (n : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℝ) (hL : 1 ≤ L) (v : E),
      let ψ := cutoffProfileSchwartz L (by linarith) χ hχ Q hQ
      ‖sobolevTranslation (euclideanToTorus ((1 / L) • v))
          (physicalSchwartzTorusSamplingCLM a k L ha1 hk hL ψ) -
        physicalSchwartzTorusSamplingCLM a k L ha1 hk hL ψ -
        physicalSchwartzTorusSamplingCLM a k L ha1 hk hL (∂_{v} ψ)‖ ≤ C * ‖v‖ ^ 2 := by
  obtain ⟨B, hB, hb⟩ := cutoffProfile_sampling_of_global_symbol a (k + 2) ha ha1
    (by linarith) χ hχ hχzero Q hQ hsymbol
  refine ⟨(2 ^ (6 - a) + 1) ^ 2 * B, by positivity, ?_⟩
  intro L hL v ψ
  calc
    _ ≤ ‖physicalSchwartzTorusSamplingCLM a k L ha1 hk hL (∂_{v} (∂_{v} ψ))‖ :=
      translated_schwartzSample_taylor a k L ha1 hk hL ψ v
    _ ≤ (2 ^ (6 - a) + 1) ^ 2 * ‖v‖ ^ 2 *
        ‖physicalSchwartzTorusSamplingCLM a (k + 2) L ha1 (by linarith) hL ψ‖ :=
      schwartzSample_secondDirectional_norm_le a k L ha ha1 hk hL ψ v
    _ ≤ (2 ^ (6 - a) + 1) ^ 2 * ‖v‖ ^ 2 * B :=
      mul_le_mul_of_nonneg_left (hb L hL) (by positivity)
    _ = _ := by ring

end DefocusingNLS

end OAI

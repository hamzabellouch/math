import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffTranslationTaylor
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffDirectionalError

namespace OAI

/-! # Translation expansion with the actual physical profile direction -/

open scoped SchwartzMap LineDeriv ContDiff
namespace DefocusingNLS
local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem cutoffProfile_physical_translation_taylor (a k : ℝ) (ha : 0 < a) (ha1 : a < 1)
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
        physicalSchwartzTorusSamplingCLM a k L ha1 hk hL
          (cutoffProfileSchwartz L (by linarith) χ hχ (cartesianDerivative v Q)
            (cartesianDerivative_contDiff Q hQ v))‖ ≤ C * (‖v‖ ^ 2 + ‖v‖ / L) := by
  obtain ⟨B, hB, hb⟩ := cutoffProfile_translation_taylor a k ha ha1 hk χ hχ hχzero Q hQ hsymbol
  obtain ⟨D, hD, hd⟩ := cutoff_directional_error_bound a k ha ha1 hk χ hχ hχzero Q hQ hsymbol
  refine ⟨B + D, add_nonneg hB hD, ?_⟩
  intro L hL v ψ
  let u := sobolevTranslation (euclideanToTorus ((1 / L) • v))
    (physicalSchwartzTorusSamplingCLM a k L ha1 hk hL ψ) -
      physicalSchwartzTorusSamplingCLM a k L ha1 hk hL ψ
  let d := physicalSchwartzTorusSamplingCLM a k L ha1 hk hL (∂_{v} ψ)
  let f := physicalSchwartzTorusSamplingCLM a k L ha1 hk hL
    (cutoffProfileSchwartz L (by linarith) χ hχ (cartesianDerivative v Q)
      (cartesianDerivative_contDiff Q hQ v))
  change ‖u - f‖ ≤ _
  calc
    _ ≤ ‖u - d‖ + ‖d - f‖ := norm_sub_le_norm_sub_add_norm_sub u d f
    _ ≤ B * ‖v‖ ^ 2 + D / L * ‖v‖ := add_le_add (hb L hL v) (hd L hL v)
    _ ≤ _ := by
      have h1 := mul_nonneg hB (show 0 ≤ ‖v‖ / L by positivity)
      have h2 := mul_nonneg hD (sq_nonneg ‖v‖)
      simp only [div_eq_mul_inv] at *
      nlinarith

end DefocusingNLS

end OAI

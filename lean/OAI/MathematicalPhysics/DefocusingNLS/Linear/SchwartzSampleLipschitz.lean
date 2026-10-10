import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzSampleDerivativeBound
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffSymbolSampling

namespace OAI

/-! # Uniform Lipschitz bound for normalized translations of a cutoff profile -/

open Set
open scoped SchwartzMap LineDeriv ContDiff
namespace DefocusingNLS
local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem translated_schwartzSample_sub_norm_le (a k L : ℝ) (ha1 : a < 1)
    (hk : 8 < k) (hL : 1 ≤ L) (ψ : 𝓢(E, ℂ)) (v : E) :
    ‖sobolevTranslation (euclideanToTorus ((1 / L) • v))
        (physicalSchwartzTorusSamplingCLM a k L ha1 hk hL ψ) -
      physicalSchwartzTorusSamplingCLM a k L ha1 hk hL ψ‖ ≤
        ‖physicalSchwartzTorusSamplingCLM a k L ha1 hk hL (∂_{v} ψ)‖ := by
  let u := fun t : ℝ => sobolevTranslation (euclideanToTorus ((t / L) • v))
    (physicalSchwartzTorusSamplingCLM a k L ha1 hk hL ψ)
  let d := fun t : ℝ => sobolevTranslation (euclideanToTorus ((t / L) • v))
    (physicalSchwartzTorusSamplingCLM a k L ha1 hk hL (∂_{v} ψ))
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t (_ : t ∈ Icc (0 : ℝ) 1) =>
      (hasDerivAt_translated_schwartzSample a k L ha1 hk hL ψ v t).hasDerivWithinAt)
    (fun t (_ : t ∈ Icc (0 : ℝ) 1) => (sobolevTranslation _).norm_map _ |>.le)
    (convex_Icc (0 : ℝ) 1) (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)
    (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)
  have hzero : euclideanToTorus ((0 / L) • v) = 0 := by
    ext j
    simp [euclideanToTorus]
  simpa only [hzero, sobolevTranslation_zero, sub_zero, Real.norm_eq_abs,
    abs_one, mul_one] using h

theorem cutoffProfile_translation_lipschitz (a k : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (hk : 8 < k) (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (hχzero : ∀ y : E, 1 ≤ ‖y‖ → χ y = 0)
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q)
    (hsymbol : ∀ n : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ y : E, y ≠ 0 →
      ‖iteratedFDeriv ℝ n Q y‖ ≤ D * ‖y‖ ^ (-2 * a - (n : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℝ) (hL : 1 ≤ L) (v : E),
      let ψ := cutoffProfileSchwartz L (by linarith) χ hχ Q hQ
      ‖sobolevTranslation (euclideanToTorus ((1 / L) • v))
          (physicalSchwartzTorusSamplingCLM a k L ha1 hk hL ψ) -
        physicalSchwartzTorusSamplingCLM a k L ha1 hk hL ψ‖ ≤ C * ‖v‖ := by
  obtain ⟨B, hB, hb⟩ := cutoffProfile_sampling_of_global_symbol a (k + 1) ha ha1
    (by linarith) χ hχ hχzero Q hQ hsymbol
  refine ⟨(2 ^ (6 - a) + 1) * B, by positivity, ?_⟩
  intro L hL v ψ
  calc
    _ ≤ ‖physicalSchwartzTorusSamplingCLM a k L ha1 hk hL (∂_{v} ψ)‖ :=
      translated_schwartzSample_sub_norm_le a k L ha1 hk hL ψ v
    _ ≤ (2 ^ (6 - a) + 1) * ‖v‖ *
        ‖physicalSchwartzTorusSamplingCLM a (k + 1) L ha1 (by linarith) hL ψ‖ :=
      schwartzSample_directional_norm_le a k L ha ha1 hk hL ψ v
    _ ≤ (2 ^ (6 - a) + 1) * ‖v‖ * B := mul_le_mul_of_nonneg_left (hb L hL) (by positivity)
    _ = _ := by ring

end DefocusingNLS

end OAI

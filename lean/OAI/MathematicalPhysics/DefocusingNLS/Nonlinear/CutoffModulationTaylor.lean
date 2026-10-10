import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffTimeLipschitz
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.ExponentialModulationTaylor

namespace OAI

/-! # Uniform phase, time and translation Taylor estimate for the cutoff profile -/

open scoped SchwartzMap ContDiff
namespace DefocusingNLS
local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "Radius" => {L : ℝ // 1 ≤ L}

theorem cutoffProfile_modulation_taylor (a k : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (hk : 8 < k) (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (hχzero : ∀ y : E, 1 ≤ ‖y‖ → χ y = 0)
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q)
    (hsymbol : ∀ n : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ y : E, y ≠ 0 →
      ‖iteratedFDeriv ℝ n Q y‖ ≤ D * ‖y‖ ^ (-2 * a - (n : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : Radius), 2 ≤ L.1 → ∀ (t : ℝ) (v : E) (z : ℂ),
      |t| ≤ 2 * Real.log 2 → |t| ≤ 1 → ‖z‖ ≤ 1 →
      ‖Complex.exp z • sobolevTranslation (euclideanToTorus ((1 / L.1) • v))
          (fixedCutoffProfile a k ha ha1 hk L χ hχ Q hQ (expandingRadius L.1 t)) -
        fixedCutoffProfile a k ha ha1 hk L χ hχ Q hQ L.1 -
        (z • fixedCutoffProfile a k ha ha1 hk L χ hχ Q hQ L.1 +
          t • fixedCutoffProfile a k ha ha1 hk L χ hχ (cartesianTransport Q)
            (cartesianTransport_contDiff Q hQ) L.1 +
          fixedCutoffProfile a k ha ha1 hk L χ hχ (cartesianDerivative v Q)
            (cartesianDerivative_contDiff Q hQ v) L.1)‖ ≤
        C * (‖z‖ ^ 2 + |t| ^ 2 + ‖v‖ ^ 2 + ‖v‖ / L.1) := by
  obtain ⟨A, hA, htaylor⟩ := cutoffProfile_mixed_taylor a k ha ha1 hk χ hχ hχzero Q hQ hsymbol
  obtain ⟨B, hB, hbase⟩ := cutoffProfile_sampling_of_global_symbol a k ha ha1 hk χ hχ hχzero Q hQ hsymbol
  obtain ⟨D, hD, hfirst⟩ := cutoffProfile_mixed_first_bound a k ha ha1 hk χ hχ hχzero Q hQ hsymbol
  refine ⟨A + B + 2 * D, by positivity, ?_⟩
  intro L hL t v z ht ht1 hz
  let u := sobolevTranslation (euclideanToTorus ((1 / L.1) • v))
    (fixedCutoffProfile a k ha ha1 hk L χ hχ Q hQ (expandingRadius L.1 t))
  let q := fixedCutoffProfile a k ha ha1 hk L χ hχ Q hQ L.1
  let d := t • fixedCutoffProfile a k ha ha1 hk L χ hχ (cartesianTransport Q)
    (cartesianTransport_contDiff Q hQ) L.1 +
      fixedCutoffProfile a k ha ha1 hk L χ hχ (cartesianDerivative v Q)
        (cartesianDerivative_contDiff Q hQ v) L.1
  have hrem : ‖u - q - d‖ ≤ A * (|t| ^ 2 + ‖v‖ ^ 2 + ‖v‖ / L.1) := by
    simpa only [d, sub_add_eq_sub_sub] using htaylor L hL t v ht
  have hq : ‖q‖ ≤ B := by
    simpa only [q, fixedCutoffProfile_self, physicalSchwartzTorusSamplingCLM_apply] using hbase L.1 L.2
  have hu : ‖u - q‖ ≤ D * (|t| + ‖v‖) := hfirst L hL t v ht ht1
  have heq : z • q + t • fixedCutoffProfile a k ha ha1 hk L χ hχ (cartesianTransport Q)
      (cartesianTransport_contDiff Q hQ) L.1 +
      fixedCutoffProfile a k ha ha1 hk L χ hχ (cartesianDerivative v Q)
        (cartesianDerivative_contDiff Q hQ v) L.1 = z • q + d := by
    dsimp only [d]
    abel
  change ‖Complex.exp z • u - q - _‖ ≤ _
  rw [heq]
  calc
    _ ≤ ‖u - q - d‖ + ‖z‖ ^ 2 * ‖q‖ + 2 * ‖z‖ * ‖u - q‖ :=
      exponential_modulation_taylor z hz u q d
    _ ≤ A * (|t| ^ 2 + ‖v‖ ^ 2 + ‖v‖ / L.1) + ‖z‖ ^ 2 * B +
        2 * ‖z‖ * (D * (|t| + ‖v‖)) :=
      add_le_add (add_le_add hrem (mul_le_mul_of_nonneg_left hq (sq_nonneg _)))
        (mul_le_mul_of_nonneg_left hu (by positivity))
    _ ≤ _ := by
      let R := ‖z‖ ^ 2 + |t| ^ 2 + ‖v‖ ^ 2 + ‖v‖ / L.1
      have hvL : 0 ≤ ‖v‖ / L.1 := by positivity
      have hc : ‖z‖ * (|t| + ‖v‖) ≤ R := by
        dsimp only [R]
        nlinarith [sq_nonneg (‖z‖ - |t|), sq_nonneg (‖z‖ - ‖v‖)]
      have h1 : A * (|t| ^ 2 + ‖v‖ ^ 2 + ‖v‖ / L.1) ≤ A * R :=
        mul_le_mul_of_nonneg_left (by dsimp [R]; nlinarith [sq_nonneg ‖z‖]) hA
      have h2 : ‖z‖ ^ 2 * B ≤ B * R := by
        have := mul_le_mul_of_nonneg_left
          (show ‖z‖ ^ 2 ≤ R by dsimp [R]; nlinarith [sq_nonneg |t|, sq_nonneg ‖v‖]) hB
        nlinarith only [this]
      have h3 := mul_le_mul_of_nonneg_left hc (show 0 ≤ 2 * D by positivity)
      dsimp only [R] at h1 h2 h3
      nlinarith only [h1, h2, h3]

end DefocusingNLS

end OAI

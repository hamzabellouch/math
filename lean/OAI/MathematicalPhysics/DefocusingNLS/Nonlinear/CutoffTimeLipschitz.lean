import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffMixedTaylor

namespace OAI

/-! # Uniform first-order bounds for the joint time and translation perturbation -/

open scoped SchwartzMap ContDiff
namespace DefocusingNLS
local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "Radius" => {L : ℝ // 1 ≤ L}

theorem cutoffProfile_time_lipschitz (a k : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (hk : 8 < k) (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (hχzero : ∀ y : E, 1 ≤ ‖y‖ → χ y = 0)
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q)
    (hsymbol : ∀ n : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ y : E, y ≠ 0 →
      ‖iteratedFDeriv ℝ n Q y‖ ≤ D * ‖y‖ ^ (-2 * a - (n : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : Radius), 2 ≤ L.1 → ∀ t : ℝ,
      |t| ≤ 2 * Real.log 2 → |t| ≤ 1 →
      ‖fixedCutoffProfile a k ha ha1 hk L χ hχ Q hQ (expandingRadius L.1 t) -
        fixedCutoffProfile a k ha ha1 hk L χ hχ Q hQ L.1‖ ≤ C * |t| := by
  have hT := cartesianTransport_global_symbol a Q hQ hsymbol
  have hTT := cartesianTransport_global_symbol a (cartesianTransport Q)
    (cartesianTransport_contDiff Q hQ) hT
  obtain ⟨B, hB, hb⟩ := cutoffProfile_sampling_of_global_symbol a k ha ha1 hk χ hχ hχzero
    (cartesianTransport (cartesianTransport Q))
    (cartesianTransport_contDiff _ (cartesianTransport_contDiff Q hQ)) hTT
  obtain ⟨D, hD, hd⟩ := cutoffProfile_sampling_of_global_symbol a k ha ha1 hk χ hχ hχzero
    (cartesianTransport Q) (cartesianTransport_contDiff Q hQ) hT
  let A := (2 ^ a + 2 ^ (k - 6)) * B
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨A + D, add_nonneg hA hD, ?_⟩
  intro L hL t ht ht1
  let u := fixedCutoffProfile a k ha ha1 hk L χ hχ Q hQ (expandingRadius L.1 t)
  let q := fixedCutoffProfile a k ha ha1 hk L χ hχ Q hQ L.1
  let d := fixedCutoffProfile a k ha ha1 hk L χ hχ (cartesianTransport Q)
    (cartesianTransport_contDiff Q hQ) L.1
  have htime : ‖u - q - t • d‖ ≤ A * |t| ^ 2 :=
    fixedCutoffProfile_logRadius_taylor a k ha ha1 hk L hL χ hχ Q hQ B hB
      (fun R => hb R.1 R.2) t ht
  have hdn : ‖d‖ ≤ D := by
    simpa only [d, fixedCutoffProfile_self, physicalSchwartzTorusSamplingCLM_apply] using hd L.1 L.2
  have hsq : |t| ^ 2 ≤ |t| := by nlinarith [abs_nonneg t]
  calc
    _ ≤ ‖u - q - t • d‖ + ‖t • d‖ := by
      simpa only [sub_zero] using norm_sub_le_norm_sub_add_norm_sub (u - q) (t • d) 0
    _ ≤ A * |t| ^ 2 + |t| * D := by
      rw [norm_smul, Real.norm_eq_abs]
      exact add_le_add htime (mul_le_mul_of_nonneg_left hdn (abs_nonneg _))
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hsq hA]

theorem cutoffProfile_mixed_first_bound (a k : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (hk : 8 < k) (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (hχzero : ∀ y : E, 1 ≤ ‖y‖ → χ y = 0)
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q)
    (hsymbol : ∀ n : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ y : E, y ≠ 0 →
      ‖iteratedFDeriv ℝ n Q y‖ ≤ D * ‖y‖ ^ (-2 * a - (n : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : Radius), 2 ≤ L.1 → ∀ (t : ℝ) (v : E),
      |t| ≤ 2 * Real.log 2 → |t| ≤ 1 →
      ‖sobolevTranslation (euclideanToTorus ((1 / L.1) • v))
          (fixedCutoffProfile a k ha ha1 hk L χ hχ Q hQ (expandingRadius L.1 t)) -
        fixedCutoffProfile a k ha ha1 hk L χ hχ Q hQ L.1‖ ≤ C * (|t| + ‖v‖) := by
  obtain ⟨A, hA, ht⟩ := cutoffProfile_time_lipschitz a k ha ha1 hk χ hχ hχzero Q hQ hsymbol
  obtain ⟨B, hB, hs⟩ := cutoffProfile_translation_lipschitz a k ha ha1 hk χ hχ hχzero Q hQ hsymbol
  refine ⟨A + B, add_nonneg hA hB, ?_⟩
  intro L hL t v htlog ht1
  let u := fixedCutoffProfile a k ha ha1 hk L χ hχ Q hQ (expandingRadius L.1 t)
  let q := fixedCutoffProfile a k ha ha1 hk L χ hχ Q hQ L.1
  let S := sobolevTranslation (euclideanToTorus ((1 / L.1) • v))
  have hshift : ‖S q - q‖ ≤ B * ‖v‖ := by
    simpa only [S, q, fixedCutoffProfile_self] using hs L.1 L.2 v
  calc
    _ ≤ ‖S u - S q‖ + ‖S q - q‖ := norm_sub_le_norm_sub_add_norm_sub (S u) (S q) q
    _ = ‖u - q‖ + ‖S q - q‖ := by rw [← map_sub, S.norm_map]
    _ ≤ A * |t| + B * ‖v‖ := add_le_add (ht L hL t htlog ht1) hshift
    _ ≤ _ := by nlinarith [mul_nonneg hA (norm_nonneg v), mul_nonneg hB (abs_nonneg t)]

end DefocusingNLS

end OAI

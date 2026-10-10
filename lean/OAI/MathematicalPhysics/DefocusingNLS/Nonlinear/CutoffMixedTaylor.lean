import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.FixedCutoffProfileIdentity
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.FixedCutoffProfileTaylor
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffPhysicalTranslation
import OAI.MathematicalPhysics.DefocusingNLS.Linear.SchwartzSampleLipschitz
import OAI.MathematicalPhysics.DefocusingNLS.Profile.CartesianTransportSymbol

namespace OAI

/-! # Uniform joint time and translation expansion in the physical symmetry directions -/

open scoped SchwartzMap ContDiff
namespace DefocusingNLS
local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "Radius" => {L : ℝ // 1 ≤ L}

theorem cutoffProfile_mixed_taylor (a k : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (hk : 8 < k) (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (hχzero : ∀ y : E, 1 ≤ ‖y‖ → χ y = 0)
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q)
    (hsymbol : ∀ n : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ y : E, y ≠ 0 →
      ‖iteratedFDeriv ℝ n Q y‖ ≤ D * ‖y‖ ^ (-2 * a - (n : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : Radius), 2 ≤ L.1 → ∀ (t : ℝ) (v : E),
      |t| ≤ 2 * Real.log 2 →
      ‖sobolevTranslation (euclideanToTorus ((1 / L.1) • v))
          (fixedCutoffProfile a k ha ha1 hk L χ hχ Q hQ (expandingRadius L.1 t)) -
        fixedCutoffProfile a k ha ha1 hk L χ hχ Q hQ L.1 -
        t • fixedCutoffProfile a k ha ha1 hk L χ hχ (cartesianTransport Q)
          (cartesianTransport_contDiff Q hQ) L.1 -
        fixedCutoffProfile a k ha ha1 hk L χ hχ (cartesianDerivative v Q)
          (cartesianDerivative_contDiff Q hQ v) L.1‖ ≤
        C * (|t| ^ 2 + ‖v‖ ^ 2 + ‖v‖ / L.1) := by
  have hT := cartesianTransport_global_symbol a Q hQ hsymbol
  have hTT := cartesianTransport_global_symbol a (cartesianTransport Q)
    (cartesianTransport_contDiff Q hQ) hT
  obtain ⟨B, hB, hb⟩ := cutoffProfile_sampling_of_global_symbol a k ha ha1 hk χ hχ hχzero
    (cartesianTransport (cartesianTransport Q))
    (cartesianTransport_contDiff _ (cartesianTransport_contDiff Q hQ)) hTT
  obtain ⟨A, hA, hspace⟩ := cutoffProfile_physical_translation_taylor a k ha ha1 hk χ hχ
    hχzero Q hQ hsymbol
  obtain ⟨D, hD, hshift⟩ := cutoffProfile_translation_lipschitz a k ha ha1 hk χ hχ hχzero
    (cartesianTransport Q) (cartesianTransport_contDiff Q hQ) hT
  let B' := (2 ^ a + 2 ^ (k - 6)) * B
  have hB' : 0 ≤ B' := by dsimp [B']; positivity
  refine ⟨B' + A + D, by positivity, ?_⟩
  intro L hL t v ht
  let u := fixedCutoffProfile a k ha ha1 hk L χ hχ Q hQ (expandingRadius L.1 t)
  let q := fixedCutoffProfile a k ha ha1 hk L χ hχ Q hQ L.1
  let d := fixedCutoffProfile a k ha ha1 hk L χ hχ (cartesianTransport Q)
    (cartesianTransport_contDiff Q hQ) L.1
  let f := fixedCutoffProfile a k ha ha1 hk L χ hχ (cartesianDerivative v Q)
    (cartesianDerivative_contDiff Q hQ v) L.1
  let S := (sobolevTranslation (euclideanToTorus ((1 / L.1) • v))).toContinuousLinearMap
  have htime : ‖u - q - t • d‖ ≤ B' * |t| ^ 2 :=
    fixedCutoffProfile_logRadius_taylor a k ha ha1 hk L hL χ hχ Q hQ B hB
      (fun R => hb R.1 R.2) t ht
  have htrans : ‖S q - q - f‖ ≤ A * (‖v‖ ^ 2 + ‖v‖ / L.1) := by
    simpa only [S, LinearIsometry.coe_toContinuousLinearMap, q, f, fixedCutoffProfile_self] using hspace L.1 L.2 v
  have htd : ‖S d - d‖ ≤ D * ‖v‖ := by
    simpa only [S, LinearIsometry.coe_toContinuousLinearMap, d, fixedCutoffProfile_self] using hshift L.1 L.2 v
  have he : S u - q - t • d - f =
      S (u - q - t • d) + (S q - q - f) + t • (S d - d) := by
    simp only [map_sub, ContinuousLinearMap.map_smul_of_tower, smul_sub]
    abel
  change ‖S u - q - t • d - f‖ ≤ _
  rw [he]
  calc
    _ ≤ ‖S (u - q - t • d)‖ + ‖S q - q - f‖ + ‖t • (S d - d)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = ‖u - q - t • d‖ + ‖S q - q - f‖ + |t| * ‖S d - d‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      simp only [S, LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.norm_map]
    _ ≤ B' * |t| ^ 2 + A * (‖v‖ ^ 2 + ‖v‖ / L.1) + |t| * (D * ‖v‖) :=
      add_le_add (add_le_add htime htrans) (mul_le_mul_of_nonneg_left htd (abs_nonneg _))
    _ ≤ _ := by
      have hm := mul_nonneg hD (sq_nonneg (|t| - ‖v‖))
      have hp : 0 ≤ ‖v‖ / L.1 := by positivity
      have h1 := mul_nonneg hB' (add_nonneg (sq_nonneg ‖v‖) hp)
      have h2 := mul_nonneg hA (sq_nonneg |t|)
      have h3 := mul_nonneg hD hp
      nlinarith

end DefocusingNLS

end OAI

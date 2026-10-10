import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.PhysicalFrameSampling
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffModulationTaylor

namespace OAI

/-! # The full modulation error is quadratic up to the inverse-radius cutoff term -/

open scoped SchwartzMap ContDiff
namespace DefocusingNLS
local notation "E" => EuclideanSpace ℝ (Fin 12)
local notation "Radius" => {L : ℝ // 1 ≤ L}
local notation "Params" => ProfileSymmetryParameters

noncomputable def modulatedCutoffProfile (a k : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (hk : 8 < k) (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (L : Radius) (p : Params) : FourierL2 :=
  Complex.exp ((a * p.2.2 : ℝ) - (p.1 : ℂ) * Complex.I) •
    sobolevTranslation (euclideanToTorus ((1 / L.1) • p.2.1))
      (fixedCutoffProfile a k ha ha1 hk L χ hχ Q hQ (expandingRadius L.1 p.2.2)) -
    fixedCutoffProfile a k ha ha1 hk L χ hχ Q hQ L.1

theorem modulatedCutoffProfile_taylor (a b k : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (hk : 8 < k) (χ : 𝓢(E, ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (hχzero : ∀ y : E, 1 ≤ ‖y‖ → χ y = 0)
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q)
    (hsymbol : ∀ n : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ y : E, y ≠ 0 →
      ‖iteratedFDeriv ℝ n Q y‖ ≤ D * ‖y‖ ^ (-2 * a - (n : ℝ)))
    (F : Params →L[ℝ] HomogeneousY a k)
    (hphys : ∀ p y, homogeneousPhysicalCLM a k ha ha1 hk (F p) y =
      (p.1 : ℂ) * (Complex.I * Q y) +
      (p.2.2 : ℂ) * (((a : ℂ) - Complex.I * (b : ℂ)) * Q y + cartesianTransport Q y) +
      cartesianDerivative p.2.1 Q y)
    (hF : ∀ p, ContDiff ℝ ∞ (fun y => homogeneousPhysicalCLM a k ha ha1 hk (F p) y)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : Radius), 2 ≤ L.1 → ∀ p : Params,
      ‖p‖ ≤ 1 / 2 → ‖p‖ ≤ 2 * Real.log 2 →
      ‖modulatedCutoffProfile a k ha ha1 hk χ hχ Q hQ L p -
        sampledPhysicalFrame a k ha ha1 hk χ hχ F hF L (physicalModulationParameterEquiv b p)‖ ≤
        C * (‖p‖ ^ 2 + ‖p‖ / L.1) := by
  obtain ⟨C, hC, hc⟩ := cutoffProfile_modulation_taylor a k ha ha1 hk χ hχ hχzero Q hQ hsymbol
  refine ⟨6 * C, by positivity, ?_⟩
  intro L hL p hp hplog
  have hθ : |p.1| ≤ ‖p‖ := by simpa only [Real.norm_eq_abs] using norm_fst_le p
  have hv : ‖p.2.1‖ ≤ ‖p‖ := (norm_fst_le p.2).trans (norm_snd_le p)
  have ht : |p.2.2| ≤ ‖p‖ := by
    simpa only [Real.norm_eq_abs] using (norm_snd_le p.2).trans (norm_snd_le p)
  let z : ℂ := (a * p.2.2 : ℝ) - (p.1 : ℂ) * Complex.I
  have hz : ‖z‖ ≤ 2 * ‖p‖ := by
    have hb := norm_sub_le ((a * p.2.2 : ℝ) : ℂ) ((p.1 : ℂ) * Complex.I)
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I,
      mul_one, abs_of_pos ha] at hb
    change ‖z‖ ≤ a * |p.2.2| + |p.1| at hb
    nlinarith [mul_nonneg (show 0 ≤ 1 - a by linarith) (abs_nonneg p.2.2)]
  have h := hc L hL p.2.2 p.2.1 z (ht.trans hplog) (by linarith) (by linarith)
  rw [sampledPhysicalFrame_modulation_tangent a b k ha ha1 hk Q hQ F hphys χ hχ hF L p]
  change ‖Complex.exp z • _ - _ - _‖ ≤ _
  apply h.trans
  have hz2 : ‖z‖ ^ 2 ≤ 4 * ‖p‖ ^ 2 := by nlinarith [norm_nonneg z, norm_nonneg p]
  have ht2 : |p.2.2| ^ 2 ≤ ‖p‖ ^ 2 := by nlinarith [abs_nonneg p.2.2, norm_nonneg p]
  have hv2 : ‖p.2.1‖ ^ 2 ≤ ‖p‖ ^ 2 := by nlinarith [norm_nonneg p.2.1, norm_nonneg p]
  have hdiv : ‖p.2.1‖ / L.1 ≤ ‖p‖ / L.1 := div_le_div_of_nonneg_right hv (by linarith [L.2])
  have hs : ‖z‖ ^ 2 + |p.2.2| ^ 2 + ‖p.2.1‖ ^ 2 + ‖p.2.1‖ / L.1 ≤
      6 * (‖p‖ ^ 2 + ‖p‖ / L.1) := by
    nlinarith [show 0 ≤ ‖p‖ / L.1 by positivity]
  exact (mul_le_mul_of_nonneg_left hs hC).trans_eq (by ring)

end DefocusingNLS

end OAI

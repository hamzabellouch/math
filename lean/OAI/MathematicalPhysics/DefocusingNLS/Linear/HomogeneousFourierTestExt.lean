import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousFourierPairing
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

namespace OAI

/-! # Schwartz Fourier tests separate the homogeneous space -/

open MeasureTheory
open scoped SchwartzMap ContDiff

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem homogeneousFourierPairing_ext (a k : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (u v : HomogeneousY a k)
    (h : ∀ φ : 𝓢(E, ℂ), homogeneousFourierPairing a k ha ha1 hk φ u =
      homogeneousFourierPairing a k ha ha1 hk φ v) : u = v := by
  let w := u - v
  have hw : ∀ φ : 𝓢(E, ℂ), homogeneousFourierPairing a k ha ha1 hk φ w = 0 := by
    intro φ
    simp only [w, map_sub, h φ, sub_self]
  have hi := (integrable_and_integral_norm_of_memLp_homogeneous a k ha ha1 hk (Lp.memLp w)).1
  have hz : (w : E → ℂ) =ᵐ[volume] 0 := by
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hi.locallyIntegrable
    intro g hg hgc
    have hc : HasCompactSupport (Complex.ofRealCLM ∘ g) := hgc.comp_left rfl
    have hs : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
    let ψ : 𝓢(E, ℂ) := hc.toSchwartzMap hs
    change (∫ ξ : E, (g ξ : ℂ) * w ξ) = 0
    calc
      _ = ∫ ξ : E, w ξ * ψ ξ := by
        apply integral_congr_ae
        exact ae_of_all _ fun ξ => mul_comm _ _
      _ = 0 := hw ψ
  have hw0 : w = 0 := Lp.eq_zero_iff_ae_eq_zero.mpr
    (hz.filter_mono (withDensity_absolutelyContinuous volume _).ae_le)
  exact sub_eq_zero.mp hw0

end DefocusingNLS

end OAI

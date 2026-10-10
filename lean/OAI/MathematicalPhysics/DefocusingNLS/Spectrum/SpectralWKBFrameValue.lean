import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFrameAmplitude

namespace OAI

/-! Exact first-coordinate normalization of the constructed WKB frame and
the positive outgoing flux at its reference point. -/

open Set
namespace DefocusingNLS

theorem spectralWKBFrame_value_norm (R E : ℝ) (hRE : R ≤ E) (chi : ℂ)
    (p v : ℝ → ℂ) (hp : ContinuousOn p (Icc R E)) (hv : ContinuousOn v (Icc R E))
    (hp0 : ∀ t ∈ Icc R E, p t ≠ 0)
    (hpD : ∀ t ∈ Ioo R E, HasDerivAt p (v t) t)
    (k r : ℝ) (hk : 0 < k) (hkp : k^2 = ‖p r‖) (hr : r ∈ Icc R E) :
    k*‖(spectralWKBFrame R chi p v r).1‖ = Real.exp (spectralWKBPhase R chi p r).re := by
  exact spectralWKBState_value_norm chi (p r) (v r) _ _ k hk hkp
    (spectralWKBAmplitude_normalization R E hRE _ p v hp hv hp0 hpD
      (spectralWKBInitialAmplitude_normalization (p R) (hp0 R ⟨le_rfl,hRE⟩)) r hr)

theorem spectralWKBFrame_initial (R : ℝ) (chi : ℂ) (p v : ℝ → ℂ) :
    spectralWKBFrame R chi p v R =
      spectralWKBState chi (p R) (v R) (spectralWKBInitialAmplitude (p R)) 0 := by
  simp only [spectralWKBFrame,spectralWKBAmplitude_initial,spectralWKBPhase,
    intervalIntegral.integral_same,mul_zero]

theorem spectralWKB_initial_flux_lower (h F gamma k : ℝ) (v : ℂ)
    (hh : h^2 = 1) (hF : 0 < F) (hk : 0 < k)
    (hkp : k^2 = ‖Complex.sqrt ((F : ℂ)+Complex.I*(gamma : ℂ))‖)
    (hv : ‖v‖ ≤ ‖Complex.sqrt ((F : ℂ)+Complex.I*(gamma : ℂ))‖^2) :
    (1/6 : ℝ) ≤ h*spectralScalarFlux (spectralWKBState ((h : ℂ)*Complex.I)
      (Complex.sqrt ((F : ℂ)+Complex.I*(gamma : ℂ))) v
      (spectralWKBInitialAmplitude (Complex.sqrt ((F : ℂ)+Complex.I*(gamma : ℂ)))) 0) := by
  let p := Complex.sqrt ((F : ℂ)+Complex.I*(gamma : ℂ))
  have hp : p ≠ 0 := norm_pos_iff.mp (by rw [← hkp]; positivity)
  have hvn := spectralWKBState_value_norm ((h : ℂ)*Complex.I) p v
    (spectralWKBInitialAmplitude p) 0 k hk hkp (spectralWKBInitialAmplitude_normalization p hp)
  simp only [Complex.zero_re,Real.exp_zero] at hvn
  have hf := spectralWKBState_flux_lower h F gamma k v (spectralWKBInitialAmplitude p) 0 hh hF hkp hv
  change (k*‖(spectralWKBState ((h : ℂ)*Complex.I) p v (spectralWKBInitialAmplitude p) 0).1‖)^2/6 ≤ _ at hf
  rw [hvn,one_pow] at hf
  exact hf

end DefocusingNLS

end OAI

import OAI.MathematicalPhysics.DefocusingNLS.Linear.HomogeneousSpectralLocalizationGauge

namespace OAI

/-! Exact residual of the scalar WKB logarithmic derivative.  The same
identity covers both exponential and oscillatory outer intervals. -/

namespace DefocusingNLS

noncomputable def homogeneousSpectralWKBLog (chi p v : ℂ) : ℂ :=
  chi * p - v / (2 * p)

noncomputable def homogeneousSpectralWKBResidual (p v w : ℂ) : ℂ :=
  (3 / 4 : ℂ) * (v / p)^2 - w / (2 * p)

theorem homogeneousSpectralWKBLog_identity (chi p v w : ℂ) (hp : p ≠ 0) :
    (chi * v - w / (2 * p) + v^2 / (2 * p^2)) +
        homogeneousSpectralWKBLog chi p v ^ 2 =
      chi^2 * p^2 + homogeneousSpectralWKBResidual p v w := by
  dsimp only [homogeneousSpectralWKBLog, homogeneousSpectralWKBResidual]
  field_simp [hp]
  ring

theorem homogeneousSpectralWKBLog_hasDerivAt
    (chi : ℂ) (p v : ℝ → ℂ) (w : ℂ) (r : ℝ)
    (hp0 : p r ≠ 0) (hp : HasDerivAt p (v r) r) (hv : HasDerivAt v w r) :
    HasDerivAt (fun t => homogeneousSpectralWKBLog chi (p t) (v t))
      (chi * v r - w / (2 * p r) + (v r)^2 / (2 * (p r)^2)) r := by
  have hd := (hp.const_mul chi).sub ((hv.div hp hp0).div_const 2)
  convert hd using 1
  · funext t
    change chi*p t-v t/(2*p t)=chi*p t-(v t/p t)/2
    ring
  · field_simp [hp0]
    ring

theorem homogeneousSpectralWKB_acceleration
    (chi : ℂ) (p v U : ℝ → ℂ) (w : ℂ) (r : ℝ)
    (hp0 : p r ≠ 0) (hp : HasDerivAt p (v r) r) (hv : HasDerivAt v w r)
    (hU : HasDerivAt U (homogeneousSpectralWKBLog chi (p r) (v r) * U r) r) :
    HasDerivAt (fun t => homogeneousSpectralWKBLog chi (p t) (v t) * U t)
      ((chi^2 * (p r)^2 + homogeneousSpectralWKBResidual (p r) (v r) w) * U r) r := by
  have hd := (homogeneousSpectralWKBLog_hasDerivAt chi p v w r hp0 hp hv).mul hU
  apply hd.congr_deriv
  have he := homogeneousSpectralWKBLog_identity chi (p r) (v r) w hp0
  linear_combination he * U r

theorem homogeneousSpectralWKBResidual_norm (p v w : ℂ) :
    ‖homogeneousSpectralWKBResidual p v w‖ ≤
      (3 / 4 : ℝ) * (‖v‖ / ‖p‖)^2 + ‖w‖ / (2 * ‖p‖) := by
  have hb := norm_sub_le ((3 / 4 : ℂ) * (v / p)^2) (w / (2 * p))
  simpa only [homogeneousSpectralWKBResidual, norm_mul, norm_div, norm_pow,
    Complex.norm_ofNat] using hb

end DefocusingNLS

end OAI

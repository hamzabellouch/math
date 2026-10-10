import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningMomentumLimit
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningSlopeLimit
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralGrowingLimit

namespace OAI

/-! The actual forbidden-side WKB projection converges to the Airy growing
projection, including its amplitude and logarithmic derivative correction. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralTurning_growing_projection_margin
    (h : ℝ) (b eta omega gamma r₀ d : ℕ → ℝ) (T G : ℝ) (hT : 0 < T)
    (hr₀ : Tendsto r₀ atTop atTop)
    (hdata : ∀ᶠ n in atTop, 0 < r₀ n ∧ 0 ≤ d n ∧ 0 ≤ eta n ∧ |gamma n| ≤ G ∧
      homogeneousSpectralLocalizationFrequency h (b n) (eta n) (omega n) (r₀ n) = 0 ∧
      (r₀ n/8+2*(eta n+99/4)/(r₀ n)^3)*(d n)^3 = 1)
    (u : ℂ × ℂ) (un : ℕ → ℂ × ℂ) (hu : spectralScalarFlux u ≠ 0)
    (hun : Tendsto un atTop (𝓝 u))
    (hmargin : (1/4 : ℝ)*spectralShellNorm (Real.sqrt (Real.sqrt T)) u ≤
      ‖spectralGrowingCoefficient (Real.sqrt (Real.sqrt T)) (1/(4*T)) u‖) :
    let P := fun n => (d n : ℂ)*spectralLiouvilleMomentum (-1) h (b n) (eta n)
      (omega n) (gamma n) (r₀ n-d n*T)
    let A := fun n => ((d n)^3*spectralLiouvilleSlope (eta n) (r₀ n-d n*T) : ℝ)
    ∀ᶠ n in atTop, (1/8 : ℝ)*spectralShellNorm (Real.sqrt ‖P n‖) (un n) ≤
      ‖((un n).2+(P n+(A n : ℂ)/(4*(P n)^2))*(un n).1)/(2*Complex.sqrt (P n))‖ := by
  dsimp only
  let P := fun n => (d n : ℂ)*spectralLiouvilleMomentum (-1) h (b n) (eta n)
    (omega n) (gamma n) (r₀ n-d n*T)
  let A := fun n => ((d n)^3*spectralLiouvilleSlope (eta n) (r₀ n-d n*T) : ℝ)
  have hP : Tendsto P atTop (𝓝 (Real.sqrt T : ℂ)) :=
    spectralTurning_negative_momentum_tendsto h b eta omega gamma r₀ d T G hT hr₀ hdata
  have hA : Tendsto A atTop (𝓝 1) := by
    simpa only [A,mul_neg,sub_eq_add_neg,mul_comm] using
      spectralTurning_scaled_slope_tendsto eta r₀ d (-T) hr₀
        (hdata.mono (fun n hn => ⟨hn.1,hn.2.1,hn.2.2.1,hn.2.2.2.2.2⟩))
  have hAC := (Complex.continuous_ofReal.tendsto 1).comp hA
  have hroot : Tendsto (fun n => Complex.sqrt (P n)) atTop
      (𝓝 (Real.sqrt (Real.sqrt T) : ℂ)) := by
    have he : Complex.sqrt (Real.sqrt T : ℂ) = (Real.sqrt (Real.sqrt T) : ℂ) :=
      Complex.sqrt_of_nonneg (by exact_mod_cast Real.sqrt_nonneg T)
    simpa only [he,Function.comp_def] using
      (Complex.continuousAt_sqrt (Or.inl (by simp))).tendsto.comp hP
  have hk : Tendsto (fun n => Real.sqrt ‖P n‖) atTop (𝓝 (Real.sqrt (Real.sqrt T))) := by
    simpa only [Function.comp_def,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg T)] using
      (Real.continuous_sqrt.tendsto ‖(Real.sqrt T : ℂ)‖).comp hP.norm
  have hsT : (Real.sqrt T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hT).ne'
  have hsquare : (Real.sqrt T : ℂ)^2 = (T : ℂ) := by exact_mod_cast Real.sq_sqrt hT.le
  have hB : Tendsto (fun n => P n+(A n : ℂ)/(4*(P n)^2)) atTop
      (𝓝 (((Real.sqrt (Real.sqrt T))^2+1/(4*T) : ℝ) : ℂ)) := by
    have hlim := hP.add (hAC.div ((hP.pow 2).const_mul 4) (mul_ne_zero (by norm_num) (pow_ne_zero _ hsT)))
    simpa only [Function.comp_def,Pi.div_apply,hsquare,Real.sq_sqrt (Real.sqrt_nonneg T),
      Complex.ofReal_add,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_mul,Complex.ofReal_ofNat] using hlim
  exact spectralGrowingCoefficient_eventual_margin (Real.sqrt (Real.sqrt T)) (1/(4*T))
    (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hT)) u hu hmargin
    (fun n => Real.sqrt ‖P n‖) (fun n => Complex.sqrt (P n))
    (fun n => P n+(A n : ℂ)/(4*(P n)^2)) un hk hroot hB hun

end DefocusingNLS

end OAI

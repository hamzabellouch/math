import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningAiryProjection
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralTurningProjectionIdentity

namespace OAI

/-! The limiting Airy growing mode is exactly the physical outgoing WKB
coefficient at the forbidden edge of the turning interval. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralTurning_physical_growing_margin
    (h : ℝ) (b eta omega gamma r₀ d : ℕ → ℝ) (a G : ℝ) (ha : a ≤ 1)
    (hr₀ : Tendsto r₀ atTop atTop)
    (hdata : ∀ᶠ n in atTop, 0 < r₀ n ∧ 0 ≤ d n ∧ 0 ≤ eta n ∧ |gamma n| ≤ G ∧
      homogeneousSpectralLocalizationFrequency h (b n) (eta n) (omega n) (r₀ n) = 0 ∧
      (r₀ n/8+2*(eta n+99/4)/(r₀ n)^3)*(d n)^3 = 1)
    (q : ℕ → ℝ → ℂ × ℂ) (p : ℝ → ℂ × ℂ) (hp : Continuous p)
    (hpD : ∀ t, a ≤ t → HasDerivAt p (spectralScalarField (-(t : ℂ)) (p t)) t)
    (hpJ : spectralScalarFlux (p 1) ≠ 0)
    (hlim : ∀ c : ℝ, TendstoUniformlyOn
      (fun n => spectralTurningAiryState (r₀ n) (d n) (Real.sqrt (d n)) (q n)) p atTop (Icc a c)) :
    ∀ᶠ T : ℝ in atTop, ∀ᶠ n in atTop,
      let c := r₀ n-d n*T
      let P := spectralLiouvilleMomentum (-1) h (b n) (eta n) (omega n) (gamma n) c
      let D := ((Complex.sqrt P)⁻¹,
        (P+(spectralLiouvilleSlope (eta n) c : ℂ)/(4*P^2))*(Complex.sqrt P)⁻¹)
      (1/8 : ℝ)*spectralShellNorm (Real.sqrt ‖P‖) (q n c) ≤
        ‖spectralScalarWronskian D (q n c)/(-2)‖ := by
  have hmargin := spectralTurning_eventual_growing_projection h b eta omega gamma r₀ d a G
    ha hr₀ hdata q p hp hpD hpJ hlim
  filter_upwards [hmargin,eventually_gt_atTop (0 : ℝ)] with T hTm hT
  have hP := spectralTurning_negative_momentum_tendsto h b eta omega gamma r₀ d T G hT hr₀ hdata
  have hre := ((Complex.continuous_re.tendsto (Real.sqrt T : ℂ)).comp hP).eventually
    (lt_mem_nhds (Real.sqrt_pos.mpr hT))
  filter_upwards [hTm,hdata,hre] with n hn hdn hren
  let P := spectralLiouvilleMomentum (-1) h (b n) (eta n) (omega n) (gamma n) (r₀ n-d n*T)
  let u := q n (r₀ n-d n*T)
  have hd : 0 < d n := by
    apply lt_of_le_of_ne hdn.2.1
    intro he
    have hs := hdn.2.2.2.2.2
    rw [← he] at hs
    norm_num at hs
  have hPre : 0 < P.re := by
    change 0 < ((d n : ℂ)*P).re at hren
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hren
    nlinarith
  have hPn : P ≠ 0 := by intro he; rw [he] at hPre; norm_num at hPre
  have hn' : (1/8 : ℝ)*spectralShellNorm (Real.sqrt ‖(d n : ℂ)*P‖)
      (u.1/(Real.sqrt (d n) : ℂ),-(Real.sqrt (d n) : ℂ)*u.2) ≤
      ‖((-(Real.sqrt (d n) : ℂ)*u.2)+((d n : ℂ)*P+
        (((d n)^3*spectralLiouvilleSlope (eta n) (r₀ n-d n*T) : ℝ) : ℂ)/(4*((d n : ℂ)*P)^2))*
          (u.1/(Real.sqrt (d n) : ℂ)))/(2*Complex.sqrt ((d n : ℂ)*P))‖ := by
    simpa only [spectralTurningAiryState,spectralScalarReflect,spectralTurningState,
      zero_add,zero_sub,mul_neg,neg_mul,sub_eq_add_neg,P,u] using hn
  rw [spectralTurning_projection_norm_scale (d n) P u hd hPn,
    spectralTurning_projection_identity (d n) (spectralLiouvilleSlope (eta n) (r₀ n-d n*T)) P u hd hPre] at hn'
  exact hn'

end DefocusingNLS

end OAI

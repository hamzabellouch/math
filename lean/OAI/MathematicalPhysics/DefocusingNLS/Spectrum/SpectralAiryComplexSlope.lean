import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralAirySlopeLimit
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarRatio
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! The full complex logarithmic slope has the growing Airy limit.
Nonzero conserved flux rules out zeros and the decaying alternative. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralAiry_complex_slope_tendsto
    (q : ℝ → ℂ × ℂ) (T : ℝ) (hT : 1≤T)
    (hq : ContinuousOn q (Ici T))
    (hD : ∀ t, T≤t → HasDerivAt q (spectralScalarField (-(t : ℂ)) (q t)) t)
    (hJ : spectralScalarFlux (q T)≠0) :
    Tendsto (fun t => (q t).2/((Real.sqrt t : ℂ)*(q t).1)) atTop (𝓝 1) := by
  obtain ⟨S,hTS,hm,hbound⟩ := spectralAiry_eventual_mass_bound q T hT hq hD hJ
  let J := spectralScalarFlux (q T)
  let m := spectralScalarMass (q S)
  let eta := fun t => spectralScalarFlux (q t)/(Real.sqrt t*spectralScalarMass (q t))
  have hflux (t : ℝ) (ht : S≤t) : spectralScalarFlux (q t)=J :=
    spectralScalarFlux_const T t q (fun x => -x) (hq.mono (fun _ hx => hx.1))
      (fun x hx => by simpa only [Complex.ofReal_neg] using hD x hx.1.le) t ⟨hTS.trans ht,le_rfl⟩
  have hinv : Tendsto (fun t : ℝ => (Real.sqrt t)⁻¹) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.sqrt_inv,Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp
        (tendsto_inv_atTop_zero : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0))
  have hrate : Tendsto (fun t : ℝ => (|J|/m)*(Real.sqrt t)⁻¹) atTop (𝓝 0) := by
    simpa only [mul_zero] using hinv.const_mul (|J|/m)
  have heta : Tendsto eta atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hrate
    filter_upwards [eventually_ge_atTop S] with t ht
    have htp : 0<t := lt_of_lt_of_le (by linarith [hT,hTS] : 0<S) ht
    have hs : 0<Real.sqrt t := Real.sqrt_pos.mpr htp
    have hmass : 0<spectralScalarMass (q t) := hm.trans_le (hbound t ht).2
    change ‖spectralScalarFlux (q t)/(Real.sqrt t*spectralScalarMass (q t))‖≤_
    rw [Real.norm_eq_abs,abs_div,abs_of_pos (mul_pos hs hmass),hflux t ht]
    calc
      _ ≤ |J|/(Real.sqrt t*m) :=
        div_le_div_of_nonneg_left (abs_nonneg _) (mul_pos hs hm)
          (mul_le_mul_of_nonneg_left (hbound t ht).2 hs.le)
      _ = _ := by ring
  have hz := spectralAirySlope_tendsto_one q T hT hq hD hJ
  have hzc : Tendsto (fun t => (spectralAirySlope q t : ℂ)) atTop (𝓝 1) := by
    exact (Complex.continuous_ofReal.tendsto 1).comp hz
  have hec : Tendsto (fun t => (eta t : ℂ)) atTop (𝓝 0) := by
    exact (Complex.continuous_ofReal.tendsto 0).comp heta
  have hsum : Tendsto (fun t => (spectralAirySlope q t : ℂ)+Complex.I*(eta t : ℂ)) atTop (𝓝 1) := by
    simpa only [mul_zero,add_zero] using hzc.add (hec.const_mul Complex.I)
  apply hsum.congr'
  filter_upwards [eventually_ge_atTop S] with t ht
  have htp : 0<t := lt_of_lt_of_le (by linarith [hT,hTS] : 0<S) ht
  have hqt : (q t).1≠0 := spectralScalarFlux_ne_zero_value (q t) (by rw [hflux t ht]; exact hJ)
  exact (spectralScalarRatio_components (q t) (Real.sqrt t) (Real.sqrt_pos.mpr htp).ne' hqt).symm

end DefocusingNLS

end OAI

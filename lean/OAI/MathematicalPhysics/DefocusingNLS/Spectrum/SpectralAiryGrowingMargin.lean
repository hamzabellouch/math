import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralAiryComplexSlope
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralGrowingProjection

namespace OAI

/-! The growing coefficient occupies a fixed fraction of the normalized Airy
Cauchy data at every sufficiently late observation point. -/

open Set Filter Topology
namespace DefocusingNLS

theorem spectralAiry_eventual_growing_margin
    (q : ℝ → ℂ × ℂ) (T : ℝ) (hT : 1≤T)
    (hq : ContinuousOn q (Ici T))
    (hD : ∀ t, T≤t → HasDerivAt q (spectralScalarField (-(t : ℂ)) (q t)) t)
    (hJ : spectralScalarFlux (q T)≠0) :
    ∀ᶠ t : ℝ in atTop,
      (1/4 : ℝ)*spectralShellNorm (Real.sqrt (Real.sqrt t)) (q t)≤
        ‖spectralGrowingCoefficient (Real.sqrt (Real.sqrt t)) (1/(4*t)) (q t)‖ := by
  have hl := spectralAiry_complex_slope_tendsto q T hT hq hD hJ
  have hn := tendsto_iff_norm_sub_tendsto_zero.mp hl
  filter_upwards [eventually_ge_atTop T,
    hn.eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1/2))] with t ht hnear
  have ht0 : 0<t := by linarith
  have hs : 0<Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hk : 0<Real.sqrt (Real.sqrt t) := Real.sqrt_pos.mpr hs
  have hJt : spectralScalarFlux (q t)≠0 := by
    rw [spectralScalarFlux_const T t q (fun x => -x) (hq.mono (fun _ hx => hx.1))
      (fun x hx => by simpa only [Complex.ofReal_neg] using hD x hx.1.le) t ⟨ht,le_rfl⟩]
    exact hJ
  have hqt := spectralScalarFlux_ne_zero_value (q t) hJt
  have hsC : (Real.sqrt t : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hs.ne'
  have he : (q t).2-(Real.sqrt t : ℂ)*(q t).1=
      ((q t).2/((Real.sqrt t : ℂ)*(q t).1)-1)*((Real.sqrt t : ℂ)*(q t).1) := by
    field_simp
  have hb : ‖(q t).2-(Real.sqrt t : ℂ)*(q t).1‖≤(Real.sqrt t/2)*‖(q t).1‖ := by
    rw [he,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hs]
    calc
      _ ≤ (1/2 : ℝ)*(Real.sqrt t*‖(q t).1‖) :=
        mul_le_mul_of_nonneg_right hnear.le (mul_nonneg hs.le (norm_nonneg _))
      _ = _ := by ring
  apply spectralGrowingCoefficient_margin _ _ hk (by positivity) (q t)
  simpa only [Real.sq_sqrt hs.le] using hb

end DefocusingNLS

end OAI

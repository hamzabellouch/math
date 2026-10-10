import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarInitialBound

namespace OAI

/-! A relative growing-coefficient margin follows from a slope near the
positive real branch. The bound is independent of the observation point. -/

namespace DefocusingNLS

noncomputable def spectralGrowingCoefficient (k delta : ℝ) (u : ℂ × ℂ) : ℂ :=
  (u.2+((k^2+delta : ℝ) : ℂ)*u.1)/(2*(k : ℂ))

theorem spectralGrowingCoefficient_wronskian (k delta : ℝ) (u : ℂ × ℂ) :
    spectralGrowingCoefficient k delta u=
      spectralScalarWronskian u ((k : ℂ)⁻¹, -((k^2+delta : ℝ) : ℂ)*(k : ℂ)⁻¹)/(-2) := by
  dsimp only [spectralGrowingCoefficient,spectralScalarWronskian]
  push_cast
  ring

theorem spectralGrowingCoefficient_margin (k delta : ℝ) (hk : 0<k) (hdelta : 0≤delta)
    (u : ℂ × ℂ)
    (hnear : ‖u.2-((k^2 : ℝ) : ℂ)*u.1‖≤(k^2/2)*‖u.1‖) :
    (1/4 : ℝ)*spectralShellNorm k u≤‖spectralGrowingCoefficient k delta u‖ := by
  let e := u.2-((k^2 : ℝ) : ℂ)*u.1
  let v := u.2+((k^2+delta : ℝ) : ℂ)*u.1
  have hlow : (2*k^2+delta)*‖u.1‖≤‖v‖+‖e‖ := by
    have he : ((2*k^2+delta : ℝ) : ℂ)*u.1=v-e := by
      dsimp only [v,e]
      push_cast
      ring
    have hh := norm_sub_le v e
    rw [← he,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)] at hh
    exact hh
  have hhi : ‖u.2‖≤‖e‖+k^2*‖u.1‖ := by
    have he : u.2=e+((k^2 : ℝ) : ℂ)*u.1 := by dsimp only [e]; ring
    have hh := norm_add_le e (((k^2 : ℝ) : ℂ)*u.1)
    rw [← he,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg k)] at hh
    exact hh
  have hc : ‖spectralGrowingCoefficient k delta u‖=‖v‖/(2*k) := by
    dsimp only [spectralGrowingCoefficient,v]
    rw [norm_div,norm_mul,Complex.norm_ofNat,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hk]
  rw [hc]
  apply (le_div_iff₀ (by positivity : 0<2*k)).mpr
  have hN : k*spectralShellNorm k u=k^2*‖u.1‖+‖u.2‖ := by
    dsimp only [spectralShellNorm]
    field_simp
  have hδ : 0≤delta*‖u.1‖ := mul_nonneg hdelta (norm_nonneg _)
  have hpos : 0≤k^2*‖u.1‖ := by positivity
  change ‖e‖≤k^2/2*‖u.1‖ at hnear
  nlinarith [hN]

end DefocusingNLS

end OAI

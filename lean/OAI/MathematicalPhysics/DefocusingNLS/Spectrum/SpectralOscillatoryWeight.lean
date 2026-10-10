import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralOscillatoryData
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWKBSquareRootJet

namespace OAI

/-! The complex momentum weight and the real outgoing normalization are
uniformly comparable at a positive-frequency remote endpoint. -/

namespace DefocusingNLS

theorem spectralComplexSqrt_weight_comparable (x gamma : ℝ) (hx : 0<x) (hg : |gamma|≤x) :
    Real.sqrt (Real.sqrt x)≤Real.sqrt ‖Complex.sqrt ((x : ℂ)+Complex.I*(gamma : ℂ))‖ ∧
    Real.sqrt ‖Complex.sqrt ((x : ℂ)+Complex.I*(gamma : ℂ))‖≤2*Real.sqrt (Real.sqrt x) := by
  let p := Complex.sqrt ((x : ℂ)+Complex.I*(gamma : ℂ))
  have hlo : Real.sqrt x≤‖p‖ := by
    simpa only [spectralWKBSquaredMomentum,Complex.ofReal_one,one_mul,abs_of_pos hx] using
      spectralWKBSqrt_frequency_lower 1 x gamma (by norm_num)
  have hZ : ‖(x : ℂ)+Complex.I*(gamma : ℂ)‖≤2*x := by
    have hh := norm_add_le (x : ℂ) (Complex.I*(gamma : ℂ))
    simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hx,norm_mul,Complex.norm_I,one_mul] at hh
    linarith
  have hp2 : ‖p‖^2≤2*x := (spectralComplexSqrt_norm_sq _).trans_le hZ
  have hxs : (Real.sqrt x)^2=x := Real.sq_sqrt hx.le
  have hpup : ‖p‖≤2*Real.sqrt x := by nlinarith [norm_nonneg p,Real.sqrt_nonneg x]
  refine ⟨Real.sqrt_le_sqrt hlo,?_⟩
  have hK := Real.sq_sqrt (norm_nonneg p)
  have hk := Real.sq_sqrt (Real.sqrt_nonneg x)
  nlinarith [Real.sqrt_nonneg ‖p‖,Real.sqrt_nonneg (Real.sqrt x)]

theorem spectralOscillatoryData_complex_norm (h x gamma : ℝ) (hh : h^2=1)
    (hx : 0<x) (hg : |gamma|≤x) :
    spectralShellNorm (Real.sqrt ‖Complex.sqrt ((x : ℂ)+Complex.I*(gamma : ℂ))‖)
      (spectralOscillatoryData h (Real.sqrt (Real.sqrt x)))≤3 := by
  obtain ⟨hl,hu⟩ := spectralComplexSqrt_weight_comparable x gamma hx hg
  exact spectralOscillatoryData_norm_le_three h _ _ hh
    (Real.sqrt_pos.2 (Real.sqrt_pos.2 hx)) hl hu

end DefocusingNLS

end OAI

import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarFlux
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralShellNorm

namespace OAI

/-! Exact normalized outgoing Cauchy data and their nonzero flux. -/

namespace DefocusingNLS

noncomputable def spectralOscillatoryData (h k : ℝ) : ℂ × ℂ :=
  ((k : ℂ)⁻¹,(h : ℂ)*Complex.I*(k : ℂ))

theorem spectralOscillatoryData_flux (h k : ℝ) (hk : k≠0) :
    spectralScalarFlux (spectralOscillatoryData h k)=h := by
  have hkC : (k : ℂ)≠0 := by exact_mod_cast hk
  have he : star (spectralOscillatoryData h k).1*(spectralOscillatoryData h k).2=
      (h : ℂ)*Complex.I := by
    simp only [spectralOscillatoryData,Complex.star_def,map_inv₀,Complex.conj_ofReal]
    field_simp [hkC]
  change (star (spectralOscillatoryData h k).1*(spectralOscillatoryData h k).2).im=h
  rw [he]
  simp only [Complex.mul_im,Complex.ofReal_re,Complex.I_im,Complex.ofReal_im,Complex.I_re,
    mul_one,mul_zero,add_zero]

theorem spectralOscillatoryData_robin (h k : ℝ) (hk : k≠0) :
    (spectralOscillatoryData h k).2=
      ((h : ℂ)*Complex.I*(k : ℂ)^2)*(spectralOscillatoryData h k).1 := by
  dsimp only [spectralOscillatoryData]
  have hkC : (k : ℂ)≠0 := by exact_mod_cast hk
  field_simp [hkC]

theorem spectralOscillatoryData_norm (h k K : ℝ) (hh : h^2=1) (hk : 0<k) :
    spectralShellNorm K (spectralOscillatoryData h k)=K/k+k/K := by
  have habs : |h|=1 := by nlinarith [sq_abs h,abs_nonneg h]
  simp only [spectralShellNorm,spectralOscillatoryData,norm_inv,norm_mul,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos hk,Complex.norm_I,habs,one_mul]
  ring

theorem spectralOscillatoryData_norm_le_three (h k K : ℝ) (hh : h^2=1) (hk : 0<k)
    (hlo : k≤K) (hhi : K≤2*k) :
    spectralShellNorm K (spectralOscillatoryData h k)≤3 := by
  have hK : 0<K := hk.trans_le hlo
  rw [spectralOscillatoryData_norm h k K hh hk]
  have h1 : K/k≤2 := (div_le_iff₀ hk).2 (by linarith)
  have h2 : k/K≤1 := (div_le_iff₀ hK).2 (by simpa using hlo)
  linarith

end DefocusingNLS

end OAI

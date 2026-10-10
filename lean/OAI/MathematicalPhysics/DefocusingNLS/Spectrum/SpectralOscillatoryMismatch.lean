import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWKBRemoteMismatch
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralOscillatoryData

namespace OAI

/-! The prescribed outgoing data select the WKB branch up to the remote
slope error, measured in the same weighted Cauchy norm. -/

namespace DefocusingNLS

theorem spectralCauchy_slope_error_norm (k : ℝ) (q u : ℂ × ℂ) (lambda : ℂ)
    (hu : u.1 ≠ 0) (hq : q.2 = lambda*q.1) :
    spectralShellNorm k (q-(q.1/u.1) • u) =
      (‖q.1‖/k)*‖lambda-u.2/u.1‖ := by
  have hf : q.1-(q.1/u.1)*u.1 = 0 := by field_simp; ring
  have hs : q.2-(q.1/u.1)*u.2 = q.1*(lambda-u.2/u.1) := by rw [hq]; ring
  dsimp only [spectralShellNorm,Prod.fst_sub,Prod.snd_sub,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]
  rw [hf,hs,norm_zero,mul_zero,zero_add,norm_mul]
  ring

theorem spectralOscillatoryData_mismatch_bound (h F K : ℝ) (L : ℂ) (u : ℂ × ℂ)
    (hF : 0 < F) (hK : Real.sqrt (Real.sqrt F) ≤ K)
    (hu : u.1 ≠ 0) (hL : u.2 = L*u.1) :
    spectralShellNorm K (spectralOscillatoryData h (Real.sqrt (Real.sqrt F)) -
      ((spectralOscillatoryData h (Real.sqrt (Real.sqrt F))).1/u.1) • u) ≤
      ‖((h : ℂ)*Complex.I)*(Real.sqrt F : ℂ)-L‖/Real.sqrt F := by
  let k := Real.sqrt (Real.sqrt F)
  have hS : 0 < Real.sqrt F := Real.sqrt_pos.mpr hF
  have hk : 0 < k := Real.sqrt_pos.mpr hS
  have hk2 : k^2 = Real.sqrt F := Real.sq_sqrt hS.le
  have hKC : 0 < K := hk.trans_le hK
  have hkC : (k : ℂ)^2 = (Real.sqrt F : ℂ) := by exact_mod_cast hk2
  have hq : (spectralOscillatoryData h k).2 =
      (((h : ℂ)*Complex.I)*(Real.sqrt F : ℂ))*(spectralOscillatoryData h k).1 := by
    simpa only [hkC] using spectralOscillatoryData_robin h k hk.ne'
  have hratio : u.2/u.1 = L := by rw [hL,mul_div_cancel_right₀ _ hu]
  have hnorm : ‖(spectralOscillatoryData h k).1‖ = 1/k := by
    simp only [spectralOscillatoryData,norm_inv,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos hk,one_div]
  change spectralShellNorm K (spectralOscillatoryData h k -
    ((spectralOscillatoryData h k).1/u.1) • u) ≤ _
  rw [spectralCauchy_slope_error_norm K _ u _ hu hq,hratio,hnorm]
  have hden : Real.sqrt F ≤ k*K := by nlinarith
  calc
    _ = ‖((h : ℂ)*Complex.I)*(Real.sqrt F : ℂ)-L‖/(k*K) := by ring
    _ ≤ _ := div_le_div_of_nonneg_left (norm_nonneg _) hS hden

end DefocusingNLS

end OAI

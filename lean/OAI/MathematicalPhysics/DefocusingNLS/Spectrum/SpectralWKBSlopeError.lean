import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWKBPhaseOrder
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralWKBSquareRootJet

namespace OAI

/-! The WKB slope at the remote endpoint differs from the prescribed outgoing
slope by the imaginary-potential error and the amplitude derivative. -/

namespace DefocusingNLS

theorem spectralWKB_oscillatory_slope_error (h F gamma g : ℝ)
    (hh : h^2 = 1) (hF : 0 < F) :
    ‖((h : ℂ)*Complex.I)*(Real.sqrt F : ℂ) -
      homogeneousSpectralWKBLog ((h : ℂ)*Complex.I)
        (Complex.sqrt ((F : ℂ)+Complex.I*(gamma : ℂ)))
        ((g : ℂ)/(2*Complex.sqrt ((F : ℂ)+Complex.I*(gamma : ℂ))))‖ ≤
      |gamma|/Real.sqrt F + |g|/(4*F) := by
  let p := Complex.sqrt ((F : ℂ)+Complex.I*(gamma : ℂ))
  have hsp : 0 < Real.sqrt F := Real.sqrt_pos.mpr hF
  have hlo : Real.sqrt F ≤ ‖p‖ := by
    simpa only [spectralWKBSquaredMomentum,Complex.ofReal_one,one_mul,abs_of_pos hF] using
      spectralWKBSqrt_frequency_lower 1 F gamma (by norm_num)
  have hpn : p ≠ 0 := norm_pos_iff.mp (hsp.trans_le hlo)
  have hpp : 0 < ‖p‖ := hsp.trans_le hlo
  have hp2 : F ≤ ‖p‖^2 := by nlinarith [Real.sq_sqrt hF.le]
  have hhabs : |h| = 1 := by nlinarith [sq_abs h,abs_nonneg h]
  have hchi : ‖(h : ℂ)*Complex.I‖ = 1 := by
    simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,hhabs,Complex.norm_I,mul_one]
  have he : ((h : ℂ)*Complex.I)*(Real.sqrt F : ℂ) -
      homogeneousSpectralWKBLog ((h : ℂ)*Complex.I) p ((g : ℂ)/(2*p)) =
      ((h : ℂ)*Complex.I)*((Real.sqrt F : ℂ)-p) + (g : ℂ)/(4*p^2) := by
    dsimp only [homogeneousSpectralWKBLog]
    field_simp
    ring
  rw [he]
  calc
    _ ≤ ‖((h : ℂ)*Complex.I)*((Real.sqrt F : ℂ)-p)‖ + ‖(g : ℂ)/(4*p^2)‖ := norm_add_le _ _
    _ = ‖p-(Real.sqrt F : ℂ)‖ + |g|/(4*‖p‖^2) := by
      rw [norm_mul,hchi,one_mul,norm_sub_rev,norm_div,norm_mul,norm_pow]
      simp only [Complex.norm_real,Real.norm_eq_abs,Complex.norm_ofNat]
    _ ≤ |gamma|/Real.sqrt F + |g|/(4*F) :=
      add_le_add (spectralComplexSqrt_approx F gamma hF)
        (div_le_div_of_nonneg_left (abs_nonneg g) (by positivity)
          (mul_le_mul_of_nonneg_left hp2 (by norm_num)))

end DefocusingNLS

end OAI

import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralScalarModulus

namespace OAI

/-! Resolve the normalized complex logarithmic derivative into momentum and flux. -/

namespace DefocusingNLS

theorem spectralScalarRatio_components (q : ℂ × ℂ) (s : ℝ) (hs : s≠0)
    (hq : q.1≠0) :
    q.2/((s : ℂ)*q.1)=
      ((spectralScalarMomentum q/(s*spectralScalarMass q) : ℝ) : ℂ)+
        Complex.I*((spectralScalarFlux q/(s*spectralScalarMass q) : ℝ) : ℂ) := by
  have hsC : (s : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hs
  have hQ : spectralScalarMass q≠0 := by
    dsimp only [spectralScalarMass]
    exact mt Complex.normSq_eq_zero.mp hq
  have hQC : (spectralScalarMass q : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hQ
  have hprod : (spectralScalarMass q : ℂ)=q.1*star q.1 := by
    exact (Complex.mul_conj q.1).symm
  have hnum : ((spectralScalarMomentum q : ℝ) : ℂ)+Complex.I*((spectralScalarFlux q : ℝ) : ℂ)=
      star q.1*q.2 := by
    dsimp only [spectralScalarMomentum,spectralScalarFlux]
    simpa only [mul_comm Complex.I] using Complex.re_add_im (star q.1*q.2)
  calc
    _ = (((spectralScalarMomentum q : ℝ) : ℂ)+Complex.I*((spectralScalarFlux q : ℝ) : ℂ))/
        ((s : ℂ)*(spectralScalarMass q : ℂ)) := by
      apply (div_eq_div_iff (mul_ne_zero hsC hq) (mul_ne_zero hsC hQC)).mpr
      rw [hprod,hnum]
      ring
    _ = _ := by push_cast; ring

end DefocusingNLS

end OAI

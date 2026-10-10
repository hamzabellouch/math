import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralDilationPairing

namespace OAI

/-! Integrating the derivative in this decomposition separates the real
volume pairing from the imaginary boundary flux. -/

namespace DefocusingNLS

theorem spectralDilationCross_decomposition (w s : ℝ) (f g df dg : ℂ) :
    spectralDilationCross w s f g df dg+
      ((2*s : ℝ) : ℂ)*star f*g+(w : ℂ)*(star df*g+star f*dg) =
      ((2*(w*(star dg*f).re+s*(star g*f).re) : ℝ) : ℂ) := by
  apply Complex.ext <;>
    simp only [spectralDilationCross,Complex.star_def,Complex.mul_re,Complex.mul_im,
      Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,Complex.conj_re,Complex.conj_im,
      Complex.ofReal_re,Complex.ofReal_im] <;> ring

end DefocusingNLS

end OAI

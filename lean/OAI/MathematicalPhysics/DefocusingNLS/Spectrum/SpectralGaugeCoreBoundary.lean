import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFreeCoreBoundary
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralGaugeRobin

namespace OAI

/-! The regular real-channel core conditions in physical circular coordinates. -/

namespace DefocusingNLS

theorem spectralGaugeCoreBoundary_eq (ell : ℕ) (r : ℝ) (f g df dg : ℂ) :
    spectralFreeCoreBoundary ell r
      ((f+Complex.I*g,df+Complex.I*dg),(f-Complex.I*g,df-Complex.I*dg))=
      ![2*f,2*Complex.I*(dg-(ell : ℂ)/(r : ℂ)*g)] := by
  funext j
  fin_cases j <;> dsimp [spectralFreeCoreBoundary] <;> ring

theorem spectralGaugeCoreBoundary_zero (ell : ℕ) (r : ℝ) (f g df dg : ℂ)
    (hf : f=0) (hg : dg=(ell : ℂ)/(r : ℂ)*g) :
    spectralFreeCoreBoundary ell r
      ((f+Complex.I*g,df+Complex.I*dg),(f-Complex.I*g,df-Complex.I*dg))=0 := by
  rw [spectralGaugeCoreBoundary_eq,hf,hg]
  simp

end DefocusingNLS

end OAI

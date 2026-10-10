import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalJet

namespace OAI

/-! Algebraic cancellation from the weighted scalar equation to the free gauge equation. -/

namespace DefocusingNLS

theorem spectralFreeGauge_algebra (r μ dμ A σ b ζ η q dq ddq u du ddu : ℂ)
    (hμ : μ ≠ 0)
    (hQ : ddq+(11/r+σ*Complex.I*r/2)*dq+b*q=0)
    (hC : (dμ+σ*Complex.I*A)*q=μ*(2*dq+σ*Complex.I*r/2*q))
    (hU : μ*ddu+(11*μ/r+dμ+σ*Complex.I*A)*du+
      (σ*Complex.I*ζ*μ-η*μ/r^2)*u=0) :
    ddq*u+2*dq*du+q*ddu+(11/r+σ*Complex.I*r/2)*(dq*u+q*du)+
      (b+σ*Complex.I*ζ-η/r^2)*(q*u)=0 := by
  apply (mul_eq_zero.mp (show μ*(ddq*u+2*dq*du+q*ddu+
      (11/r+σ*Complex.I*r/2)*(dq*u+q*du)+
      (b+σ*Complex.I*ζ-η/r^2)*(q*u))=0 by
    linear_combination q*hU-du*hC+μ*u*hQ)).resolve_left hμ

end DefocusingNLS

end OAI

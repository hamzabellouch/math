import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFreeGaugeAlgebra

namespace OAI

/-! Product cancellation for the radial stationary-profile gauge. -/

namespace DefocusingNLS

/-- The stationary equation cancels every zeroth-order term of a radial product. -/
theorem spectralRadialProductGauge (r a b p η σ q dq ddq u du ddu : ℂ)
    (hq : q ≠ 0)
    (hstat : σ*Complex.I*(ddq+11/r*dq)-r/2*dq+
      (-a+σ*Complex.I*b)*q-σ*Complex.I*p*q=0) :
    σ*Complex.I*(ddq*u+2*dq*du+q*ddu+11/r*(dq*u+q*du)-η/r^2*(q*u))-
      r/2*(dq*u+q*du)+(-a+σ*Complex.I*b)*(q*u)-σ*Complex.I*p*(q*u)=
    q*(σ*Complex.I*(ddu+(11/r+2*dq/q)*du-η/r^2*u)-r/2*du) := by
  have hc : q*(2*dq/q)=2*dq := by field_simp
  linear_combination u*hstat-σ*Complex.I*du*hc

/-- The two circular equations split into the real-coordinate complexification.
The variables remain complex; no reality hypothesis is imposed on an eigenmode. -/
theorem spectralCircularGaugeSplit (r η lam m p qlog qbarlog f df ddf g dg ddg : ℂ)
    (hp : lam*(f+Complex.I*g)=
      Complex.I*(ddf+Complex.I*ddg+(11/r+2*qlog)*(df+Complex.I*dg)-
        η/r^2*(f+Complex.I*g))-r/2*(df+Complex.I*dg)-2*Complex.I*m*p*f)
    (hm : lam*(f-Complex.I*g)=
      -Complex.I*(ddf-Complex.I*ddg+(11/r+2*qbarlog)*(df-Complex.I*dg)-
        η/r^2*(f-Complex.I*g))-r/2*(df-Complex.I*dg)+2*Complex.I*m*p*f) :
    lam*f=-(ddg+(11/r+qlog+qbarlog)*dg-η/r^2*g)-
        (r/2-Complex.I*(qlog-qbarlog))*df ∧
    lam*g=ddf+(11/r+qlog+qbarlog)*df-η/r^2*f-
        (r/2-Complex.I*(qlog-qbarlog))*dg-2*m*p*f := by
  have hI3 : Complex.I^3 = -Complex.I := by rw [pow_succ,Complex.I_sq]; ring
  constructor
  · linear_combination (norm := (ring_nf; simp only [Complex.I_sq]; ring)) (hp+hm)/2
  · linear_combination (norm := (ring_nf; simp only [Complex.I_sq,hI3]; ring))
      -Complex.I*(hp-hm)/2

end DefocusingNLS

end OAI

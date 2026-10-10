import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRadialProductGauge

namespace OAI

/-! The inhomogeneous circular gauge retains the physical Jordan source. -/

namespace DefocusingNLS

theorem spectralCircularSourceGaugeSplit (r η lam m p qlog qbarlog f df ddf g dg ddg F G : ℂ)
    (hp : lam*(f+Complex.I*g)+(F+Complex.I*G)=
      Complex.I*(ddf+Complex.I*ddg+(11/r+2*qlog)*(df+Complex.I*dg)-
        η/r^2*(f+Complex.I*g))-r/2*(df+Complex.I*dg)-2*Complex.I*m*p*f)
    (hm : lam*(f-Complex.I*g)+(F-Complex.I*G)=
      -Complex.I*(ddf-Complex.I*ddg+(11/r+2*qbarlog)*(df-Complex.I*dg)-
        η/r^2*(f-Complex.I*g))-r/2*(df-Complex.I*dg)+2*Complex.I*m*p*f) :
    lam*f+F=-(ddg+(11/r+qlog+qbarlog)*dg-η/r^2*g)-
        (r/2-Complex.I*(qlog-qbarlog))*df ∧
    lam*g+G=ddf+(11/r+qlog+qbarlog)*df-η/r^2*f-
        (r/2-Complex.I*(qlog-qbarlog))*dg-2*m*p*f := by
  have hI3 : Complex.I^3 = -Complex.I := by rw [pow_succ,Complex.I_sq]; ring
  constructor
  · linear_combination (norm := (ring_nf; simp only [Complex.I_sq]; ring)) (hp+hm)/2
  · linear_combination (norm := (ring_nf; simp only [Complex.I_sq,hI3]; ring))
      -Complex.I*(hp-hm)/2

end DefocusingNLS

end OAI

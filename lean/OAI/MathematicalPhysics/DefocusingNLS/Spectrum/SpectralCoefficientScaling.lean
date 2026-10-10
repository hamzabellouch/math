import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPolynomialEquation

namespace OAI

/-! Exact amplitude scaling of the two circular odd-power coefficients. -/

namespace DefocusingNLS

theorem spectralDiagonalCoefficient_scale (m : ℕ) (A q : ℂ) :
    spectralDiagonalCoefficient m (A*q)=(A*star A)^m*spectralDiagonalCoefficient m q := by
  simp only [spectralDiagonalCoefficient,star_mul,mul_pow]
  ring

theorem spectralCrossCoefficient_scale (m : ℕ) (hm : 1 ≤ m) (A q : ℂ) :
    spectralCrossCoefficient m (A*q)*star A=
      (A*star A)^m*A*spectralCrossCoefficient m q := by
  have hs : (star A)^(m-1)*star A=(star A)^m := by
    rw [← pow_succ]
    congr 1
    omega
  calc
    _ = A^m*((star A)^(m-1)*star A)*A*
        ((m : ℂ)*q^(m+1)*(star q)^(m-1)) := by
      simp only [spectralCrossCoefficient,star_mul,mul_pow,pow_succ]
      ring
    _ = (A*star A)^m*A*spectralCrossCoefficient m q := by
      rw [hs,mul_pow]
      unfold spectralCrossCoefficient
      ring

theorem spectralCircularCoefficient_scale (m : ℕ) (hm : 1 ≤ m)
    (A L q v w s : ℂ) (hA : (A*star A)^m=s) :
    spectralDiagonalCoefficient m (A*q)*(A*L*v)+
      spectralCrossCoefficient m (A*q)*(star A*L*w)=
        A*L*s*(spectralDiagonalCoefficient m q*v+spectralCrossCoefficient m q*w) := by
  have hd := spectralDiagonalCoefficient_scale m A q
  have hc := spectralCrossCoefficient_scale m hm A q
  rw [hA] at hd hc
  calc
    _ = (s*spectralDiagonalCoefficient m q)*(A*L*v)+
        (spectralCrossCoefficient m (A*q)*star A)*(L*w) := by rw [hd]; ring
    _ = _ := by rw [hc]; ring

end DefocusingNLS

end OAI

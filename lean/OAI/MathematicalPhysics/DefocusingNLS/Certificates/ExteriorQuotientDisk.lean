import OAI.MathematicalPhysics.DefocusingNLS.Certificates.ExteriorSlowCone
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.ExteriorFormDeterminant

namespace OAI

/-! Nonvanishing and the exact exterior disk for the true outgoing logarithmic derivative. -/

namespace DefocusingNLS.ExteriorCertificate

theorem exterior_slow_nonzero (b Z : ℝ)
    (hb : |100000000*b-33477607| ≤ 2) (hZ : 2704/1000 ≤ Z) :
    regularizedSlowSolution (-Complex.I*(b : ℂ)) 6 (-Complex.I*(Z : ℂ)) ≠ 0 := by
  have hZ0 : Z ≠ 0 := by linarith
  have hx : (-Complex.I*(Z : ℂ)) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (Complex.ofReal_ne_zero.mpr hZ0)
  have hjet := regularizedSlowSolution_jet_nonzero (-Complex.I*(b : ℂ)) 6
    (-Complex.I*(Z : ℂ)) (by simp) (by simp) hx
  exact hermitianPairForm_first_ne_zero _ _ _ _ _
    (exterior_diagonal_positive b Z hb hZ) (slow_exterior_pairForm b Z hZ0)
    (hjet.imp_right neg_ne_zero.mpr)

theorem exterior_slow_quotient_disk (b Z : ℝ)
    (hb : |100000000*b-33477607| ≤ 2) (hZ : 2704/1000 ≤ Z) :
    ‖(-deriv (regularizedSlowSolution (-Complex.I*(b : ℂ)) 6) (-Complex.I*(Z : ℂ)))/
        regularizedSlowSolution (-Complex.I*(b : ℂ)) 6 (-Complex.I*(Z : ℂ))+
        exteriorForm b Z 1 0/((exteriorForm b Z 1 1).re : ℂ)‖ ≤
      Z*‖(forwardProduct 5 (Complex.I*(Z : ℂ)) (-Complex.I*(b : ℂ)) 5).det‖/
        (exteriorForm b Z 1 1).re := by
  have hZ0 : Z ≠ 0 := by linarith
  have hd := exterior_diagonal_positive b Z hb hZ
  have he := forwardFormEntry_determinant 5 Z
    (forwardProduct 5 (Complex.I*(Z : ℂ)) (-Complex.I*(b : ℂ)) 5)
  change (exteriorForm b Z 0 0).re*(exteriorForm b Z 1 1).re-
    Complex.normSq (exteriorForm b Z 0 1) = _ at he
  have hdet : (exteriorForm b Z 0 0).re*(exteriorForm b Z 1 1).re-
      Complex.normSq (exteriorForm b Z 0 1) =
      -(Z*‖(forwardProduct 5 (Complex.I*(Z : ℂ)) (-Complex.I*(b : ℂ)) 5).det‖)^2 := by
    rw [he,Complex.normSq_eq_norm_sq]
    ring
  have h := hermitianPairForm_quotient_disk _ _ _ _ _ _ hd
    (mul_nonneg (by linarith) (norm_nonneg _)) (exterior_slow_nonzero b Z hb hZ)
    (slow_exterior_pairForm b Z hZ0) hdet
  have hc : star (exteriorForm b Z 0 1) = exteriorForm b Z 1 0 :=
    forwardFormEntry_hermitian 5 _ _ (by simp) 1 0
  rwa [hc] at h

end DefocusingNLS.ExteriorCertificate

end OAI

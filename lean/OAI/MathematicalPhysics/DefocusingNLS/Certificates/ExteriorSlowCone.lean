import OAI.MathematicalPhysics.DefocusingNLS.Certificates.ExteriorFormBounds
import OAI.MathematicalPhysics.DefocusingNLS.Certificates.ForwardConeTransport

namespace OAI

/-! The exact outgoing jet lies in the certified exterior forward cone. -/

namespace DefocusingNLS.ExteriorCertificate

theorem slow_exterior_cone (b Z : ℝ) (hZ : Z ≠ 0) :
    matrixCone 5 (Complex.I*(Z : ℂ))
      (forwardProduct 5 (Complex.I*(Z : ℂ)) (-Complex.I*(b : ℂ)) 5)
      (slowBoundaryColumn (-Complex.I*(b : ℂ)) 6 (Complex.I*(Z : ℂ))) ≤ 0 := by
  have hs : (Complex.I*(Z : ℂ)).re = 0 := by simp
  have hi : (Complex.I*(Z : ℂ)).im ≠ 0 := by simpa using hZ
  have hC := (normalizedMatching_tail_disk 0 0 5 (-Complex.I*(b : ℂ))
    (Complex.I*(Z : ℂ)) (by norm_num) (by decide) (by simp) hs hi).1
  have h := forward_matchingHomotopyColumn_cone 0 0 5 (-Complex.I*(b : ℂ))
    (Complex.I*(Z : ℂ)) 1 (by norm_num) (by decide) (by simp) hs hi
    (by norm_num) le_rfl
  norm_num only [Nat.cast_zero,zero_add] at h
  change matrixCone 5 (Complex.I*(Z : ℂ))
    (forwardProduct 5 (Complex.I*(Z : ℂ)) (-Complex.I*(b : ℂ)) 5)
    (matchingHomotopyColumn 5 5 (Complex.I*(Z : ℂ)) 1 (-Complex.I*(b : ℂ))) ≤ 0 at h
  rw [matchingHomotopyColumn_one 5 5 _ _ (by decide) (by simp) hs hi hC,
    matrixCone_smul] at h
  by_contra hn
  have hp := mul_pos (Complex.normSq_pos.mpr (inv_ne_zero hC)) (lt_of_not_ge hn)
  linarith

theorem slow_exterior_pairForm (b Z : ℝ) (hZ : Z ≠ 0) :
    hermitianPairForm (exteriorForm b Z 0 0).re (exteriorForm b Z 1 1).re
      (exteriorForm b Z 0 1)
      (regularizedSlowSolution (-Complex.I*(b : ℂ)) 6 (-Complex.I*(Z : ℂ)))
      (-deriv (regularizedSlowSolution (-Complex.I*(b : ℂ)) 6) (-Complex.I*(Z : ℂ))) ≤ 0 := by
  have h := slow_exterior_cone b Z hZ
  have he := forwardFormEntry_pairForm 5 (Complex.I*(Z : ℂ))
    (forwardProduct 5 (Complex.I*(Z : ℂ)) (-Complex.I*(b : ℂ)) 5)
    (by simp)
    (regularizedSlowSolution (-Complex.I*(b : ℂ)) 6 (-Complex.I*(Z : ℂ)))
    (-deriv (regularizedSlowSolution (-Complex.I*(b : ℂ)) 6) (-Complex.I*(Z : ℂ)))
  rw [slowBoundaryColumn_eq_jet _ _ _ (by simp) (by simp) (by simpa using hZ)] at h
  unfold exteriorForm
  simp only [neg_mul] at h he ⊢
  rw [he]
  linarith

end DefocusingNLS.ExteriorCertificate

end OAI

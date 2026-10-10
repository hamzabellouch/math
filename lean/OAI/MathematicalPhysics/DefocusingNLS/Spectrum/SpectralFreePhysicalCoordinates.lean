import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFreePhysicalBasis
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalCoupling

namespace OAI

/-! Identification of the zero-profile physical change of coordinates with
exactly the free H columns used by the matching determinant. -/

namespace DefocusingNLS

theorem spectralFreePositive_q (ell : ℕ) (b : ℝ) (z : ℂ) :
    ((ell : ℂ)-2*Complex.I*(b : ℂ))/2+z = spectralQ ell 1 b z := by
  unfold spectralQ
  push_cast
  ring

theorem spectralFreeNegative_q (ell : ℕ) (b : ℝ) (z : ℂ) :
    ((ell : ℂ)-(-2*Complex.I*(b : ℂ)))/2+z = spectralQ ell (-1) b z := by
  unfold spectralQ
  push_cast
  ring

theorem spectralPhysicalPair_free_positive (ell : ℕ) (b : ℝ) (z : ℂ) (r : ℝ) :
    spectralPhysicalPair (2*Complex.I*(b : ℂ)-2*z) (-2*Complex.I*(b : ℂ)-2*z)
      (spectralFreeFirstColumn ell (spectralQ ell 1 b z)) r =
      spectralFreePositivePhysical ell b z r := by
  have he : (ell : ℂ)-2*spectralQ ell 1 b z = 2*Complex.I*(b : ℂ)-2*z := by
    unfold spectralQ
    push_cast
    ring
  simp only [spectralPhysicalPair,spectralFreePositivePhysical,spectralFreeFirstColumn,he]
  apply Prod.ext
  · rfl
  · simp [spectralPhysicalJet]

theorem spectralPhysicalPair_free_negative (ell : ℕ) (b : ℝ) (z : ℂ) (r : ℝ) :
    spectralPhysicalPair (2*Complex.I*(b : ℂ)-2*z) (-2*Complex.I*(b : ℂ)-2*z)
      (spectralFreeSecondColumn ell (spectralQ ell (-1) b z)) r =
      spectralFreeNegativePhysical ell b z r := by
  have he : (ell : ℂ)-2*spectralQ ell (-1) b z = -2*Complex.I*(b : ℂ)-2*z := by
    unfold spectralQ
    push_cast
    ring
  rw [spectralFreeNegativePhysical_eq]
  simp only [spectralPhysicalPair,he]
  apply Prod.ext
  · simp [spectralFreeSecondColumn,spectralPhysicalJet]
  · rfl

theorem spectralPhysicalCircularField_free (b : ℝ) (z η : ℂ) (r : ℝ)
    (V : (ℂ × ℂ) × (ℂ × ℂ)) :
    spectralPhysicalCircularField (2*Complex.I*(b : ℂ)-2*z) (-2*Complex.I*(b : ℂ)-2*z) η 1 0 r V =
      spectralFreePhysicalPairField b z η r V := by
  apply Prod.ext <;> apply Prod.ext
  all_goals
    simp only [spectralPhysicalCircularField,spectralFreePhysicalPairField,spectralFreePhysicalField,
      spectralDiagonalCoefficient,spectralCrossCoefficient,star_zero,
      zero_pow (by omega : 1 ≠ 0),zero_pow (by omega : 2 ≠ 0),mul_zero,zero_mul,
      add_zero,one_mul,neg_mul]
  all_goals
    ring_nf
    simp only [Complex.I_sq]
    ring

end DefocusingNLS

end OAI

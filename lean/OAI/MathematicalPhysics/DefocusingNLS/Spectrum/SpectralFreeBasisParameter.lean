import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFreePhysicalParameter
import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralFreePhysicalCoordinates

namespace OAI

/-! Holomorphic free H basis columns and their actual parameter-forced physical equations. -/

namespace DefocusingNLS

theorem spectralFreePositivePhysical_analyticAt (ell : ℕ) (b : ℝ) (z : ℂ)
    (hq : -1 < (spectralQ ell 1 b z).re) (r : ℝ)
    (hrt : max 0 (Real.log 4/2) ≤ Real.log r) :
    AnalyticAt ℂ (fun lam => spectralFreePositivePhysical ell b lam r) z := by
  have hP := spectralFreeFirst_parameter_equation ell (2*Complex.I*(b : ℂ))
    (-2*Complex.I*(b : ℂ)) z (by simpa only [spectralFreePositive_q] using hq)
  have hA := spectralPhysicalPair_analyticAt
    (fun lam => 2*Complex.I*(b : ℂ)-2*lam) (fun lam => -2*Complex.I*(b : ℂ)-2*lam)
    (fun lam => spectralFreeFirstColumn ell (((ell : ℂ)-(2*Complex.I*(b : ℂ)))/2+lam)) z r
    (analyticAt_const.sub (analyticAt_const.mul analyticAt_id))
    (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)) (hP.1 (Real.log r) hrt)
  simpa only [spectralFreePositive_q,spectralPhysicalPair_free_positive] using hA

theorem spectralFreePositivePhysical_parameter_hasDerivAt (ell : ℕ) (b : ℝ) (z : ℂ)
    (hq : -1 < (spectralQ ell 1 b z).re) (r : ℝ) (hr : 0 < r)
    (hrt : max 0 (Real.log 4/2) < Real.log r) :
    HasDerivAt (fun s => deriv (fun lam => spectralFreePositivePhysical ell b lam s) z)
      (spectralFreePhysicalPairField b z ((ell : ℂ)*((ell : ℂ)+10)) r
        (deriv (fun lam => spectralFreePositivePhysical ell b lam r) z) +
        ((0,-Complex.I*(spectralFreePositivePhysical ell b z r).1.1),
         (0,Complex.I*(spectralFreePositivePhysical ell b z r).2.1))) r := by
  have h := spectralFreeFirstPhysical_parameter_equation ell (2*Complex.I*(b : ℂ))
    (-2*Complex.I*(b : ℂ)) z (by simpa only [spectralFreePositive_q] using hq) r hr hrt
  dsimp only at h
  simpa only [spectralFreePositive_q,spectralPhysicalPair_free_positive,spectralPhysicalCircularField_free,
    Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat] using h

theorem spectralFreeNegativePhysical_analyticAt (ell : ℕ) (b : ℝ) (z : ℂ)
    (hq : -1 < (spectralQ ell (-1) b z).re) (r : ℝ)
    (hrt : max 0 (Real.log 4/2) ≤ Real.log r) :
    AnalyticAt ℂ (fun lam => spectralFreeNegativePhysical ell b lam r) z := by
  have hP := spectralFreeSecond_parameter_equation ell (2*Complex.I*(b : ℂ))
    (-2*Complex.I*(b : ℂ)) z (by simpa only [spectralFreeNegative_q] using hq)
  have hA := spectralPhysicalPair_analyticAt
    (fun lam => 2*Complex.I*(b : ℂ)-2*lam) (fun lam => -2*Complex.I*(b : ℂ)-2*lam)
    (fun lam => spectralFreeSecondColumn ell (((ell : ℂ)-(-2*Complex.I*(b : ℂ)))/2+lam)) z r
    (analyticAt_const.sub (analyticAt_const.mul analyticAt_id))
    (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)) (hP.1 (Real.log r) hrt)
  simpa only [spectralFreeNegative_q,spectralPhysicalPair_free_negative] using hA

theorem spectralFreeNegativePhysical_parameter_hasDerivAt (ell : ℕ) (b : ℝ) (z : ℂ)
    (hq : -1 < (spectralQ ell (-1) b z).re) (r : ℝ) (hr : 0 < r)
    (hrt : max 0 (Real.log 4/2) < Real.log r) :
    HasDerivAt (fun s => deriv (fun lam => spectralFreeNegativePhysical ell b lam s) z)
      (spectralFreePhysicalPairField b z ((ell : ℂ)*((ell : ℂ)+10)) r
        (deriv (fun lam => spectralFreeNegativePhysical ell b lam r) z) +
        ((0,-Complex.I*(spectralFreeNegativePhysical ell b z r).1.1),
         (0,Complex.I*(spectralFreeNegativePhysical ell b z r).2.1))) r := by
  have h := spectralFreeSecondPhysical_parameter_equation ell (2*Complex.I*(b : ℂ))
    (-2*Complex.I*(b : ℂ)) z (by simpa only [spectralFreeNegative_q] using hq) r hr hrt
  dsimp only at h
  simpa only [spectralFreeNegative_q,spectralPhysicalPair_free_negative,spectralPhysicalCircularField_free,
    Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat] using h

end DefocusingNLS

end OAI

import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralPhysicalCoupling

namespace OAI

/-! The physical coordinate change with the acceleration sources required
by the differentiated outgoing equation. -/

namespace DefocusingNLS
local notation "E₄" => (ℂ × ℂ) × (ℂ × ℂ)

theorem spectralPhysicalFreePair_source_hasDerivAt (νp νm η : ℂ) (Y : ℝ → E₄) (r : ℝ) (hr : 0 < r) (F G : ℂ)
    (hY : HasDerivAt Y (circularLeadingField (Real.log r) (Y (Real.log r))+
      circularBoundedField νp νm η 1 0
        (Y (Real.log r)) + ((0, F), (0, G))) (Real.log r)) :
    HasDerivAt (spectralPhysicalPair νp νm Y)
      (spectralPhysicalCircularField νp νm η 1 0 r
        (spectralPhysicalPair νp νm Y r) +
        ((0, Complex.exp (νp*(Real.log r : ℂ))/(r : ℂ)^2*F),
         (0, Complex.exp (νm*(Real.log r : ℂ))/(r : ℂ)^2*G))) r := by
  have hdP : HasDerivAt (fun t => (Y t).1)
      ((Y (Real.log r)).1.2,-(2*νp+10)*(Y (Real.log r)).1.2-
      (νp*(νp+10)-η)*(Y (Real.log r)).1.1-
      (1 : ℂ)*Complex.I*(Real.exp (2*Real.log r)/2 : ℝ)*(Y (Real.log r)).1.2+F)
      (Real.log r) := by
    apply ((ContinuousLinearMap.fst ℝ (ℂ × ℂ) (ℂ × ℂ)).hasFDerivAt.comp_hasDerivAt
      (Real.log r) hY).congr_deriv
    rw [ContinuousLinearMap.coe_fst']
    apply Prod.ext
    · simp [circularLeadingField, circularBoundedField]
    · simp [circularLeadingField, circularBoundedField,spectralDiagonalCoefficient,
        spectralCrossCoefficient]
      ring
  have hdM : HasDerivAt (fun t => (Y t).2)
      ((Y (Real.log r)).2.2,-(2*νm+10)*(Y (Real.log r)).2.2-
      (νm*(νm+10)-η)*(Y (Real.log r)).2.1-
      (-1 : ℂ)*Complex.I*(Real.exp (2*Real.log r)/2 : ℝ)*(Y (Real.log r)).2.2+G)
      (Real.log r) := by
    apply ((ContinuousLinearMap.snd ℝ (ℂ × ℂ) (ℂ × ℂ)).hasFDerivAt.comp_hasDerivAt
      (Real.log r) hY).congr_deriv
    rw [ContinuousLinearMap.coe_snd']
    apply Prod.ext
    · simp [circularLeadingField, circularBoundedField]
    · simp [circularLeadingField, circularBoundedField,spectralDiagonalCoefficient,
        spectralCrossCoefficient]
      ring
  apply ((spectralPhysicalJet_hasDerivAt 1 νp η _ r hr F hdP).prodMk
    (spectralPhysicalJet_hasDerivAt (-1) νm η _ r hr G hdM)).congr_deriv
  apply Prod.ext <;> apply Prod.ext
  · simp only [Prod.fst_add,add_zero]
    rfl
  · dsimp only [spectralPhysicalPair,spectralPhysicalCircularField,spectralPhysicalJet,
      Prod.fst_add,Prod.snd_add,spectralDiagonalCoefficient,spectralCrossCoefficient]
    simp only [star_zero,zero_pow (by omega : 1 ≠ 0),zero_pow (by omega : 2 ≠ 0),
      mul_zero,zero_mul,add_zero,one_mul]
    ring
  · simp only [Prod.fst_add,Prod.snd_add,add_zero]
    rfl
  · dsimp only [spectralPhysicalPair,spectralPhysicalCircularField,spectralPhysicalJet,
      Prod.fst_add,Prod.snd_add,spectralDiagonalCoefficient,spectralCrossCoefficient]
    simp only [star_zero,zero_pow (by omega : 1 ≠ 0),zero_pow (by omega : 2 ≠ 0),
      mul_zero,zero_mul,add_zero,neg_mul,one_mul,neg_neg]
    ring

end DefocusingNLS

end OAI

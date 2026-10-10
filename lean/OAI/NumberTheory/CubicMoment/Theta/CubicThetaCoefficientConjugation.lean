import OAI.NumberTheory.CubicMoment.Theta.CubicThetaConjugateCoordinates

namespace OAI

/-! The full normalized arithmetic Fourier family commutes with
Eisenstein conjugation. Its ramified support and phases remain explicit. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma CubicThetaCoordinates.conjugated_unit_square {n : Eisenstein}
    (R : CubicThetaCoordinates n) :
    (R.conjugated.unit:Eisenstein)^2 = conjugate ((R.unit:Eisenstein)^2) := by
  simp only [conjugated,Units.val_mul,Units.val_pow_eq_pow_val,cubicTheta_conjugateUnit_val,Units.val_neg,Units.val_one,mul_pow,←pow_mul]
  rw [Nat.mul_comm R.order 2,pow_mul]
  norm_num [map_pow]

lemma CubicThetaCoordinates.conjugated_unit_real {n : Eisenstein}
    (R : CubicThetaCoordinates n) :
    ((R.conjugated.unit:Eisenstein) = 1 ∨ (R.conjugated.unit:Eisenstein) = -1) ↔
      ((R.unit:Eisenstein) = 1 ∨ (R.unit:Eisenstein) = -1) := by
  rw [←sq_eq_one_iff,←sq_eq_one_iff,R.conjugated_unit_square]
  exact ⟨fun h => conjugate.injective (h.trans (map_one conjugate).symm),
    fun h => by rw [h,map_one]⟩

lemma CubicThetaCoordinates.conjugated_coefficient {n : Eisenstein}
    (R : CubicThetaCoordinates n) : R.conjugated.coefficient = star R.coefficient := by
  have ht : cubicThetaTwistedGauss (conjugate R.squarefreePart)
      ((R.conjugated.unit:Eisenstein)^4*lambdaE^2) =
      star (cubicThetaTwistedGauss R.squarefreePart ((R.unit:Eisenstein)^4*lambdaE^2)) := by
    have hLam : conjugate (lambdaE^2) = lambdaE^2 := by
      rw [map_pow,cubicTheta_conjugate_lambda,neg_sq]
    have harg : (R.conjugated.unit:Eisenstein)^4*lambdaE^2 =
        conjugate ((R.unit:Eisenstein)^4*lambdaE^2) := by
      rw [map_mul,R.conjugated_unit_fourth,hLam]
    rw [harg,cubicThetaTwistedGauss,cubicThetaTwistedGauss,
      cubicSymbol_conjugate R.squarefree_primary,
      cubicTheta_gauss_conjugate R.squarefree_primary,star_mul,star_star]
    ring
  have hs : (R.conjugated.order % 3 = 1 ∧
      ((R.conjugated.unit:Eisenstein) = 1 ∨ (R.conjugated.unit:Eisenstein) = -1)) ↔
      (R.order % 3 = 1 ∧ ((R.unit:Eisenstein) = 1 ∨ (R.unit:Eisenstein) = -1)) :=
    and_congr Iff.rfl R.conjugated_unit_real
  change (R.order % 3 = 1 ∧
    ((R.conjugated.unit:Eisenstein) = 1 ∨ (R.conjugated.unit:Eisenstein) = -1)) ↔
    (R.order % 3 = 1 ∧ ((R.unit:Eisenstein) = 1 ∨ (R.unit:Eisenstein) = -1)) at hs
  simp only [coefficient,show R.conjugated.order = R.order from rfl,hs,
    show R.conjugated.squarefreePart = conjugate R.squarefreePart from rfl,
    R.conjugated_amplitude,R.conjugated_phase,ht]
  split_ifs <;> simp only [star_mul,star_zero,Complex.star_def,Complex.conj_ofReal,
    cubicTheta_gauss_conjugate R.squarefree_primary] <;> ring


theorem cubicThetaArithmeticCoefficient_conjugate (n : Eisenstein) :
    cubicThetaArithmeticCoefficient (conjugate n) = star (cubicThetaArithmeticCoefficient n) := by
  by_cases hn : Nonempty (CubicThetaCoordinates n)
  · let R := Classical.choice hn
    rw [cubicThetaArithmeticCoefficient_formula R.conjugated,
      cubicThetaArithmeticCoefficient_formula R,R.conjugated_coefficient]
  · have hc : ¬Nonempty (CubicThetaCoordinates (conjugate n)) := by
      rintro ⟨R⟩
      exact hn (by simpa only [conjugate_conjugate] using
        (show Nonempty (CubicThetaCoordinates (conjugate (conjugate n))) from ⟨R.conjugated⟩))
    simp only [cubicThetaArithmeticCoefficient,dite_eq_right hn,dite_eq_right hc,star_zero]

end CubicFirstMoment

end

end OAI

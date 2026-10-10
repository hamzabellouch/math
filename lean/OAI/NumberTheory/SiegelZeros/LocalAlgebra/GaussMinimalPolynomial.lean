import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import OAI.NumberTheory.SiegelZeros.Structure.GaussFixedField

namespace OAI

namespace SiegelZeros


namespace SiegelZerosAwei.W09

open Polynomial

variable {q : ℕ} [NeZero q]

noncomputable def signedConductor (χ : DirichletCharacter ℂ q) : ℤ :=
  if χ (-1) = 1 then (q : ℤ) else -(q : ℤ)

omit [NeZero q] in
theorem signedConductor_cast (χ : DirichletCharacter ℂ q) (hq : χ.IsQuadratic) :
    (signedConductor χ : ℂ) = χ (-1) * (q : ℂ) := by
  unfold signedConductor
  split_ifs with he
  · simp [he]
  · rcases hq (-1) with hzero | hone | hneg
    · exact ((isUnit_neg_one.map χ).ne_zero hzero).elim
    · exact (he hone).elim
    · simp [hneg]

omit [NeZero q] in
theorem signedConductor_natAbs (χ : DirichletCharacter ℂ q) :
    (signedConductor χ).natAbs = q := by
  unfold signedConductor
  split <;> simp

theorem signedConductor_ne_zero (χ : DirichletCharacter ℂ q) :
    signedConductor χ ≠ 0 := by
  intro h
  have hn := signedConductor_natAbs χ
  rw [h, Int.natAbs_zero] at hn
  exact (NeZero.ne q) hn.symm

theorem characterGaussSum_sq_signedConductor (χ : DirichletCharacter ℂ q)
    (hp : χ.IsPrimitive) (hq : χ.IsQuadratic) :
    characterGaussSum χ ^ 2 = (signedConductor χ : ℂ) := by
  rw [characterGaussSum_sq χ hp hq, signedConductor_cast χ hq]

theorem characterGaussSum_minpoly_rat (χ : DirichletCharacter ℂ q)
    (hp : χ.IsPrimitive) (hq : χ.IsQuadratic) (hn : χ ≠ 1) :
    minpoly ℚ (characterGaussSum χ) = X ^ 2 - C (signedConductor χ : ℚ) := by
  have hi : IsIntegral ℚ (characterGaussSum χ) :=
    (characterGaussSum_isIntegral χ hp hq).tower_top
  have hd : (minpoly ℚ (characterGaussSum χ)).natDegree = 2 := by
    rw [← IntermediateField.adjoin.finrank hi]
    exact characterField_finrank χ hp hq hn
  have hm : (X ^ 2 - C (signedConductor χ : ℚ)).Monic :=
    monic_X_pow_sub_C _ (by decide : 2 ≠ 0)
  symm
  apply minpoly.unique_of_degree_le_degree_minpoly ℚ (characterGaussSum χ) hm
  · simp [characterGaussSum_sq_signedConductor χ hp hq]
  · rw [degree_eq_natDegree hm.ne_zero, degree_eq_natDegree (minpoly.ne_zero hi),
      natDegree_X_pow_sub_C, hd]

theorem characterGaussSum_minpoly_int (χ : DirichletCharacter ℂ q)
    (hp : χ.IsPrimitive) (hq : χ.IsQuadratic) (hn : χ ≠ 1) :
    minpoly ℤ (characterGaussSum χ) = X ^ 2 - C (signedConductor χ) := by
  apply Polynomial.map_injective (f := algebraMap ℤ ℚ) (algebraMap ℤ ℚ).injective_int
  rw [← minpoly.isIntegrallyClosed_eq_field_fractions' ℚ
    (characterGaussSum_isIntegral χ hp hq), characterGaussSum_minpoly_rat χ hp hq hn]
  simp

theorem characterGaussSum_minpoly_discr (χ : DirichletCharacter ℂ q)
    (hp : χ.IsPrimitive) (hq : χ.IsQuadratic) (hn : χ ≠ 1) :
    Polynomial.discr (minpoly ℤ (characterGaussSum χ)) = 4 * signedConductor χ := by
  rw [characterGaussSum_minpoly_int χ hp hq hn]
  have hm : (X ^ 2 - C (signedConductor χ) : ℤ[X]).Monic :=
    monic_X_pow_sub_C _ (by decide : 2 ≠ 0)
  rw [Polynomial.discr_of_degree_eq_two (by
    rw [degree_eq_natDegree hm.ne_zero, natDegree_X_pow_sub_C]
    rfl)]
  simp only [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C]
  simp

end SiegelZerosAwei.W09


end SiegelZeros

end OAI

import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterTrivialZero
import OAI.NumberTheory.Ostmann.ZeroDensity.CharacterZeroSet

namespace OAI

/-! # The only zeros crossed by the fixed smooth contour

Between Re(s)=-1/2 and Re(s)=2 the poles of the logarithmic derivative are
precisely the critical-strip zeros, together with the possible zero at zero.
-/

namespace Ostmann

open Complex

theorem PrimitiveComplexCharacter.L_ne_zero_one_le_re (χ : PrimitiveComplexCharacter)
    (z : ℂ) (hz : 1 ≤ z.re) : χ.L z ≠ 0 := by
  let : NeZero χ.modulus := ⟨χ.positive.ne'⟩
  exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ.character (.inl χ.nontrivial) hz

theorem PrimitiveComplexCharacter.completed_ne_zero_left (χ : PrimitiveComplexCharacter)
    (z : ℂ) (hz : z.re ≤ 0) : χ.completed z ≠ 0 := by
  apply (χ.completed_analytic z).analyticOrderAt_eq_zero.mp
  have hpos : 0 < (1 - z).re := by simp; linarith
  have hge : 1 ≤ (1 - z).re := by simp; linarith
  calc
    analyticOrderAt χ.completed z = analyticOrderAt χ.inverse.completed (1 - z) := by
      simpa using χ.completed_order_reflection (1 - z)
    _ = analyticOrderAt χ.inverse.L (1 - z) := (χ.inverse.L_order_eq_completed _ hpos).symm
    _ = 0 := (χ.inverse.L_analytic _).analyticOrderAt_eq_zero.mpr
      (χ.inverse.L_ne_zero_one_le_re _ hge)

theorem PrimitiveComplexCharacter.L_ne_zero_left_ne_origin (χ : PrimitiveComplexCharacter)
    (z : ℂ) (hz : -(1 / 2 : ℝ) ≤ z.re) (hz' : z.re ≤ 0) (hne : z ≠ 0) : χ.L z ≠ 0 := by
  rw [χ.L_eq_completed_mul z hne]
  apply mul_ne_zero (χ.completed_ne_zero_left z hz')
  classical
  unfold PrimitiveComplexCharacter.gammaInverse DirichletCharacter.gammaFactor
  split_ifs
  · rw [gammaReal_inverse_factor]
    apply mul_ne_zero hne
    apply mul_ne_zero (inv_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)))
    apply inv_ne_zero
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    simp only [add_re]
    norm_num
    linarith
  · apply inv_ne_zero
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    simp only [add_re, one_re]
    linarith

theorem PrimitiveComplexCharacter.contour_zero_location (χ : PrimitiveComplexCharacter)
    (z : ℂ) (hz : -(1 / 2 : ℝ) ≤ z.re) (hzero : χ.L z = 0) :
    z = 0 ∨ z ∈ complexCharacterZeros χ := by
  by_cases hne : z = 0
  · exact .inl hne
  right
  have hpos : 0 < z.re := by
    by_contra hh
    exact χ.L_ne_zero_left_ne_origin z hz (not_lt.mp hh) hne hzero
  have hlt : z.re < 1 := by
    by_contra hh
    exact χ.L_ne_zero_one_le_re z (not_lt.mp hh) hzero
  exact ⟨hpos, hlt, hzero⟩

end Ostmann

end OAI

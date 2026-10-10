import Mathlib
import OAI.NumberTheory.CubicGram.IntegerBasis

namespace OAI

/-! Eisenstein integers, norm, residue quotients and cubic first-moment definitions. -/

noncomputable section
open scoped BigOperators
open Module Complex UniqueFactorizationMonoid
attribute [local instance] Classical.propDecidable

namespace CubicFirstMoment

lemma residueRepresentative_spec (p : Eisenstein) (v : Residues p) :
    Ideal.Quotient.mk (modulus p) (residueRepresentative p v) = v :=
  Classical.choose_spec (Ideal.Quotient.mk_surjective v)

lemma real_coordinates_norm (a b : ℝ) :
    Complex.normSq ((a : ℂ) + (b : ℂ)*omega) = a^2-a*b+b^2 := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, omega_re, omega_im]
  ring_nf
  norm_num [Real.sq_sqrt]
  ring

lemma complex_coordinates (z : ℂ) :
    z = ((z.re + z.im / Real.sqrt 3 : ℝ) : ℂ) +
      ((2*z.im / Real.sqrt 3 : ℝ) : ℂ)*omega := by
  have hs : Real.sqrt (3 : ℝ) ≠ 0 := by positivity
  apply Complex.ext
  · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, omega_re, zero_mul, sub_zero]
    ring
  · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, omega_im, zero_mul, add_zero, zero_add]
    field_simp

end CubicFirstMoment
end

end OAI

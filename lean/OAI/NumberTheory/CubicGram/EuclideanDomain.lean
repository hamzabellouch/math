import Mathlib
import OAI.NumberTheory.CubicGram.IntegerBasis

namespace OAI

/-! Nearest-lattice division and the Eisenstein Euclidean domain. -/

section
noncomputable section
open scoped BigOperators
open Module
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
@[simp] lemma normNat_mul (x y : Eisenstein) : normNat (x*y) = normNat x * normNat y := by
  apply Nat.cast_injective (R := ℝ)
  simp only [Nat.cast_mul, normNat_cast]
  exact Complex.normSq_mul _ _

@[simp] lemma normNat_one : normNat 1 = 1 := by
  apply Nat.cast_injective (R := ℝ)
  simp only [normNat_cast, Nat.cast_one]
  exact Complex.normSq_one

@[simp] lemma normNat_zero : normNat 0 = 0 := by
  apply Nat.cast_injective (R := ℝ)
  simp only [normNat_cast, Nat.cast_zero]
  exact Complex.normSq_zero

lemma real_coordinates_norm (a b : ℝ) :
    Complex.normSq ((a : ℂ) + (b : ℂ)*omega) = a^2-a*b+b^2 := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, omega_re, omega_im]
  ring_nf
  norm_num [Real.sq_sqrt]
  ring

def nearestEisenstein (z : ℂ) : Eisenstein :=
  ofCoords (round (z.re + z.im / Real.sqrt 3)) (round (2*z.im / Real.sqrt 3))

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

lemma nearestEisenstein_normSq_lt (z : ℂ) :
    Complex.normSq (z - (nearestEisenstein z : ℂ)) < 1 := by
  let a : ℝ := z.re + z.im / Real.sqrt 3
  let b : ℝ := 2*z.im / Real.sqrt 3
  have hdist : z - (nearestEisenstein z : ℂ) =
      ((a - round a : ℝ) : ℂ) + ((b - round b : ℝ) : ℂ)*omega := by
    conv_lhs => lhs; rw [complex_coordinates z]
    simp only [nearestEisenstein, ofCoords_coe]
    dsimp only [a, b]
    push_cast
    ring
  have ha : (a - round a)^2 ≤ (1/2 : ℝ)^2 :=
    sq_le_sq.mpr (by simpa using (abs_sub_round a))
  have hb : (b - round b)^2 ≤ (1/2 : ℝ)^2 :=
    sq_le_sq.mpr (by simpa using (abs_sub_round b))
  rw [hdist, real_coordinates_norm]
  nlinarith [sq_nonneg (a-round a + (b-round b))]

@[simp] lemma nearestEisenstein_zero : nearestEisenstein 0 = 0 := by
  simp [nearestEisenstein, ofCoords]

def latticeQuotient (x y : Eisenstein) : Eisenstein :=
  nearestEisenstein ((x : ℂ)/(y : ℂ))

def latticeRemainder (x y : Eisenstein) : Eisenstein := x-y*latticeQuotient x y

lemma normNat_latticeRemainder_lt (x : Eisenstein) {y : Eisenstein} (hy : y ≠ 0) :
    normNat (latticeRemainder x y) < normNat y := by
  have hy' : (y : ℂ) ≠ 0 := fun h => hy (Subtype.ext h)
  have hrepr : (latticeRemainder x y : ℂ) = (y : ℂ) *
      ((x : ℂ)/(y : ℂ) - (nearestEisenstein ((x : ℂ)/(y : ℂ)) : ℂ)) := by
    simp only [latticeRemainder, latticeQuotient, Subalgebra.coe_sub, Subalgebra.coe_mul,
      mul_sub, mul_div_cancel₀ _ hy']
  have hnorm : norm (latticeRemainder x y) < norm y := by
    rw [norm, hrepr, Complex.normSq_mul]
    exact mul_lt_of_lt_one_right (Complex.normSq_pos.mpr hy') (nearestEisenstein_normSq_lt _)
  rwa [← normNat_cast, ← normNat_cast, Nat.cast_lt] at hnorm

instance eisensteinEuclideanDomain : EuclideanDomain Eisenstein where
  quotient := latticeQuotient
  quotient_zero x := by simp [latticeQuotient]
  remainder := latticeRemainder
  quotient_mul_add_remainder_eq x y := by simp [latticeRemainder]
  r x y := normNat x < normNat y
  r_wellFounded := (measure normNat).wf
  remainder_lt := normNat_latticeRemainder_lt
  mul_left_not_lt x y hy := by
    change ¬ normNat (x*y) < normNat x
    rw [normNat_mul, not_lt]
    exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (normNat_ne_zero hy))

open UniqueFactorizationMonoid

instance eisensteinNormalization : StrongNormalizationMonoid Eisenstein :=
  UniqueFactorizationMonoid.strongNormalizationMonoid

def normNatHom : Eisenstein →* ℕ where
  toFun := normNat
  map_one' := normNat_one
  map_mul' := normNat_mul

lemma associated_normNat {x y : Eisenstein} (h : Associated x y) :
    normNat x = normNat y :=
  associated_iff_eq.mp (h.map normNatHom)

end CubicFirstMoment
end
end

end OAI

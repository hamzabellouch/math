import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialMatrixGroup
import Mathlib.GroupTheory.Commutator.Basic

namespace OAI

/-! # Polynomial continuity of commutator sections

For a fixed matrix, conjugation by the variable matrix is polynomial in
the matrix and inverse coordinates. Hence the commutator is continuous
in either variable separately in the polynomial topology.
-/

noncomputable section
namespace PolycyclicRecognition.PolynomialMatrixGroup

open scoped commutatorElement
variable {K : Type*} [Field K] {n : ℕ}

def conjugationPolynomial (h : PolynomialMatrixGroup K n) (s : Coord n) :
    MvPolynomial (Coord n) K :=
  ∑ l, ∑ k, MvPolynomial.X (false, s.2.1, k) *
    MvPolynomial.C ((if s.1 then entries h⁻¹ else entries h) k l) *
    MvPolynomial.X (true, l, s.2.2)

theorem coordinates_conjugation_fixed (h g : PolynomialMatrixGroup K n) :
    coordinates (g * h * g⁻¹) =
      AffinePolynomialPoint.polynomialMap (conjugationPolynomial h) (coordinates g) := by
  have he : (g * h * g⁻¹)⁻¹ = g * h⁻¹ * g⁻¹ := by group
  apply AffinePolynomialPoint.ext
  funext ⟨b, i, j⟩
  cases b <;> simp [coordinates, AffinePolynomialPoint.polynomialMap, conjugationPolynomial,
    he, Matrix.mul_apply, Finset.sum_mul]

theorem continuous_conjugation_fixed (h : PolynomialMatrixGroup K n) :
    Continuous (fun g : PolynomialMatrixGroup K n => g * h * g⁻¹) :=
  continuous_of_polynomial _ (conjugationPolynomial h) (coordinates_conjugation_fixed h)

theorem continuous_commutator_right (h : PolynomialMatrixGroup K n) :
    Continuous (fun g : PolynomialMatrixGroup K n => ⁅g, h⁆) := by
  change Continuous (fun g : PolynomialMatrixGroup K n => (g * h * g⁻¹) * h⁻¹)
  exact (continuous_conjugation_fixed h).mul_const h⁻¹

theorem continuous_commutator_left (g : PolynomialMatrixGroup K n) :
    Continuous (fun h : PolynomialMatrixGroup K n => ⁅g, h⁆) := by
  have he : (fun h : PolynomialMatrixGroup K n => ⁅g, h⁆) =
      fun h => (⁅h, g⁆)⁻¹ := by
    funext h
    exact (commutatorElement_inv h g).symm
  rw [he]
  exact (continuous_commutator_right g).inv

end PolycyclicRecognition.PolynomialMatrixGroup

end

end OAI

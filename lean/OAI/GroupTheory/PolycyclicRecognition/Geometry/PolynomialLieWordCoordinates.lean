import OAI.GroupTheory.PolycyclicRecognition.Geometry.FiniteLieNorm
import OAI.GroupTheory.PolycyclicRecognition.Algebra.DynkinWords
import Mathlib.Algebra.MvPolynomial.Eval

namespace OAI

/-! # Coordinate polynomials for finite Lie expressions -/

noncomputable section
namespace PolycyclicRecognition

open scoped BigOperators

variable {L I J S A : Type*} [LieRing L] [LieAlgebra ℝ L] [Fintype J]
  [CommRing A] [Algebra ℝ A] (b : Module.Basis J ℝ L)

def bracketCoordinatePolynomial (X : I → J → MvPolynomial S A) :
    FreeMagma I → J → MvPolynomial S A
  | .of i => X i
  | .mul u v => fun j => ∑ k, ∑ l,
      MvPolynomial.C (algebraMap ℝ A (b.repr ⁅b k, b l⁆ j)) *
        bracketCoordinatePolynomial X u k * bracketCoordinatePolynomial X v l

theorem eval_bracketCoordinatePolynomial
    (X : I → J → MvPolynomial S A) (f : A →ₐ[ℝ] ℝ) (a : S → ℝ)
    (Y : I → L) (hX : ∀ i j, (X i j).eval₂ f.toRingHom a = b.repr (Y i) j)
    (w : FreeMagma I) (j : J) :
    (bracketCoordinatePolynomial b X w j).eval₂ f.toRingHom a =
      b.repr (evalBracketWord Y w) j := by
  have hc (r : ℝ) : f.toRingHom (algebraMap ℝ A r) = r := f.commutes r
  induction w using FreeMagma.rec generalizing j with
  | of i => exact hX i j
  | mul u v hu hv =>
    simp only [bracketCoordinatePolynomial, MvPolynomial.eval₂_sum,
      MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, hc, hu, hv, evalBracketWord]
    rw [basis_bracket_coordinate]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring

def dynkinCoordinatePolynomial {c n : ℕ} (coeff : DynkinCoefficients c n)
    (X : Fin n → J → MvPolynomial S A) (j : J) : MvPolynomial S A :=
  ∑ d : Fin c, ∑ w : Fin (d.val + 1) → Fin n,
    MvPolynomial.C (algebraMap ℝ A (coeff d w)) *
      bracketCoordinatePolynomial b X (rightNestedWord d.val w) j

theorem eval_dynkinCoordinatePolynomial {c n : ℕ} (coeff : DynkinCoefficients c n)
    (X : Fin n → J → MvPolynomial S A) (f : A →ₐ[ℝ] ℝ) (a : S → ℝ)
    (Y : Fin n → L) (hX : ∀ i j, (X i j).eval₂ f.toRingHom a = b.repr (Y i) j)
    (j : J) :
    (dynkinCoordinatePolynomial b coeff X j).eval₂ f.toRingHom a =
      b.repr (finiteDynkinPolynomial coeff Y) j := by
  have hc (r : ℝ) : f.toRingHom (algebraMap ℝ A r) = r := f.commutes r
  simp only [dynkinCoordinatePolynomial, finiteDynkinPolynomial,
    MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C,
    hc, eval_bracketCoordinatePolynomial b X f a Y hX,
    map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]

end PolycyclicRecognition

end

end OAI

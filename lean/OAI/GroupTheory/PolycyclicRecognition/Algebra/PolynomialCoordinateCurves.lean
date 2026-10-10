import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialFunctionSpace
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialModelRepresentation
import Mathlib.Algebra.MvPolynomial.Equiv

namespace OAI

/-! # Polynomial scalar curves in polynomial group coordinates -/

noncomputable section
namespace PolycyclicRecognition

variable {L J : Type*} [RealNormedLieAlgebra L] [Fintype J]
  (b : Module.Basis J ℝ L)

def HasPolynomialLineCoordinates (F : ℝ → L) : Prop :=
  ∀ j, (fun t => b.repr (F t) j) ∈ polynomialFunctions

omit [Fintype J] in
theorem hasPolynomialLineCoordinates_const (v : L) : HasPolynomialLineCoordinates b (fun _ => v) :=
  fun j => polynomialFunctions_const (b.repr v j)

omit [Fintype J] in
theorem hasPolynomialLineCoordinates_line (v : L) : HasPolynomialLineCoordinates b (fun t => t • v) := by
  intro j
  simpa only [map_smul, Finsupp.smul_apply, smul_eq_mul] using
    polynomialFunctions_linear (b.repr v j)

theorem hasPolynomialLineCoordinates_dynkin {c n : ℕ} (coeff : DynkinCoefficients c n)
    (F : Fin n → ℝ → L) (hF : ∀ i, HasPolynomialLineCoordinates b (F i)) :
    HasPolynomialLineCoordinates b (fun t => finiteDynkinPolynomial coeff (fun i => F i t)) := by
  have h : ∀ i j, ∃ p : Polynomial ℝ, ∀ t, p.eval t = b.repr (F i t) j :=
    fun i j => mem_polynomialFunctions_iff.mp (hF i j)
  choose p hp using h
  let X : Fin n → J → MvPolynomial Unit ℝ :=
    fun i j => (MvPolynomial.uniqueAlgEquiv ℝ Unit).symm (p i j)
  intro j
  apply mem_polynomialFunctions_iff.mpr
  refine ⟨MvPolynomial.uniqueAlgEquiv ℝ Unit (dynkinCoordinatePolynomial b coeff X j), ?_⟩
  intro t
  rw [Polynomial.eval, MvPolynomial.eval₂_const_uniqueAlgEquiv]
  apply eval_dynkinCoordinatePolynomial b coeff X (AlgHom.id ℝ ℝ)
  intro i k
  change ((MvPolynomial.uniqueAlgEquiv ℝ Unit).symm (p i k)).eval₂ (RingHom.id ℝ) (fun _ => t) = _
  rw [MvPolynomial.eval₂_const_uniqueAlgEquiv_symm, Polynomial.eval₂_id]
  exact hp i k t

section Group

variable [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L]

theorem hasPolynomialLineCoordinates_mul (F H : ℝ → L)
    (hF : HasPolynomialLineCoordinates b F) (hH : HasPolynomialLineCoordinates b H) :
    HasPolynomialLineCoordinates b (fun t => F t * H t) := by
  have h := hasPolynomialLineCoordinates_dynkin b P.coefficients ![F, H] (by
    intro i
    fin_cases i
    · exact hF
    · exact hH)
  have heq : (fun t => finiteDynkinPolynomial P.coefficients (fun i => ![F, H] i t)) =
      (fun t => F t * H t) := by
    funext t
    rw [P.mul_eq]
    congr 1
    ext i
    fin_cases i <;> rfl
  rwa [heq] at h

end Group

end PolycyclicRecognition

end

end OAI

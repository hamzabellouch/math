import OAI.GroupTheory.PolycyclicRecognition.Geometry.NilpotentSemidirectGroup
import OAI.GroupTheory.PolycyclicRecognition.Geometry.PolynomialLieWordCoordinates
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialCoordinateOrbit

namespace OAI

/-! # Polynomial coordinate orbits in the nilpotent semidirect construction -/

noncomputable section
namespace PolycyclicRecognition

open scoped BigOperators ContDiff

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] {n : ℕ}
  (b : Module.Basis (Fin n) ℝ L)
  (D : LieDerivation ℝ L L) (hD : IsNilpotent D.toLinearMap)

local instance semidirectCoordinateModuleRat : Module ℚ L := Module.compHom L (algebraMap ℚ ℝ)

def semidirectCoordinate : (Fin n ⊕ Unit) → (L × ℝ) → ℝ
  | .inl i, p => b.repr p.1 i
  | .inr _, p => p.2

omit [FiniteDimensional ℝ L] P in
theorem semidirectCoordinate_injective :
    Function.Injective (fun g => fun i => semidirectCoordinate b i g) := by
  intro x y h
  apply Prod.ext
  · apply b.repr.injective
    ext i
    exact congrFun h (.inl i)
  · exact congrFun h (.inr ())

omit P in
theorem contDiff_semidirectCoordinate (i : Fin n ⊕ Unit) :
    ContDiff ℝ ∞ (semidirectCoordinate b i) := by
  cases i with
  | inl i => exact (contDiff_pi.mp b.equivFun.toContinuousLinearEquiv.contDiff i).comp contDiff_fst
  | inr i => exact contDiff_snd

def semidirectFlowCoordinatePolynomial (k : ℕ) (j : Fin n) :
    MvPolynomial (Fin n ⊕ Unit) ((L × ℝ) → ℝ) :=
  ∑ i ∈ Finset.range k,
    MvPolynomial.C (fun g => b.repr (((i.factorial : ℚ)⁻¹ • D.toLinearMap ^ i) g.1) j) *
      MvPolynomial.X (.inr ()) ^ i

omit [FiniteDimensional ℝ L] P in
theorem semidirectFlowCoordinatePolynomial_eval {k : ℕ} (hk : D.toLinearMap ^ k = 0)
    (x g : L × ℝ) (j : Fin n) :
    coordinatePolynomialEvaluation (semidirectCoordinate b)
      (semidirectFlowCoordinatePolynomial b D k j) g x =
      b.repr (nilpotentDerivationFlow D hD x.2 g.1) j := by
  rw [nilpotentDerivationFlow_eq_sum D hD hk]
  simp only [semidirectFlowCoordinatePolynomial, coordinatePolynomialEvaluation,
    MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C,
    MvPolynomial.eval₂_pow, MvPolynomial.eval₂_X, Pi.evalRingHom_apply,
    semidirectCoordinate, map_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact mul_comm _ _

def semidirectProductCoordinatePolynomial (k : ℕ) :
    (Fin n ⊕ Unit) → MvPolynomial (Fin n ⊕ Unit) ((L × ℝ) → ℝ)
  | .inl j => dynkinCoordinatePolynomial b P.coefficients
      ![(fun i => MvPolynomial.X (.inl i)), semidirectFlowCoordinatePolynomial b D k] j
  | .inr _ => MvPolynomial.X (.inr ()) + MvPolynomial.C (fun g => g.2)

theorem semidirectProductCoordinatePolynomial_eval {k : ℕ} (hk : D.toLinearMap ^ k = 0) :
    ∀ (g : L × ℝ) (i : Fin n ⊕ Unit) (x : L × ℝ),
      semidirectCoordinate b i ((derivationSemidirectGroup D hD).mul x g) =
        coordinatePolynomialEvaluation (semidirectCoordinate b)
          (semidirectProductCoordinatePolynomial b D k i) g x  := by
  intro g i x
  rw [derivationSemidirect_mul]
  cases i with
  | inl j =>
    change b.repr (x.1 * nilpotentDerivationFlow D hD x.2 g.1) j = _
    rw [P.mul_eq]
    symm
    apply eval_dynkinCoordinatePolynomial b P.coefficients _
      (Pi.evalAlgHom ℝ (fun _ : L × ℝ => ℝ) g) _ ![x.1, nilpotentDerivationFlow D hD x.2 g.1]
    intro i j
    fin_cases i
    · simp [semidirectCoordinate]
    · exact semidirectFlowCoordinatePolynomial_eval b D hD hk x g j
  | inr j => simp [semidirectCoordinate, coordinatePolynomialEvaluation, semidirectProductCoordinatePolynomial]

include hD in
theorem finiteDimensional_semidirectCoordinateOrbit :
    letI := derivationSemidirectGroup D hD
    FiniteDimensional ℝ (coordinateOrbitSpan (semidirectCoordinate b))  := by
  let := derivationSemidirectGroup D hD
  let k := nilpotencyClass D.toLinearMap
  have hk : D.toLinearMap ^ k = 0 := pow_nilpotencyClass hD
  exact finiteDimensional_coordinateOrbitSpan_of_polynomial (semidirectCoordinate b)
    (semidirectProductCoordinatePolynomial b D k)
    (fun g i x => semidirectProductCoordinatePolynomial_eval b D hD hk g i x)

end PolycyclicRecognition

end

end OAI

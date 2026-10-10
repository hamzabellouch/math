import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialDerivationCoordinates
import OAI.GroupTheory.PolycyclicRecognition.Geometry.SemidirectCoordinateOrbit
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialBilinearWords

namespace OAI

/-! # Multivariate polynomial multiplication in the derivation extension -/

noncomputable section
namespace PolycyclicRecognition
variable {I L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] {n : ℕ}
  (b : Module.Basis (Fin n) ℝ L)

def semidirectCoordinateLinear : (L × ℝ) →ₗ[ℝ] ((Fin n ⊕ Unit) → ℝ) where
  toFun p i := semidirectCoordinate b i p
  map_add' p q := by
    funext i
    cases i with
    | inl i => exact congrFun (map_add b.equivFun p.1 q.1) i
    | inr i => rfl
  map_smul' r p := by
    funext i
    cases i with
    | inl i => exact congrFun (map_smul b.equivFun r p.1) i
    | inr i => rfl

def HasPolynomialSemidirectCoordinates (F : (I → ℝ) → L × ℝ) : Prop :=
  IsCoordinatePolynomial (fun x i => semidirectCoordinate b i (F x))

omit [FiniteDimensional ℝ L] P in
theorem polynomialSemidirectCoordinates_basis {d : ℕ}
    (c : Module.Basis (Fin d) ℝ (L × ℝ)) :
    HasPolynomialSemidirectCoordinates b (fun x => c.equivFun.symm x) :=
  IsCoordinatePolynomial.linear_pi
    ((semidirectCoordinateLinear b).comp c.equivFun.symm.toLinearMap)

omit [FiniteDimensional ℝ L] P in
theorem polynomialSemidirectCoordinates_const (v : L × ℝ) :
    HasPolynomialSemidirectCoordinates (I := I) b (fun _ => v) :=
  IsCoordinatePolynomial.const (semidirectCoordinateLinear b v)

theorem polynomialSemidirectCoordinates_mul
    (D : LieDerivation ℝ L L) (hD : IsNilpotent D.toLinearMap)
    (F H : (I → ℝ) → L × ℝ)
    (hF : HasPolynomialSemidirectCoordinates b F)
    (hH : HasPolynomialSemidirectCoordinates b H) :
    HasPolynomialSemidirectCoordinates b
      (fun x => (derivationSemidirectGroup D hD).mul (F x) (H x)) := by
  have hFl : IsCoordinatePolynomial (fun x => b.equivFun (F x).1) :=
    (IsCoordinatePolynomial.reindex (Sum.inl : Fin n → Fin n ⊕ Unit)).comp hF
  have hHl : IsCoordinatePolynomial (fun x => b.equivFun (H x).1) :=
    (IsCoordinatePolynomial.reindex (Sum.inl : Fin n → Fin n ⊕ Unit)).comp hH
  have hFr := coordinatePolynomial_iff_components.mp hF (.inr ())
  have hHr := coordinatePolynomial_iff_components.mp hH (.inr ())
  have hflow := coordinatePolynomial_derivationFlow b D hD
    (fun x => (F x).2) (fun x => (H x).1) hFr hHl
  have hprod := (coordinatePolynomial_dynkinProduct P.coefficients (basisBracket b)).comp
    (hFl.pair hflow)
  apply coordinatePolynomial_iff_components.mpr
  intro i
  cases i with
  | inl i =>
    have hp := coordinatePolynomial_iff_components.mp hprod i
    have hp' : (fun x => b.equivFun
        ((F x).1 * nilpotentDerivationFlow D hD (F x).2 (H x).1) i) ∈
        multivariatePolynomialFunctions I := by
      simpa only [Function.comp_def, Sum.elim_inl, Sum.elim_inr,
        basis_dynkinProduct, ← P.mul_eq] using hp
    simpa only [derivationSemidirect_mul, semidirectCoordinate,
      Module.Basis.equivFun_apply] using hp'
  | inr i => exact (multivariatePolynomialFunctions I).add_mem hFr hHr

end PolycyclicRecognition

end

end OAI

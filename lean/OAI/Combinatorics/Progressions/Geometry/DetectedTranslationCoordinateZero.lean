import OAI.Combinatorics.Progressions.Polynomial.DetectedTranslationPhaseDegree

namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial _root_.OAI.MvPolynomial Module RationalFilteredNilmanifold

variable {B L : Type} {U : Type*} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)

@[simp] theorem detectedTranslationBaseCoordinatePolynomial_constantCoeff
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (i : B) :
    constantCoeff (detectedTranslationBaseCoordinatePolynomial w d hw hwd M hM D E i) = 0 := by
  rw [detectedTranslationBaseCoordinatePolynomial_eq_logCoordinate]
  exact detectedTranslationLogCoordinate_constant w d hw hwd M hM D E (Sum.inl i)

@[simp] theorem detectedTranslationGroupEval_zero
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1)) :
    detectedTranslationGroupEval w d hw hwd M hM D (0 : U → ℝ) E = 1 := by
  let g := detectedTranslationSymbolLift w d hw hwd M hM D E
  have hlog : VectorPolynomial.coefficients g.log 0 = 0 := by
    dsimp only [g]
    rw [detectedTranslationSymbolLift_log]
    exact (weightedFiltration w d hwd).realSymbolRepresentative_constant
      (weightedBasis w d hw) (weightedBasisGrade w d)
      (weightedFiltration_layer_eq_span w d hw hwd) _ _
  have hval : (weightedFiltration w d hwd).realification.polynomialOrbitRealEval
      (fun _ : U => 1) (0 : U → ℝ) g = 1 := by
    apply NilpotentLieBCHGroup.ext
    change VectorPolynomial.eval₂ (0 : U → ℝ) g.log = 0
    have h := VectorPolynomial.eval₂_algebraMap (S := ℝ) (0 : U → ℚ) g.log
    simp only [Pi.zero_apply, map_zero] at h
    change VectorPolynomial.eval₂ (fun _ : U => (0 : ℝ)) g.log = 0
    rw [h]
    change VectorPolynomial.eval (fun _ : U => (0 : ℚ)) g.log = 0
    rw [VectorPolynomial.eval_zero_eq_coefficient, hlog]
  change bchRealTranslationHom w d hwd
    ((weightedFiltration w d hwd).realification.polynomialOrbitRealEval
      (fun _ : U => 1) (0 : U → ℝ) g) = 1
  rw [hval, map_one]

@[simp] theorem detectedTranslationPhasePolynomial_specialize_zero
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1)) :
    aeval (Sum.elim (fun _ : U => (0 : MvPolynomial B ℝ)) X)
      (detectedTranslationPhasePolynomial w d hw hwd M hM D E) = 0 := by
  have h := detectedTranslationPhasePolynomial_specialize w d hw hwd M hM D E (0 : U → ℝ)
  simpa only [Pi.zero_apply, map_zero, detectedTranslationGroupEval_zero,
    PolynomialTranslationGroupOver.polynomial_one] using h

@[simp] theorem detectedTranslationPhasePolynomial_eval_zero
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (a : B → ℝ) :
    eval (Sum.elim (0 : U → ℝ) a)
      (detectedTranslationPhasePolynomial w d hw hwd M hM D E) = 0 := by
  rw [detectedTranslationPhasePolynomial_eval, detectedTranslationGroupEval_zero,
    PolynomialTranslationGroupOver.polynomial_one, map_zero]

@[simp] theorem detectedTranslationPhasePolynomial_coeff_zero_parameters
    (E : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (β : B →₀ ℕ) :
    (detectedTranslationPhasePolynomial w d hw hwd M hM D E).coeff
      ((0 : U →₀ ℕ).sumElim β) = 0 := by
  rw [detectedTranslationPhasePolynomial_coeff]
  have h := congrArg (fun group : PolynomialTranslationGroupOver ℝ B => group.polynomial.coeff β)
    (detectedTranslationGroupPolynomial_specialize w d hw hwd M hM D E (0 : U → ℝ))
  simpa only [PolynomialTranslationGroupOver.map_polynomial, coeff_map,
    detectedTranslationGroupEval_zero, PolynomialTranslationGroupOver.polynomial_one,
    AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, eval_zero, constantCoeff_eq] using h

end Erdos3.PolynomialTranslationLie

end

end OAI

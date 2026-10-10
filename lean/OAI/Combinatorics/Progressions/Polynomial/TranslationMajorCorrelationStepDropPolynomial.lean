import OAI.Combinatorics.Progressions.Estimates.TranslationMajorTwistedCorrelationStepDrop
import OAI.Combinatorics.Progressions.Lattices.MajorTranslationIntegerEvaluation

namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open MvPolynomial Module RationalFilteredNilmanifold
open scoped TensorProduct BigOperators NNReal

theorem exists_majorPolynomial_correlation_step_drop (d : ℕ) (hd : 1 ≤ d) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {U L : Type} [Fintype U] [DecidableEq U]
      [LieRing L] [LieAlgebra ℚ L] {m t e : ℕ}
      (w : Fin m → ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
      [Fintype (WeightedBasisIndex w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L t e) (htd : t < d)
      (Ψ : PatchKernel m) (F : MvPolynomial (U ⊕ Fin m) ℝ)
      (hF : F ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
      (A : Fin m → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
      (M : ℝ≥0) (_hM : realPolynomialMass F ≤ M)
      (R : D.Niltest (fun _ : U => 1)) (p : ℝ), 0 ≤ p →
      (weightedTranslationNilmanifold w d hw hwd).GeometryComplexityLE p →
      Real.log (3 + (2 * bufferedTranslationTermLip w d Ψ M : ℝ≥0)) ≤ p →
      R.ComplexityLE p → (R.normBound : ℝ) ≤ 1 →
      ∀ (origin : U → ℤ) (lengths : U → ℕ), (∀ i, 0 < lengths i) →
      (Fintype.card U : ℝ) ≤ p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
      Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths,
        bufferedTranslationPhase Ψ (specializeMajorParameters (RingHom.id ℝ) F 0)
          (algebraicMajorSymbol F (specializeMajorParameters (RingHom.id ℝ) F 0)
            A (fun i => (x i : ℝ))) * R.eval x‖ →
      let N := pi (pairModels (weightedTranslationNilmanifold w d hw hwd) (D.raiseStep htd.le))
      ∃ (η : weightedSubalgebra w d →ₗ[ℚ] ℚ)
        (b : Basis (Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L)))
          ℚ (PairAlgebra (weightedSubalgebra w d) L))
        (ω : Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L)) → ℕ)
        (hLayers : ∀ j, N.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})),
        η (centralRationalElement w d (by omega) 1) = 1 ∧
        (∀ i, rationalLogHeight (η ((weightedTranslationNilmanifold w d hw hwd).basis i)) ≤
          (p + C) ^ C) ∧
        (∀ i j, rationalLogHeight (N.basis.repr (b i) j) ≤ (p + C) ^ C) ∧
        N.filtration.ControlledSymbolFactorization b ω hLayers
          (pairFrequency η (0 : L →ₗ[ℚ] ℚ)) (fun i => (lengths i : ℝ))
          (pairOrbitSymbol (weightedTranslationNilmanifold w d hw hwd) (D.raiseStep htd.le)
            (majorTranslationPolynomialOrbit w d hw hwd F hF A hA)
            (D.raiseStepRealOrbit htd.le R.orbit) b ω hLayers) ((p + C) ^ C) := by
  obtain ⟨C, hC, hstep⟩ := exists_translation_major_correlation_step_drop d hd
  refine ⟨C, hC, ?_⟩
  intro U L _ _ _ _ m t e w hw hwd _ _ _ _ _ _ _ _ _ D htd Ψ F hF A hA M hM
    R p hp hgeometry hbound hR hRcap origin lengths hlengths hU hlarge hcorr
  apply hstep w hw hwd D htd Ψ (specializeMajorParameters (RingHom.id ℝ) F 0) M
    (majorZeroParameterSlice_degree w hw hF) ((majorZeroParameterSlice_mass F).trans hM)
    (majorTranslationPolynomialOrbit w d hw hwd F hF A hA)
    R p hp hgeometry hbound hR hRcap origin lengths hlengths hU hlarge
  simpa only [majorTranslationPolynomialOrbit_integerEval] using hcorr

end Erdos3.PolynomialTranslationLie

end

end OAI

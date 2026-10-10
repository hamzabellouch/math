import OAI.Combinatorics.Progressions.Polynomial.TranslationMajorTwistedCorrelationStepDropPolynomial

namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial _root_.OAI.MvPolynomial Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct BigOperators NNReal

theorem exists_reduced_majorPolynomial_twisted_correlation_potential
    (d : ℕ) (hd : 0 < d) :
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
      (M : ℕ) (hM : 0 < M)
      (D : RationalFilteredNilmanifold L t e) (htd : t < d)
      (Ψ : PatchKernel m) (F : MvPolynomial (U ⊕ Fin m) ℝ)
      (hF : F.IsWeightedHomogeneous (Sum.elim (fun _ : U => 1) w) d)
      (A : Fin m → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
      (K : ℝ≥0) (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
      (_hT : ∀ x r, ‖T x r‖ ≤ 1) (_hLip : ∀ r, LipschitzWith K (fun x => T x r))
      (R : D.Niltest (fun _ : U => 1)) (p : ℝ), 0 ≤ p →
      (weightedTranslationResidueNilmanifold w d hw hwd M hM).GeometryComplexityLE p →
      Real.log (3 + (2 * twistedBufferedTranslationTermLip w d Ψ
        (((Fintype.card U + m + 1 : ℕ) : ℝ≥0) ^ d) K : ℝ≥0)) ≤ p →
      R.ComplexityLE p → (R.normBound : ℝ) ≤ 1 →
      ∀ (origin : U → ℤ) (lengths : U → ℕ), (∀ i, 0 < lengths i) →
      (Fintype.card U : ℝ) ≤ p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
      ∀ (β : (U → ℤ) → Fin m → ℤ),
      (∀ x ∈ translatedIntegerBox origin lengths, ∀ i,
        |eval (fun j => (x j : ℝ)) (A i) - (β x i : ℝ)| ≤ 1 / 2) →
      Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths,
        T (fun i => eval (fun j => (x j : ℝ)) (A i) - (β x i : ℝ))
            (fun i => (β x i : ZMod M)) *
          (Ψ.value (fun i => eval (fun j => (x j : ℝ)) (A i) - (β x i : ℝ)) : ℂ) *
          (Real.fourierChar (eval (fun j => ((Sum.elim x (β x) j : ℤ) : ℝ)) F) : ℂ) *
          R.eval x‖ →
      let N := pi (pairModels
        (weightedTranslationResidueNilmanifold w d hw hwd M hM) (D.raiseStep htd.le))
      let orbit := majorTranslationPolynomialOrbit w d hw hwd (fractionalCoefficientPolynomial F)
        (fractionalMajor_mem_weightedSupportLE w F hF) A hA
      let partner := D.raiseStepRealOrbit htd.le R.orbit
      ∃ (b : Basis (Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L)))
          ℚ (PairAlgebra (weightedSubalgebra w d) L))
        (ω : Fin (finrank ℚ (PairAlgebra (weightedSubalgebra w d) L)) → ℕ)
        (hLayers : ∀ j, N.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})),
        (∀ i j, rationalLogHeight (N.basis.repr (b i) j) ≤ (p + C)^C) ∧
      ∃ (l : ℕ) (E P S : N.filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
        (Vfast : LieSubalgebra ℚ (weightedSubalgebra w d)) (V : MvPolynomial (Fin m) ℚ) (q : ℕ),
        0 < l ∧ (l : ℝ) ≤ Real.exp ((p + C)^C) ∧
        E * P * S = pairOrbitSymbol (weightedTranslationResidueNilmanifold w d hw hwd M hM)
          (D.raiseStep htd.le) orbit partner b ω hLayers ∧
        N.filtration.SymbolSlowBound b ω hLayers (fun _ => 1)
          (fun i => (lengths i : ℝ)) (Real.exp ((p + C)^C)) E ∧
        N.filtration.SymbolRationalGrid b ω hLayers (fun _ => 1) l S ∧
        (∀ t : U → ℝ,
          eval₂ t ((weightedFiltration w d hwd).realSymbolRepresentative
            (weightedBasis w d hw) (weightedBasisGrade w d)
            (weightedFiltration_layer_eq_span w d hw hwd) (fun _ : U => 1)
            (realificationLieHom (N.filtration.filteredPolynomialSymbolMap
              (weightedFiltration w d hwd) (liePiEval (R := ℚ) true)
              (pairFirstProjection_filtered
                (weightedTranslationResidueNilmanifold w d hw hwd M hM) (D.raiseStep htd.le))
              (fun _ : U => 1)) P.coord)) ∈ realificationLieSubalgebra Vfast) ∧
        V.IsWeightedHomogeneous w d ∧
        (∀ x ∈ Vfast, ∀ z ∈ Vfast.toSubmodule.map
            (baseLinear.comp (weightedSubalgebra w d).subtype),
          eval z (scalarDirectionalDerivative x.val.base V) = eval z x.val.polynomial) ∧
        0 < q ∧ (q : ℝ) ≤ Real.exp ((p + C)^C) ∧
        (fun α => V.coeff α) ∈ denominatorGrid q ∧
        realPolynomialMass (MvPolynomial.map (algebraMap ℚ ℝ) V) ≤ Real.exp ((p + C)^C) ∧
        ∀ α, ((V.coeff α).num.natAbs : ℝ) ≤ Real.exp ((p + C)^C) ∧
          ((V.coeff α).den : ℝ) ≤ Real.exp ((p + C)^C) := by
  obtain ⟨C, hC, hdegree⟩ := exists_reduced_majorPolynomial_degree_twisted_correlation_potential d hd
  refine ⟨C, hC, ?_⟩
  intro U L _ _ _ _ m t e w hw hwd _ _ _ _ _ _ _ _ _ M hM D htd Ψ F hF A hA
    K T hT hLip R p hp hgeometry hbound hR hRcap origin lengths hlengths hU hlarge β hβ hcorr
  have hFle : F ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d :=
    fun _ hα => (hF (mem_support_iff.mp hα)).le
  convert hdegree w hw hwd M hM D htd Ψ F hFle A hA K T hT hLip R p hp
    hgeometry hbound hR hRcap origin lengths hlengths hU hlarge β hβ hcorr using 1

end Erdos3.PolynomialTranslationLie

end

end OAI

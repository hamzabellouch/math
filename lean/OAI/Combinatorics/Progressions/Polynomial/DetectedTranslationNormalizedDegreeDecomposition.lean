import OAI.Combinatorics.Progressions.Estimates.TranslationMajorCorrelationDecomposition

namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial _root_.OAI.MvPolynomial Module RationalFilteredNilmanifold

variable {B L : Type} {U ι : Type*} [Fintype B] [LieRing L] [LieAlgebra ℚ L]
    (w : B → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)
    {e : ℕ} (D : RationalFilteredNilmanifold L d e)
    (b : Basis ι ℚ (PairAlgebra (weightedSubalgebra w d) L)) (ω : ι → ℕ)
    (hN : ∀ j, (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem exists_detectedTranslation_normalized_degree_decomposition
    (hd : 0 < d)
    (F : MvPolynomial (U ⊕ B) ℝ)
    (hF : F ∈ weightedSupportLE (Sum.elim (fun _ : U => 1) w) d)
    (A : B → MvPolynomial U ℝ) (hA : ∀ i, (A i).totalDegree ≤ w i)
    (partner : D.filtration.realification.PolynomialOrbit (fun _ : U => 1))
    (E P Q : (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.RealPolynomialSymbolGroup (fun _ : U => 1))
    (hprod : E * P * Q = pairOrbitSymbol
      (weightedTranslationResidueNilmanifold w d hw hwd M hM) D
      (majorTranslationPolynomialOrbit w d hw hwd F hF A hA) partner b ω hN)
    (W : LieSubalgebra ℚ (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.AssociatedGraded)
    (hP : P.coord ∈ realificationLieSubalgebra
      ((pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration.symbolPointwiseSubalgebra b ω hN (fun _ : U => 1) W))
    (V : MvPolynomial B ℚ) (H : U → ℝ) (hH : ∀ i, H i ≠ 0)
    (q r : ℕ) (hq : 0 < q) (Cbase : ℝ) (hCbase : 0 ≤ Cbase)
    (hphaseGrid : realPolynomialCoefficientGrid q
      (detectedTranslationPhasePolynomial w d hw hwd M hM D Q))
    (hbaseGrid : ∀ i, realPolynomialCoefficientGrid q
      (detectedTranslationBaseCoordinatePolynomial w d hw hwd M hM D Q i))
    (hVgrid : (fun α => V.coeff α) ∈ denominatorGrid q)
    (hEdegree : (detectedTranslationNormalizedPhase w d hw hwd M hM D E H).totalDegree ≤ r)
    (hVdegree : V.totalDegree ≤ r)
    (hF₀degree : (specializeMajorParameters (RingHom.id ℝ)
      (weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d F) 0).totalDegree ≤ r)
    (heDegree : ∀ i,
      (detectedTranslationNormalizedBase w d hw hwd M hM D E H i).totalDegree ≤ r)
    (hQdegree : (detectedTranslationPhasePolynomial w d hw hwd M hM D Q).totalDegree ≤ r)
    (haDegree : ∀ i,
      (detectedTranslationBaseCoordinatePolynomial w d hw hwd M hM D Q i).totalDegree ≤ r)
    (heMass : ∀ i, realPolynomialMass
      (detectedTranslationNormalizedBase w d hw hwd M hM D E H i) ≤ Cbase) :
    let fast := W.map (weightedTranslationGradedProjection
      (pi (pairModels (weightedTranslationResidueNilmanifold w d hw hwd M hM) D)).filtration
        w d hw hwd (liePiEval (R := ℚ) true)
        (pairFirstProjection_filtered (weightedTranslationResidueNilmanifold w d hw hwd M hM) D))
    let K := (fast.toSubmodule.baseChange ℝ).map
      (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype))
    let Ftop := weightedHomogeneousComponent (Sum.elim (fun _ : U => 1) w) d F
    let F₀ := specializeMajorParameters (RingHom.id ℝ) Ftop 0
    (∀ x ∈ fast, ∀ z ∈ fast.toSubmodule.map
      (baseLinear.comp (weightedSubalgebra w d).subtype),
      eval z (scalarDirectionalDerivative x.val.base V) = eval z x.val.polynomial) →
    (∀ u, (detectedTranslationGroupEval w d hw hwd M hM D u Q).base ∈ K) →
    ∃ (S : MvPolynomial (U ⊕ B) ℝ) (R : MvPolynomial (U ⊕ B) ℚ),
      (∀ u z, z ∈ K → eval (Sum.elim u z) Ftop =
        eval (Sum.elim (fun i => u i / H i)
          (fun j => z j - eval u (majorTranslationTopCoordinates w A j))) S +
        eval₂ (algebraMap ℚ ℝ) (Sum.elim u z) R) ∧
      realPolynomialMass S ≤ realPolynomialMass F₀ +
        (realPolynomialMass (detectedTranslationNormalizedPhase w d hw hwd M hM D E H) +
          realPolynomialMass (map (algebraMap ℚ ℝ) V)) * (1 + Cbase)^r ∧
      (fun α => R.coeff α) ∈ denominatorGrid (q^(r+1)) ∧
      S.totalDegree ≤ (r+1)^2 ∧ R.totalDegree ≤ (r+1)^2 := by
  intro fast K Ftop F₀ hderiv hright
  obtain ⟨Qrat, a, _hQmap, hamap, hQgrid, hagrid, hQratDegree, hQeval⟩ :=
    exists_detectedTranslation_rational_right w d hw hwd M hM D Q q hq hphaseGrid hbaseGrid
  have hfactor (u : U → ℝ) : algebraicMajorSymbol Ftop F₀
      (majorTranslationTopCoordinates w A) u =
        normalizedMajorLeft (detectedTranslationNormalizedPhase w d hw hwd M hM D E H)
          (detectedTranslationNormalizedBase w d hw hwd M hM D E H) H u *
        detectedTranslationGroupEval w d hw hwd M hM D u P * rationalMajorRight Qrat a u := by
    rw [detectedTranslationGroupEval_normalized_left w d hw hwd M hM D E H hH,
      hQeval]
    exact detectedTranslationGroupEval_major_factorization w d hw hwd M hM D b ω hN
      F hF A hA partner E P Q hprod u
  have hpotential := detectedTranslationGroupEval_fast_potential w d hw hwd M hM D b ω hN
    hd W P hP V hderiv
  have haright (u : U → ℝ) : (fun j => eval₂ (algebraMap ℚ ℝ) u (a j)) ∈ K := by
    have heq := congrArg PolynomialTranslationGroupOver.base (hQeval u)
    change (fun i => eval₂ (algebraMap ℚ ℝ) u (a i)) = _ at heq
    rw [heq]
    exact hright u
  have hVrealDegree : (map (algebraMap ℚ ℝ) V).totalDegree ≤ r := by
    have hdeg : (map (algebraMap ℚ ℝ) V).totalDegree = V.totalDegree := by
      unfold totalDegree
      rw [support_map_of_injective V (algebraMap ℚ ℝ).injective]
    exact hdeg.trans_le hVdegree
  have haratDegree (i : B) : (a i).totalDegree ≤ r := by
    have hdeg : (map (algebraMap ℚ ℝ) (a i)).totalDegree = (a i).totalDegree := by
      unfold totalDegree
      rw [support_map_of_injective (a i) (algebraMap ℚ ℝ).injective]
    rw [hamap i] at hdeg
    exact hdeg ▸ haDegree i
  refine ⟨majorSlowPolynomial F₀
      (detectedTranslationNormalizedPhase w d hw hwd M hM D E H)
      (map (algebraMap ℚ ℝ) V)
      (detectedTranslationNormalizedBase w d hw hwd M hM D E H),
    majorRationalPolynomial Qrat V a, ?_, ?_, ?_, ?_, ?_⟩
  · exact algebraic_major_normalized_identity_on_subspace K Ftop F₀
      (majorTranslationTopCoordinates w A)
      (detectedTranslationNormalizedPhase w d hw hwd M hM D E H)
      (detectedTranslationNormalizedBase w d hw hwd M hM D E H) Qrat a V H
      (fun u => detectedTranslationGroupEval w d hw hwd M hM D u P)
      hfactor hpotential haright
  · exact algebraic_major_normalized_slow_mass F₀
      (detectedTranslationNormalizedPhase w d hw hwd M hM D E H) V
      (detectedTranslationNormalizedBase w d hw hwd M hM D E H)
      hCbase heMass hEdegree hVrealDegree
  · exact majorRationalPolynomial_denominatorGrid Qrat V a q r hVdegree hQgrid hVgrid hagrid
  · exact majorSlowPolynomial_totalDegree_le_square F₀
      (detectedTranslationNormalizedPhase w d hw hwd M hM D E H)
      (map (algebraMap ℚ ℝ) V)
      (detectedTranslationNormalizedBase w d hw hwd M hM D E H)
      hF₀degree hEdegree hVrealDegree heDegree
  · exact majorRationalPolynomial_totalDegree_le_square Qrat V a
      (hQratDegree.trans_le hQdegree) hVdegree haratDegree

end Erdos3.PolynomialTranslationLie

end

end OAI

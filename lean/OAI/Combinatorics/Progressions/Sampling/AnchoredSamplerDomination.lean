import OAI.Combinatorics.Progressions.Estimates.CappedNormalizedComparison
import OAI.Combinatorics.Progressions.Probability.BaseAndCenterMixedLaw

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open Module Submodule MeasureTheory VectorPolynomial
open scoped BigOperators NNReal

theorem exists_anchored_translated_selected_sampler_oneSite_domination (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {X G : Type*} [Fintype X] [DecidableEq X] [Fintype G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (R σ : Fin m → ℝ) (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (_hσ1 : ∀ j, σ j ≤ 1)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cinv j * ‖x‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ)+1) * R j ≤ 1/4)
    (L₀ : ℕ) {P δ : ℝ} (_hP : 0 ≤ P) (_hδ : 0 < δ) (_hδsmall : δ ≤ 1/6)
    (_hδP : δ⁻¹ ≤ Real.exp P) (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (_hL₀P : (L₀ : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (anchor : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (root : LayerSamplerVariables G I n B → ℤ) (_hroot : ∀ k, |(root k : ℝ)| ≤ Real.exp P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val+1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ) (_hs : ∀ k, 0 < stride k)
    {Rrank S ρ : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (_hρ : 0 < ρ) (_hρP : 1/ρ ≤ Real.exp P)
    (H : X → ℝ) (_hsize : ∀ k, Real.exp ((P+A)^A) ≤ H k)
    (_hrank : ∀ j, HasLayerSamplingRank (j.val+1) H Rrank (U j) (p j))
    (_hRrank : Real.exp ((P+A)^A) ≤ Rrank)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty)
    (W : Option (LayerSamplerVariables G I n B) × X → ℝ) (hW : ∀ z, 0 < W z)
    (_hwidth : ∀ z, ρ * H z.2 ≤ W z),
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T W z,
      ∀ center : CoefficientTorus (K := LayerSamplerVariables G I n B) U,
      let D := translatedSelectedPhysicalDensity (G := G) B U b hb o R σ hR hσ L₀ center p hm
      let Z := selectedResidueDensityMass stride T W (fun z => D (anchor + z))
      let M := ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (V j)
      ∃ hD : 0 < Z,
        |Z-1| ≤ 3*δ ∧ 1/2 ≤ Z ∧ Z ≤ 3/2 ∧
        ∀ φ : (X → ℝ) → ℝ, (∀ v, φ v ∈ Set.Icc (0 : ℝ) 1) →
          (∑' z, (translatedSelectedResidueDensityPMF anchor stride T W hW hZ D
            (translatedSelectedPhysicalDensity_nonneg (G := G) B U b hb o R σ hR hσ L₀ center p hm)
            hD z).toReal * φ (physicalAffineSite root z)) ≤
            M * (∑' z, (selectedResidueSmoothPMF stride T W hW hZ z).toReal *
              φ (physicalAffineSite root (anchor + z))) + 6*δ := by
  obtain ⟨A, hA, hlaw⟩ := exists_anchored_translated_selected_sampler_oneSite_law m
  refine ⟨A, hA, ?_⟩
  intro X G _ _ _ I _ n B _ J _ U b hb o _ _ _ _ μ _ _ ν _ _
    R σ hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall L₀ P δ hP hδ hδsmall hδP
    hX hK hI hn hJ hAP hL₀P hCP hVP hRP hσP anchor root hroot p hp hm stride hs Rrank S ρ
    hS hSP hstride hρ hρP H hsize hrank hRrank T hT W hW hwidth
  obtain ⟨hZ, hcenters⟩ := hlaw B U b hb o μ ν R σ hR hσ hσ1 C V hC hV
    Cinv hCinv hchart hsmall L₀ hP hδ hδsmall hδP hX hK hI hn hJ hAP hL₀P hCP hVP hRP hσP
    anchor root hroot p hp hm stride hs hS hSP hstride hρ hρP H hsize hrank hRrank T hT W hW hwidth
  refine ⟨hZ, ?_⟩
  intro center
  obtain ⟨hD, hclose, hlower, hupper, hcompare⟩ := hcenters center
  refine ⟨hD, hclose, hlower, hupper, ?_⟩
  intro φ hφ
  rw [translatedSelectedResidueDensityPMF_mean]
  simp_rw [translatedSelectedResidueDensityPMF_complex_mean] at hcompare
  have hφn (v : X → ℝ) : ‖(φ v : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hφ v).1]
    exact (hφ v).2
  have hcap (y : CoefficientTorus (K := Empty) U) :
      coefficientFiberAverage U μ root
        (fun x => VectorPolynomial.selectedCoefficientDensity (G := G) B U b hb o R σ hR hσ L₀ (center+x)) y ≤
          ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (V j) := by
    rw [coefficientFiberAverage_translate]
    exact (selectedCoefficientDensity_fiber_cap (G := G) B U b hb o hR hσ
      (fun j => (V j : ℝ)) (fun j => (V j).coe_nonneg) (fun j => (hV j).2)
      μ ν hσ1 Cinv hCinv hchart hsmall L₀ root _).2.2
  exact selectedResidueDensityPMF_le_of_normalized_comparison stride T W hW hZ
    (fun z => translatedSelectedPhysicalDensity (G := G) B U b hb o R σ hR hσ L₀ center p hm (anchor + z))
    (fun z => coefficientFiberAverage U μ root
      (fun x => VectorPolynomial.selectedCoefficientDensity (G := G) B U b hb o R σ hR hσ L₀ (center+x))
      (coefficientEvaluationTorus U root (affineSampleCoefficientTorus U p hm (fun k j => ((anchor + z) (k,j) : ℝ)))))
    (fun z => φ (physicalAffineSite root (anchor + z)))
    (fun z => translatedSelectedPhysicalDensity_nonneg (G := G) B U b hb o R σ hR hσ L₀ center p hm (anchor + z))
    hD (fun z => hcap _) (fun z => (hφ _).1) (hcompare (fun v => (φ v : ℂ)) hφn)

end Erdos3.BooleanCubeKernel

end

end OAI

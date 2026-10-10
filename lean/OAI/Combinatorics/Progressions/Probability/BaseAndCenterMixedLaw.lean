import OAI.Combinatorics.Progressions.Estimates.AnchoredSelectedOneSiteComparison
import OAI.Combinatorics.Progressions.Estimates.AnchoredTranslatedNormalization
import OAI.Combinatorics.Progressions.Estimates.AnchoredTrimmedReference

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open Module Submodule MeasureTheory VectorPolynomial
open scoped BigOperators NNReal

theorem exists_anchored_translated_selected_sampler_oneSite_law (m : ℕ) :
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
    let sample := fun z : Option (LayerSamplerVariables G I n B) × X → ℤ =>
      affineSampleCoefficientTorus U p hm (fun k j => ((anchor + z) (k,j) : ℝ))
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T W z,
      ∀ center : CoefficientTorus (K := LayerSamplerVariables G I n B) U,
      let D := translatedSelectedPhysicalDensity (G := G) B U b hb o R σ hR hσ L₀ center p hm
      let Z := selectedResidueDensityMass stride T W (fun z => D (anchor + z))
      let fiber := fun z => coefficientFiberAverage U μ root
        (fun x => VectorPolynomial.selectedCoefficientDensity (G := G) B U b hb o R σ hR hσ L₀ (center+x))
        (coefficientEvaluationTorus U root (sample z))
      ∃ hD : 0 < Z,
        |Z-1| ≤ 3*δ ∧ 1/2 ≤ Z ∧ Z ≤ 3/2 ∧
        ∀ φ : (X → ℝ) → ℂ, (∀ v, ‖φ v‖ ≤ 1) →
          ‖(∑' z, ((translatedSelectedResidueDensityPMF anchor stride T W hW hZ D
            (translatedSelectedPhysicalDensity_nonneg (G := G) B U b hb o R σ hR hσ L₀ center p hm)
            hD z).toReal : ℂ) * φ (physicalAffineSite root z)) -
            (∑' z, ((selectedResidueSmoothPMF stride T W hW hZ z).toReal : ℂ) *
              (φ (physicalAffineSite root (anchor + z)) * (fiber z : ℂ)))‖ ≤ 6*δ := by
  obtain ⟨A₀, hA₀, hnormal⟩ := exists_anchored_translated_selected_sampler_normalization m
  obtain ⟨A₁, _, hcomparison⟩ := exists_anchored_translated_selected_sampler_oneSite_comparison m
  let A := max A₀ A₁
  have hA : 2 ≤ A := hA₀.trans (le_max_left _ _)
  refine ⟨A, hA, ?_⟩
  intro X G _ _ _ I _ n B _ J _ U b hb o _ _ _ _ μ _ _ ν _ _
    R σ hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall L₀ P δ hP hδ hδsmall hδP
    hX hK hI hn hJ hAP hL₀P hCP hVP hRP hσP anchor root hroot p hp hm stride hs Rrank S ρ
    hS hSP hstride hρ hρP H hsize hrank hRrank T hT W hW hwidth
  have hthreshold (a : ℕ) (ha : a ≤ A) : Real.exp ((P+a)^a) ≤ Real.exp ((P+A)^A) := by
    apply Real.exp_le_exp.mpr
    have haa : (a : ℝ) ≤ A := by exact_mod_cast ha
    have hAr : (2 : ℝ) ≤ A := by exact_mod_cast hA
    exact (pow_le_pow_left₀ (by positivity) (by linarith : P+(a:ℝ) ≤ P+A) a).trans
      (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ P+A) ha)
  have h₀ := hthreshold A₀ (le_max_left _ _)
  have h₁ := hthreshold A₁ (le_max_right _ _)
  obtain ⟨hZ, hcenters⟩ := hnormal B U b hb o μ ν R σ hR hσ hσ1 C V hC hV
    Cinv hCinv hchart hsmall L₀ hP hδ hδsmall hδP hX hK hI hn hJ hAP hL₀P hCP hVP hRP hσP
    anchor p hp hm stride hs hS hSP hstride hρ hρP H (fun i => h₀.trans (hsize i)) hrank
    (h₀.trans hRrank) T hT W hW hwidth
  refine ⟨hZ, ?_⟩
  intro center
  obtain ⟨hD, hclose, hlower, hupper, _⟩ := hcenters center
  refine ⟨hD, hclose, hlower, hupper, ?_⟩
  intro φ hφ
  rw [translatedSelectedResidueDensityPMF_complex_mean]
  obtain ⟨_, he⟩ := hcomparison B U b hb o μ R σ hR hσ hσ1 C V hC hV
    Cinv hCinv hchart hsmall L₀ hP hδ hδP hX hK hI hn hJ hAP hL₀P hCP hVP hRP hσP
    anchor root hroot p hp hm stride hs hS hSP hstride hρ hρP H (fun i => h₁.trans (hsize i)) hrank
    (h₁.trans hRrank) T hT W hW hwidth center φ hφ
  have h := selectedResidueDensityPMF_error_of_bounded_test stride T W hW hZ
    (fun z => translatedSelectedPhysicalDensity B U b hb o R σ hR hσ L₀ center p hm (anchor + z))
    (fun z => translatedSelectedPhysicalDensity_nonneg B U b hb o R σ hR hσ L₀ center p hm (anchor + z)) hD
    (fun z => φ (physicalAffineSite root (anchor + z))) (fun z => hφ _) he hclose
  exact h.trans_eq (by ring)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open Module Submodule MeasureTheory VectorPolynomial
open scoped BigOperators NNReal

theorem exists_anchored_mixed_center_selected_sampler_oneSite_law (m : ℕ) :
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
    let D := fun center => translatedSelectedPhysicalDensity (G := G) B U b hb o R σ hR hσ L₀
      (coefficientConstantCenter U center) p hm
    let Z := fun center => selectedResidueDensityMass stride T W (fun z => D center (anchor + z))
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T W z,
    ∃ hD : ∀ center, 0 < Z center,
      (∀ center, |Z center-1| ≤ 3*δ ∧ 1/2 ≤ Z center ∧ Z center ≤ 3/2) ∧
      ∀ φ : (X → ℝ) → ℂ, (∀ v, ‖φ v‖ ≤ 1) →
        ‖(∫ center, ∑' z, ((translatedSelectedResidueDensityPMF anchor stride T W hW hZ (D center)
          (translatedSelectedPhysicalDensity_nonneg (G := G) B U b hb o R σ hR hσ L₀
            (coefficientConstantCenter U center) p hm) (hD center) z).toReal : ℂ) *
            φ (physicalAffineSite root z) ∂μ) -
          (∑' z, ((selectedResidueSmoothPMF stride T W hW hZ z).toReal : ℂ) *
            φ (physicalAffineSite root (anchor + z)))‖ ≤ 6*δ := by
  obtain ⟨A, hA, hlaw⟩ := exists_anchored_translated_selected_sampler_oneSite_law m
  refine ⟨A, hA, ?_⟩
  intro X G _ _ _ I _ n B _ J _ U b hb o _ _ _ _ μ _ _ ν _ _
    R σ hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall L₀ P δ hP hδ hδsmall hδP
    hX hK hI hn hJ hAP hL₀P hCP hVP hRP hσP anchor root hroot p hp hm stride hs Rrank S ρ
    hS hSP hstride hρ hρP H hsize hrank hRrank T hT W hW hwidth
  obtain ⟨hZ, hcenters⟩ := hlaw B U b hb o μ ν R σ hR hσ hσ1 C V hC hV
    Cinv hCinv hchart hsmall L₀ hP hδ hδsmall hδP hX hK hI hn hJ hAP hL₀P hCP hVP hRP hσP
    anchor root hroot p hp hm stride hs hS hSP hstride hρ hρP H hsize hrank hRrank T hT W hW hwidth
  choose hD hrest using (fun center : CoefficientTorus (K := LayerSamplerVariables G I n B) U =>
    hcenters (coefficientConstantCenter U center))
  refine ⟨hZ, hD, ?_, ?_⟩
  · intro center
    exact ⟨(hrest center).1, (hrest center).2.1, (hrest center).2.2.1⟩
  · intro φ hφ
    simp_rw [translatedSelectedResidueDensityPMF_complex_mean]
    let D₀ := VectorPolynomial.selectedCoefficientDensity (G := G) B U b hb o R σ hR hσ L₀
    have hD₀ := selectedCoefficientDensity_measurable (G := G) B U b hb o R σ hR hσ L₀
    obtain ⟨M, hM⟩ := selectedCoefficientDensity_bounded (G := G) B U b hb o R σ hR hσ L₀
      C V hC hV hσ1 Cinv hCinv hchart hsmall
    have hbound (x) : ‖D₀ x‖ ≤ M := by
      rw [Real.norm_eq_abs, abs_of_nonneg (hM x).1]
      exact (hM x).2
    let scale := selectedLayerSamplerScale (G := G) B U b R σ hR hσ L₀
    have hspec := allocatedCoefficientDensity_spec B U b hb o hR hσ scale
      hσ1 Cinv hCinv hchart hsmall μ ν
    let D := fun center z => translatedSelectedPhysicalDensity (G := G) B U b hb o R σ hR hσ L₀
      (coefficientConstantCenter U center) p hm (anchor + z)
    let sample := fun z : Option (LayerSamplerVariables G I n B) × X → ℤ =>
      affineSampleCoefficientTorus U p hm (fun k j => ((anchor + z) (k,j) : ℝ))
    let F := fun center z => coefficientFiberAverage U μ root
      (fun x => D₀ (coefficientConstantCenter U center+x))
      (coefficientEvaluationTorus U root (sample z))
    apply selectedResidue_center_mixture_compare μ stride T W hW hZ D
      (fun z => (translatedSelectedPhysicalDensity_measurable_center B U b hb o R σ hR hσ L₀ p hm (anchor + z)).comp
        (coefficientConstantCenter_continuous U).measurable)
      (fun center z => translatedSelectedPhysicalDensity_nonneg B U b hb o R σ hR hσ L₀
        (coefficientConstantCenter U center) p hm (anchor + z)) hD F
      (fun z => coefficientMixedFiber_integrable U μ D₀ hD₀ hbound root _)
      (fun z => (coefficientMixedFiber_average U μ D₀ hD₀ hbound root _).trans hspec.2.2.2.1)
      (fun z => φ (physicalAffineSite root (anchor + z))) (fun z => hφ _)
    intro center
    have h := (hrest center).2.2.2 φ hφ
    simpa only [translatedSelectedResidueDensityPMF_complex_mean] using h

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open Module Submodule MeasureTheory VectorPolynomial
open scoped BigOperators NNReal

theorem exists_base_and_center_mixed_selected_sampler_law (m : ℕ) :
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
    (_hwidth : ∀ z, ρ * H z.2 ≤ W z)
    (N Rtrim : X → ℕ) (_htrim : ∀ i, 2 * Rtrim i < N i)
    (_hnoise : ∀ u ∈ rectangularWeightIndices 0 W 1, ∀ i,
      |integerPhysicalSite root (anchor + u) i| ≤ (Rtrim i : ℤ)),
    let D := fun center => translatedSelectedPhysicalDensity (G := G) B U b hb o R σ hR hσ L₀
      (coefficientConstantCenter U center) p hm
    let Z := fun base center => selectedResidueDensityMass stride T W
      (fun u => D center ((integerBaseTranslation base + anchor) + u))
    ∃ hZ : 0 < ∑' u, selectedResidueSmoothWeight stride T W u,
    ∃ hD : ∀ base center, 0 < Z base center,
      (∀ base center, |Z base center-1| ≤ 3*δ ∧ 1/2 ≤ Z base center ∧ Z base center ≤ 3/2) ∧
      ∀ φ : (X → ℝ) → ℂ, (∀ v, ‖φ v‖ ≤ 1) →
        ‖(𝔼 base ∈ trimmedIntegerBox N Rtrim,
          ∫ center, ∑' z, ((translatedSelectedResidueDensityPMF
            (integerBaseTranslation base + anchor) stride T W hW hZ (D center)
            (translatedSelectedPhysicalDensity_nonneg (G := G) B U b hb o R σ hR hσ L₀
              (coefficientConstantCenter U center) p hm) (hD base center) z).toReal : ℂ) *
              φ (physicalAffineSite root z) ∂μ) -
          𝔼 x ∈ integerBox N, φ (fun i => (x i : ℝ))‖ ≤
            6*δ + 2 * ∑ i, 2 * (Rtrim i : ℝ) / N i := by
  obtain ⟨A, hA, hlaw⟩ := exists_anchored_mixed_center_selected_sampler_oneSite_law m
  refine ⟨A, hA, ?_⟩
  intro X G _ _ _ I _ n B _ J _ U b hb o _ _ _ _ μ _ _ ν _ _
    R σ hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall L₀ P δ hP hδ hδsmall hδP
    hX hK hI hn hJ hAP hL₀P hCP hVP hRP hσP anchor root hroot p hp hm stride hs Rrank S ρ
    hS hSP hstride hρ hρP H hsize hrank hRrank T hT W hW hwidth N Rtrim htrim hnoise
  have hfamily (base : X → ℤ) := hlaw B U b hb o μ ν R σ hR hσ hσ1 C V hC hV
    Cinv hCinv hchart hsmall L₀ hP hδ hδsmall hδP hX hK hI hn hJ hAP hL₀P hCP hVP hRP hσP
    (integerBaseTranslation base + anchor) root hroot p hp hm stride hs hS hSP hstride hρ hρP
    H hsize hrank hRrank T hT W hW hwidth
  choose hZs hDs hrests using hfamily
  refine ⟨hZs 0, hDs, ?_, ?_⟩
  · intro base center
    exact (hrests base).1 center
  · intro φ hφ
    apply selectedResidue_anchored_trimmed_transfer root anchor N Rtrim htrim stride T W hW
      (hZs 0) hnoise φ hφ
    intro base _
    exact (hrests base).2 φ hφ

end Erdos3.BooleanCubeKernel

end

end OAI

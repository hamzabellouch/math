import OAI.Combinatorics.Progressions.Dynamics.SelectedParameterBudget
import OAI.Combinatorics.Progressions.Estimates.CanonicalEmptyLayerGeometry
import OAI.Combinatorics.Progressions.Geometry.ExplicitMixedUniformBox
import OAI.Combinatorics.Progressions.Geometry.FixedCenterBoxDomination
import OAI.Combinatorics.Progressions.Lattices.LayerSamplerIntegerBox

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open Module Submodule MeasureTheory VectorPolynomial
open scoped BigOperators NNReal

theorem exists_explicit_selected_sampler_marginals (m : ℕ) :
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
    (root : LayerSamplerVariables G I n B → ℤ) (_hroot : ∀ k, |(root k : ℝ)| ≤ Real.exp P)
    (τ : ℝ) (_hτ : 0 < τ) (_hτhalf : τ ≤ 1/2) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hτdim : (Fintype.card X : ℝ) * τ ≤ 1/2)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val+1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ) (_hs : ∀ k, 0 < stride k)
    {Rrank S : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (N : X → ℕ) (_hsize : ∀ k, Real.exp ((P+A)^A) ≤ (N k : ℝ))
    (_hrank : ∀ j, HasLayerSamplingRank (j.val+1) (fun i => (N i : ℝ)) Rrank (U j) (p j))
    (_hRrank : Real.exp ((P+A)^A) ≤ Rrank)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty),
    let W := trimmedSpatialWidths (K := LayerSamplerVariables G I n B) (Real.exp (2*P)) τ N
    let margin := spatialTrimMargin τ N
    let pa := fun (a : X → ℤ) j => translate (fun i => (a i : ℝ)) (p j)
    let hma := fun (a : X → ℤ) j => coefficients_translate_mem (U j) (fun i => (a i : ℝ)) (p j) (hm j)
    let D := fun a center => translatedSelectedPhysicalDensity (G := G) B U b hb o R σ hR hσ L₀
      (coefficientConstantCenter U center) (pa a) (hma a)
    let Z := fun a center => selectedResidueDensityMass stride T W (D a center)
    let M := ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (V j)
    ∃ hW : ∀ z, 0 < W z,
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T W z,
    ∃ hD : ∀ a center, 0 < Z a center,
      (∀ a center, |Z a center-1| ≤ 3*δ ∧ 1/2 ≤ Z a center ∧ Z a center ≤ 3/2) ∧
      (∀ center (φ : (X → ℝ) → ℝ), (∀ v, φ v ∈ Set.Icc (0 : ℝ) 1) →
        (𝔼 a ∈ trimmedIntegerBox N margin,
          ∑' z, (selectedResidueDensityPMF stride T W hW hZ (D a center)
            (translatedSelectedPhysicalDensity_nonneg (G := G) B U b hb o R σ hR hσ L₀
              (coefficientConstantCenter U center) (pa a) (hma a)) (hD a center) z).toReal *
              φ ((fun i => (a i : ℝ)) + physicalAffineSite root z)) ≤
            2*M*(𝔼 x ∈ integerBox N, φ (fun i => (x i : ℝ))) + 6*δ) ∧
      ∀ φ : (X → ℝ) → ℂ, (∀ v, ‖φ v‖ ≤ 1) →
        ‖(𝔼 a ∈ trimmedIntegerBox N margin,
          ∫ center, ∑' z, ((selectedResidueDensityPMF stride T W hW hZ (D a center)
            (translatedSelectedPhysicalDensity_nonneg (G := G) B U b hb o R σ hR hσ L₀
              (coefficientConstantCenter U center) (pa a) (hma a)) (hD a center) z).toReal : ℂ) *
              φ ((fun i => (a i : ℝ)) + physicalAffineSite root z) ∂μ) -
            (𝔼 x ∈ integerBox N, φ (fun i => (x i : ℝ)))‖ ≤
          6*δ + 2 * (Fintype.card X : ℝ) * τ := by
  obtain ⟨A₀, _, hmixed⟩ := exists_mixed_selected_sampler_uniform_box_law m
  obtain ⟨A₁, _, hfixed⟩ := exists_fixed_center_selected_sampler_box_domination m
  let A := 2*(max A₀ A₁)+256
  have hA : 256 ≤ A := by dsimp [A]; omega
  refine ⟨A, by omega, ?_⟩
  intro X G _ _ _ I _ n B _ J _ U b hb o _ _ _ _ μ _ _ ν _ _
    R σ hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall L₀ P δ hP hδ hδsmall hδP
    hX hK hI hn hJ hAP hL₀P hCP hVP hRP hσP root hroot τ hτ hτhalf hτP hτdim p hp hm
    stride hs Rrank S hS hSP hstride N hsize hrank hRrank T hT
  have hPQ := le_spatialSamplingBudget hP
  have he := Real.exp_le_exp.mpr hPQ
  have hthreshold (a : ℕ) (ha : a ≤ max A₀ A₁) :=
    spatial_threshold_dominates hP hA (show 2*a ≤ A by dsimp [A]; omega)
  have h₀ := hthreshold A₀ (le_max_left _ _)
  have h₁ := hthreshold A₁ (le_max_right _ _)
  have hN (i) : 0 < N i := by
    have := four_le_of_spatial_threshold hP hA (N i) (hsize i)
    omega
  have hmarginSize (i) : 4 ≤ τ * (N i : ℝ) :=
    spatialTrimMargin_size_of_exp_size hP hτ hτP
      ((spatial_threshold_large hP hA).trans (hsize i))
  let W := trimmedSpatialWidths (K := LayerSamplerVariables G I n B) (Real.exp (2*P)) τ N
  have hW : ∀ z, 0 < W z := trimmedSpatialWidths_pos (Real.exp_pos _).le hτ N hN
  have hrootSum := root_sum_le_spatial_budget hK root hroot
  have hloss : (∑ i, 2 * (spatialTrimMargin τ N i : ℝ) / N i) ≤ 1/2 := by
    have h := spatialTrimMargin_error_bound N hN hmarginSize
    linarith
  obtain ⟨hZ, hD, hclose, htest⟩ :=
    hmixed B U b hb o μ ν R σ hR hσ hσ1 C V hC hV
      Cinv hCinv hchart hsmall L₀ (hP.trans hPQ) hδ hδsmall (hδP.trans he)
      (hX.trans hPQ) (hK.trans hPQ)
      (fun j => (hI j).trans hPQ) (fun j => (hn j).trans hPQ) (fun j => (hJ j).trans hPQ)
      (hAP.trans he) (hL₀P.trans he) (fun j => (hCP j).trans he) (fun j => (hVP j).trans he)
      (fun j => (hRP j).trans he) (fun j => (hσP j).trans he)
      root (fun k => (hroot k).trans he) p hp hm stride hs hS (hSP.trans he) hstride
      (spatialWidthFraction_pos P hτ) (spatialWidthFraction_inv_le hP hτ hτP)
      (fun i => (N i : ℝ)) (fun i => h₀.trans (hsize i)) hrank (h₀.trans hRrank)
      T hT W hW (spatialWidthFraction_le_trimmed_width P hτ.le N)
      N (spatialTrimMargin τ N) (spatialTrimMargin_proper hτhalf N hN hmarginSize)
      (spatialTrimMargin_fits (Real.exp_pos _).le hτ.le root hrootSum N)
  obtain ⟨_, _, _, hdom⟩ :=
    hfixed B U b hb o μ ν R σ hR hσ hσ1 C V hC hV
      Cinv hCinv hchart hsmall L₀ (hP.trans hPQ) hδ hδsmall (hδP.trans he)
      (hX.trans hPQ) (hK.trans hPQ)
      (fun j => (hI j).trans hPQ) (fun j => (hn j).trans hPQ) (fun j => (hJ j).trans hPQ)
      (hAP.trans he) (hL₀P.trans he) (fun j => (hCP j).trans he) (fun j => (hVP j).trans he)
      (fun j => (hRP j).trans he) (fun j => (hσP j).trans he)
      root (fun k => (hroot k).trans he) p hp hm stride hs hS (hSP.trans he) hstride
      (spatialWidthFraction_pos P hτ) (spatialWidthFraction_inv_le hP hτ hτP)
      (fun i => (N i : ℝ)) (fun i => h₁.trans (hsize i)) hrank (h₁.trans hRrank)
      T hT W hW (spatialWidthFraction_le_trimmed_width P hτ.le N)
      N (spatialTrimMargin τ N) (spatialTrimMargin_proper hτhalf N hN hmarginSize)
      (spatialTrimMargin_fits (Real.exp_pos _).le hτ.le root hrootSum N) hloss
  refine ⟨hW, hZ, hD, hclose, ?_, ?_⟩
  · intro center φ hφ
    exact hdom (coefficientConstantCenter U center) φ hφ
  · intro φ hφ
    exact (htest φ hφ).trans (add_le_add (le_refl (6*δ))
      (spatialTrimMargin_error_bound N hN hmarginSize))

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open Module Submodule MeasureTheory VectorPolynomial
open scoped BigOperators NNReal

theorem exists_explicit_joint_sampler_marginals (m : ℕ) :
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
    (root : LayerSamplerVariables G I n B → ℤ) (_hroot : ∀ k, |(root k : ℝ)| ≤ Real.exp P)
    (τ : ℝ) (_hτ : 0 < τ) (_hτhalf : τ ≤ 1/2) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hτdim : (Fintype.card X : ℝ) * τ ≤ 1/2)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val+1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ) (_hs : ∀ k, 0 < stride k)
    {Rrank S : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (N : X → ℕ) (_hsize : ∀ k, Real.exp ((P+A)^A) ≤ (N k : ℝ))
    (_hrank : ∀ j, HasLayerSamplingRank (j.val+1) (fun i => (N i : ℝ)) Rrank (U j) (p j))
    (_hRrank : Real.exp ((P+A)^A) ≤ Rrank)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty),
    let W := trimmedSpatialWidths (K := LayerSamplerVariables G I n B) (Real.exp (2*P)) τ N
    let margin := spatialTrimMargin τ N
    let pa := fun (a : X → ℤ) j => translate (fun i => (a i : ℝ)) (p j)
    let hma := fun (a : X → ℤ) j => coefficients_translate_mem (U j) (fun i => (a i : ℝ)) (p j) (hm j)
    let D := fun a center => translatedSelectedPhysicalDensity (G := G) B U b hb o R σ hR hσ L₀
      (coefficientConstantCenter U center) (pa a) (hma a)
    let Q := trimmedIntegerBox N margin
    let Z := fun center => selectedJointDensityMass Q stride T W (fun a => D a center)
    let M := ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (V j)
    ∃ hQ : Q.Nonempty,
    ∃ hW : ∀ z, 0 < W z,
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T W z,
    ∃ hD : ∀ center, 0 < Z center,
      (∀ center, |Z center-1| ≤ 3*δ ∧ 1/2 ≤ Z center ∧ Z center ≤ 3/2) ∧
      (∀ center (φ : (X → ℝ) → ℝ), (∀ v, φ v ∈ Set.Icc (0 : ℝ) 1) →
        (selectedJointFiniteLaw Q hQ stride T W hW hZ (fun a => D a center)
          (fun a => translatedSelectedPhysicalDensity_nonneg (G := G) B U b hb o R σ hR hσ L₀
            (coefficientConstantCenter U center) (pa a) (hma a)) (hD center)).mean
          (fun z => φ ((fun i => (z.1.val i : ℝ)) + physicalAffineSite root z.2.val)) ≤
          2*M*(𝔼 x ∈ integerBox N, φ (fun i => (x i : ℝ))) + 12*δ) ∧
      ∀ φ : (X → ℝ) → ℂ, (∀ v, ‖φ v‖ ≤ 1) →
        ‖(∫ center,
          (selectedJointFiniteLaw Q hQ stride T W hW hZ (fun a => D a center)
            (fun a => translatedSelectedPhysicalDensity_nonneg (G := G) B U b hb o R σ hR hσ L₀
              (coefficientConstantCenter U center) (pa a) (hma a)) (hD center)).complexMean
            (fun z => φ ((fun i => (z.1.val i : ℝ)) + physicalAffineSite root z.2.val)) ∂μ) -
          (𝔼 x ∈ integerBox N, φ (fun i => (x i : ℝ)))‖ ≤
          12*δ + 2 * (Fintype.card X : ℝ) * τ := by
  obtain ⟨A₀, _, hlaw⟩ := exists_explicit_selected_sampler_marginals m
  let A := max A₀ 256
  have hA : 256 ≤ A := le_max_right _ _
  refine ⟨A, by omega, ?_⟩
  intro X G _ _ _ I _ n B _ J _ U b hb o _ _ _ _ μ _ _ ν _ _
    R σ hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall L₀ P δ hP hδ hδsmall hδP
    hX hK hI hn hJ hAP hL₀P hCP hVP hRP hσP root hroot τ hτ hτhalf hτP hτdim p hp hm
    stride hs Rrank S hS hSP hstride N hsize hrank hRrank T hT
  have hthreshold : Real.exp ((P+A₀)^A₀) ≤ Real.exp ((P+A)^A) := by
    have ha : A₀ ≤ A := le_max_left _ _
    have har : (A₀ : ℝ) ≤ A := by exact_mod_cast ha
    have hAr : (256 : ℝ) ≤ A := by exact_mod_cast hA
    apply Real.exp_le_exp.mpr
    exact (pow_le_pow_left₀ (by positivity) (by linarith : P+(A₀ : ℝ) ≤ P+A) A₀).trans
      (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ P+A) ha)
  obtain ⟨hW, hZ, hlocal, hclose, hdom, hmix⟩ :=
    hlaw B U b hb o μ ν R σ hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall L₀
      hP hδ hδsmall hδP hX hK hI hn hJ hAP hL₀P hCP hVP hRP hσP
      root hroot τ hτ hτhalf hτP hτdim p hp hm stride hs hS hSP hstride
      N (fun i => hthreshold.trans (hsize i)) hrank (hthreshold.trans hRrank) T hT
  let W := trimmedSpatialWidths (K := LayerSamplerVariables G I n B) (Real.exp (2*P)) τ N
  let Q := trimmedIntegerBox N (spatialTrimMargin τ N)
  let pa := fun (a : X → ℤ) j => translate (fun i => (a i : ℝ)) (p j)
  let hma := fun (a : X → ℤ) j => coefficients_translate_mem (U j) (fun i => (a i : ℝ)) (p j) (hm j)
  let D := fun a center => translatedSelectedPhysicalDensity (G := G) B U b hb o R σ hR hσ L₀
    (coefficientConstantCenter U center) (pa a) (hma a)
  have hN (i) : 0 < N i := by
    have := four_le_of_spatial_threshold hP hA (N i) (hsize i)
    omega
  have hmarginSize (i) : 4 ≤ τ * (N i : ℝ) :=
    spatialTrimMargin_size_of_exp_size hP hτ hτP
      ((spatial_threshold_large hP hA).trans (hsize i))
  have hQ : Q.Nonempty :=
    trimmedIntegerBox_nonempty N _ (spatialTrimMargin_proper hτhalf N hN hmarginSize)
  have hjbounds (center) : selectedJointDensityMass Q stride T W (fun a => D a center) ∈
      Set.Icc (1/2 : ℝ) (3/2) :=
    selectedJointDensityMass_bounds Q hQ stride T W _ (fun a => ⟨(hclose a center).2.1, (hclose a center).2.2⟩)
  have hglobal (center) : 0 < selectedJointDensityMass Q stride T W (fun a => D a center) :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1/2) (hjbounds center).1
  have hD0 (center) (a) := translatedSelectedPhysicalDensity_nonneg (G := G) B U b hb o R σ hR hσ L₀
    (coefficientConstantCenter U center) (pa a) (hma a)
  refine ⟨hQ, hW, hZ, hglobal, ?_, ?_, ?_⟩
  · intro center
    exact ⟨selectedJointDensityMass_close Q hQ stride T W _ (fun a => (hclose a center).1),
      (hjbounds center).1, (hjbounds center).2⟩
  · intro center φ hφ
    have h := selectedJointFiniteLaw_local_real_comparison Q hQ stride T W hW hZ
      (fun a => D a center) (hD0 center) (hglobal center) (fun a => hlocal a center)
      (fun a z => φ ((fun i => (a i : ℝ)) + physicalAffineSite root z))
      (fun a z => by rw [abs_of_nonneg (hφ _).1]; exact (hφ _).2)
      (fun a => (hclose a center).1)
    linarith only [(abs_le.mp h).2, hdom center φ hφ]
  · intro φ hφ
    have hmeas (a) (z) : Measurable (fun center => D a center z) :=
      (translatedSelectedPhysicalDensity_measurable_center B U b hb o R σ hR hσ L₀ (pa a) (hma a) z).comp
        (coefficientConstantCenter_continuous U).measurable
    have h := selectedJointFiniteLaw_integral_local_comparison Q hQ stride T W hW hZ μ
      (fun center a => D a center) hmeas hD0 hglobal (fun center a => hlocal a center)
      (fun a z => φ ((fun i => (a i : ℝ)) + physicalAffineSite root z)) (fun a z => hφ _)
      (fun center a => (hclose a center).1)
    exact ((norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add h (hmix φ hφ))).trans_eq (by ring)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open Module Submodule MeasureTheory VectorPolynomial
open scoped BigOperators NNReal Classical

theorem exists_explicit_joint_sampler_with_collisions (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {X G S₀ : Type*} [Fintype X] [DecidableEq X] [Nonempty X] [Fintype G]
    [Fintype S₀] [DecidableEq S₀]
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
    (site : S₀ → LayerSamplerVariables G I n B → ℤ) (_hsite : Function.Injective site)
    (_hsitebound : ∀ q k, |(site q k : ℝ)| ≤ Real.exp P)
    (τ : ℝ) (_hτ : 0 < τ) (_hτhalf : τ ≤ 1/2) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hτdim : (Fintype.card X : ℝ) * τ ≤ 1/2)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val+1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ) (_hs : ∀ k, 0 < stride k)
    {Rrank S : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (N : X → ℕ) (_hsize : ∀ k, Real.exp ((P+A)^A) ≤ (N k : ℝ))
    (_hrank : ∀ j, HasLayerSamplingRank (j.val+1) (fun i => (N i : ℝ)) Rrank (U j) (p j))
    (_hRrank : Real.exp ((P+A)^A) ≤ Rrank)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty),
    let W := trimmedSpatialWidths (K := LayerSamplerVariables G I n B) (Real.exp (2*P)) τ N
    let margin := spatialTrimMargin τ N
    let pa := fun (a : X → ℤ) j => translate (fun i => (a i : ℝ)) (p j)
    let hma := fun (a : X → ℤ) j => coefficients_translate_mem (U j) (fun i => (a i : ℝ)) (p j) (hm j)
    let D := fun a center => translatedSelectedPhysicalDensity (G := G) B U b hb o R σ hR hσ L₀
      (coefficientConstantCenter U center) (pa a) (hma a)
    let Q := trimmedIntegerBox N margin
    let Z := fun center => selectedJointDensityMass Q stride T W (fun a => D a center)
    let M := ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (V j)
    ∃ hQ : Q.Nonempty,
    ∃ hW : ∀ z, 0 < W z,
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T W z,
    ∃ hD : ∀ center, 0 < Z center,
    let law := fun center => selectedJointFiniteLaw Q hQ stride T W hW hZ (fun a => D a center)
      (fun a => translatedSelectedPhysicalDensity_nonneg (G := G) B U b hb o R σ hR hσ L₀
        (coefficientConstantCenter U center) (pa a) (hma a)) (hD center)
    (∀ center, |Z center-1| ≤ 3*δ ∧ 1/2 ≤ Z center ∧ Z center ≤ 3/2) ∧
    (∀ root : LayerSamplerVariables G I n B → ℤ,
      (∀ k, |(root k : ℝ)| ≤ Real.exp P) → ∀ z : Q × rectangularWeightIndices 0 W 1,
        jointIntegerPhysicalSite root (z.1.val,z.2.val) ∈ integerBox N) ∧
    (∀ center z, 0 < (law center).weight z →
      columnResiduePattern stride z.2.val ∈ T ∧ 0 < D z.1.val center z.2.val) ∧
    (∀ center, ∃ c : ∀ j, U j, coefficientConstantCenter U center =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (constantCoefficientArray U (fun s => c s.1))) ∧
      ∀ z, 0 < (law center).weight z →
        HasQuarterAffinePolynomialLifts p (fun j => (c j).val)
          (fun k i => (jointIntegerFrame (z.1.val,z.2.val) k i : ℝ))
          (layerSamplerBox B U b (selectedLayerSamplerScale B U b R σ hR hσ L₀))) ∧
    (∀ root : LayerSamplerVariables G I n B → ℤ,
      (∀ k, |(root k : ℝ)| ≤ Real.exp P) → ∀ center (φ : (X → ℝ) → ℝ),
      (∀ v, φ v ∈ Set.Icc (0 : ℝ) 1) →
      (law center).mean (fun z => φ (fun i => (jointIntegerPhysicalSite root (z.1.val,z.2.val) i : ℝ))) ≤
        2*M*(𝔼 x ∈ integerBox N, φ (fun i => (x i : ℝ))) + 12*δ) ∧
    (∀ root : LayerSamplerVariables G I n B → ℤ,
      (∀ k, |(root k : ℝ)| ≤ Real.exp P) → ∀ φ : (X → ℝ) → ℂ, (∀ v, ‖φ v‖ ≤ 1) →
      ‖(∫ center, (law center).complexMean
          (fun z => φ (fun i => (jointIntegerPhysicalSite root (z.1.val,z.2.val) i : ℝ))) ∂μ) -
        (𝔼 x ∈ integerBox N, φ (fun i => (x i : ℝ)))‖ ≤
        12*δ + 2 * (Fintype.card X : ℝ) * τ) ∧
    ∀ center, (law center).mean
      (fun z => noninjectivityIndicator (fun q => jointIntegerPhysicalSite (site q) (z.1.val,z.2.val))) ≤ δ := by
  obtain ⟨A₀, _, hsampler⟩ := exists_explicit_joint_sampler_marginals m
  obtain ⟨A₁, _, hcollisionBudget⟩ := exists_selectedCollisionLog_bound m
  let A := max 256 (max A₀ A₁)
  have hA : 256 ≤ A := le_max_left _ _
  refine ⟨A, by omega, ?_⟩
  intro X G S₀ _ _ _ _ _ _ I _ n B _ J _ U b hb o _ _ _ _ μ _ _ ν _ _
    R σ hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall L₀ P δ hP hδ hδsmall hδP
    hX hK hI hn hJ hAP hL₀P hCP hVP hRP hσP site hsite hsitebound τ hτ hτhalf hτP hτdim p hp hm
    stride hs Rrank S hS hSP hstride N hsize hrank hRrank T hT
  have hthreshold (a : ℕ) (ha : a ≤ A) : Real.exp ((P+a)^a) ≤ Real.exp ((P+A)^A) := by
    apply Real.exp_le_exp.mpr
    have haa : (a : ℝ) ≤ A := by exact_mod_cast ha
    have hAr : (256 : ℝ) ≤ A := by exact_mod_cast hA
    exact (pow_le_pow_left₀ (by positivity) (by linarith : P+(a:ℝ) ≤ P+A) a).trans
      (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ P+A) ha)
  have h₀ := hthreshold A₀ ((le_max_left A₀ A₁).trans (le_max_right 256 _))
  have h₁ := hthreshold A₁ ((le_max_right A₀ A₁).trans (le_max_right 256 _))
  have hsample (root : LayerSamplerVariables G I n B → ℤ)
      (hroot : ∀ k, |(root k : ℝ)| ≤ Real.exp P) :=
    hsampler B U b hb o μ ν R σ hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall L₀
      hP hδ hδsmall hδP hX hK hI hn hJ hAP hL₀P hCP hVP hRP hσP root hroot τ hτ hτhalf hτP hτdim
      p hp hm stride hs hS hSP hstride N (fun i => h₀.trans (hsize i)) hrank
      (h₀.trans hRrank) T hT
  obtain ⟨hQ, hW, hZ, hD, hclose, _, _⟩ :=
    hsample 0 (fun k => by simpa using (Real.exp_pos P).le)
  let W := trimmedSpatialWidths (K := LayerSamplerVariables G I n B) (Real.exp (2*P)) τ N
  let Q := trimmedIntegerBox N (spatialTrimMargin τ N)
  let pa := fun (a : X → ℤ) j => translate (fun i => (a i : ℝ)) (p j)
  let hma := fun (a : X → ℤ) j => coefficients_translate_mem (U j) (fun i => (a i : ℝ)) (p j) (hm j)
  let D := fun a center => translatedSelectedPhysicalDensity (G := G) B U b hb o R σ hR hσ L₀
    (coefficientConstantCenter U center) (pa a) (hma a)
  have hN (i) : 0 < N i := by
    have := four_le_of_spatial_threshold hP hA (N i) (hsize i)
    omega
  have hmarginSize (i) : 4 ≤ τ * (N i : ℝ) :=
    spatialTrimMargin_size_of_exp_size hP hτ hτP
      ((spatial_threshold_large hP hA).trans (hsize i))
  have hscale := trimmedSpatialWidths_scale (K := LayerSamplerVariables G I n B)
    (Real.exp_pos (2*P)).le stride hs N (fun i =>
      spatial_scale_of_exp_size hP hτ hτP (Nat.cast_nonneg _) ((hstride i).trans hSP) hAP
        ((spatial_threshold_large hP hA).trans (hsize i)))
  refine ⟨hQ, hW, hZ, hD, hclose, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro root hroot z
    exact jointIntegerPhysicalSite_mem_box root N _
      (fun i => (spatialTrimMargin_proper hτhalf N hN hmarginSize i).le) W
      (spatialTrimMargin_fits (Real.exp_pos (2*P)).le hτ.le root
        (root_sum_le_spatial_budget hK root hroot) N) z
  · intro center z hz
    exact selectedJointFiniteLaw_support Q hQ stride T W hW hZ (fun a => D a center)
      (fun a => translatedSelectedPhysicalDensity_nonneg (G := G) B U b hb o R σ hR hσ L₀
        (coefficientConstantCenter U center) (pa a) (hma a)) (hD center) z hz
  · intro center
    exact exists_selectedJointFiniteLaw_lifts B U b hb o R σ hR hσ L₀ p hm
      hσ1 Cinv hCinv hchart hsmall hp Q hQ stride T W hW hZ center (hD center)
  · intro root hroot center φ hφ
    obtain ⟨_, _, _, _, _, hdom, _⟩ := hsample root hroot
    simpa only [jointIntegerPhysicalSite_cast] using hdom center φ hφ
  · intro root hroot φ hφ
    obtain ⟨_, _, _, _, _, _, hmix⟩ := hsample root hroot
    simpa only [jointIntegerPhysicalSite_cast] using hmix φ hφ
  · intro center
    let i : X := Classical.choice inferInstance
    exact selectedJointFiniteLaw_collision_small Q hQ m site hsite i hP hδ hδP hK hsitebound
      stride hs ((hstride i).trans hSP) T hT W hW hZ hscale
      (spatialWidthFraction_pos P hτ) (spatialWidthFraction_inv_le hP hτ hτP)
      ((Real.exp_le_exp.mpr (hcollisionBudget P hP)).trans (h₁.trans (hsize i)))
      (fun k => spatialWidthFraction_le_trimmed_width P hτ.le N (some k,i))
      (fun a => D a center)
      (fun a => translatedSelectedPhysicalDensity_nonneg (G := G) B U b hb o R σ hR hσ L₀
        (coefficientConstantCenter U center) (pa a) (hma a)) (hD center) (hclose center).2.1
      (fun a z => translatedSelectedPhysicalDensity_le_exp B U b hb o C V hC hV R σ hR hσ hσ1
        Cinv hCinv hchart hsmall L₀ hP hK hRP hσP hI hn hJ hAP hL₀P hCP hVP
        (coefficientConstantCenter U center) (pa a) (hma a) z)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open Module Submodule MeasureTheory VectorPolynomial
open scoped BigOperators NNReal Classical

theorem exists_full_parameter_joint_sampler (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {X G : Type*} [Fintype X] [DecidableEq X] [Nonempty X] [Fintype G] [Nonempty G]
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
    (τ : ℝ) (_hτ : 0 < τ) (_hτhalf : τ ≤ 1/2) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hτdim : (Fintype.card X : ℝ) * τ ≤ 1/2)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val+1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ) (_hs : ∀ k, 0 < stride k)
    {Rrank S : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (N : X → ℕ) (_hsize : ∀ k, Real.exp ((P+A)^A) ≤ (N k : ℝ))
    (_hrank : ∀ j, HasLayerSamplingRank (j.val+1) (fun i => (N i : ℝ)) Rrank (U j) (p j))
    (_hRrank : Real.exp ((P+A)^A) ≤ Rrank)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty),
    let scale := selectedLayerSamplerScale (G := G) B U b R σ hR hσ L₀
    let sides := layerSamplerSides (G := G) B U b R scale.value
    let sites := layerSamplerIntegerBox B U b scale
    let P' := selectedFourierInputBudget m P
    let W := trimmedSpatialWidths (K := LayerSamplerVariables G I n B) (Real.exp (2*P')) τ N
    let margin := spatialTrimMargin τ N
    let pa := fun (a : X → ℤ) j => translate (fun i => (a i : ℝ)) (p j)
    let hma := fun (a : X → ℤ) j => coefficients_translate_mem (U j) (fun i => (a i : ℝ)) (p j) (hm j)
    let D := fun a center => translatedSelectedPhysicalDensity (G := G) B U b hb o R σ hR hσ L₀
      (coefficientConstantCenter U center) (pa a) (hma a)
    let Q := trimmedIntegerBox N margin
    let Z := fun center => selectedJointDensityMass Q stride T W (fun a => D a center)
    let M := ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (V j)
    L₀ ≤ scale.value ∧ (scale.value : ℝ) ≤ Real.exp P' ∧
    (∀ k, 0 < sides k ∧ sides k ≤ scale.value) ∧
    (∃ k, sides k = scale.value) ∧ sites.Nonempty ∧
    ∃ hQ : Q.Nonempty,
    ∃ hW : ∀ z, 0 < W z,
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T W z,
    ∃ hD : ∀ center, 0 < Z center,
    let law := fun center => selectedJointFiniteLaw Q hQ stride T W hW hZ (fun a => D a center)
      (fun a => translatedSelectedPhysicalDensity_nonneg (G := G) B U b hb o R σ hR hσ L₀
        (coefficientConstantCenter U center) (pa a) (hma a)) (hD center)
    (∀ center, |Z center-1| ≤ 3*δ ∧ 1/2 ≤ Z center ∧ Z center ≤ 3/2) ∧
    (∀ root ∈ sites, ∀ z : Q × rectangularWeightIndices 0 W 1,
      jointIntegerPhysicalSite root (z.1.val,z.2.val) ∈ integerBox N) ∧
    (∀ center z, 0 < (law center).weight z →
      columnResiduePattern stride z.2.val ∈ T ∧ 0 < D z.1.val center z.2.val) ∧
    (∀ center, ∃ c : ∀ j, U j, coefficientConstantCenter U center =
      -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
        (constantCoefficientArray U (fun s => c s.1))) ∧
      ∀ z, 0 < (law center).weight z →
        HasQuarterAffinePolynomialLifts p (fun j => (c j).val)
          (fun k i => (jointIntegerFrame (z.1.val,z.2.val) k i : ℝ))
          (fun k => (sides k : ℝ))) ∧
    (∀ root ∈ sites, ∀ center (φ : (X → ℝ) → ℝ), (∀ v, φ v ∈ Set.Icc (0 : ℝ) 1) →
      (law center).mean (fun z => φ (fun i => (jointIntegerPhysicalSite root (z.1.val,z.2.val) i : ℝ))) ≤
        2*M*(𝔼 x ∈ integerBox N, φ (fun i => (x i : ℝ))) + 12*δ) ∧
    (∀ root ∈ sites, ∀ φ : (X → ℝ) → ℂ, (∀ v, ‖φ v‖ ≤ 1) →
      ‖(∫ center, (law center).complexMean
          (fun z => φ (fun i => (jointIntegerPhysicalSite root (z.1.val,z.2.val) i : ℝ))) ∂μ) -
        (𝔼 x ∈ integerBox N, φ (fun i => (x i : ℝ)))‖ ≤
        12*δ + 2 * (Fintype.card X : ℝ) * τ) ∧
    (∀ center (φ : (X → ℝ) → ℝ), (∀ v, φ v ∈ Set.Icc (0 : ℝ) 1) →
      (𝔼 root ∈ sites, (law center).mean
        (fun z => φ (fun i => (jointIntegerPhysicalSite root (z.1.val,z.2.val) i : ℝ)))) ≤
        2*M*(𝔼 x ∈ integerBox N, φ (fun i => (x i : ℝ))) + 12*δ) ∧
    (∀ φ : (X → ℝ) → ℂ, (∀ v, ‖φ v‖ ≤ 1) →
      ‖(𝔼 root ∈ sites, ∫ center, (law center).complexMean
          (fun z => φ (fun i => (jointIntegerPhysicalSite root (z.1.val,z.2.val) i : ℝ))) ∂μ) -
        (𝔼 x ∈ integerBox N, φ (fun i => (x i : ℝ)))‖ ≤
        12*δ + 2 * (Fintype.card X : ℝ) * τ) ∧
    ∀ center, (law center).mean
      (fun z => noninjectivityIndicator
        (fun root : sites => jointIntegerPhysicalSite root.val (z.1.val,z.2.val))) ≤ δ := by
  obtain ⟨a, _, hsampler⟩ := exists_explicit_joint_sampler_with_collisions m
  obtain ⟨A, hA, hthreshold⟩ := exists_selectedParameterThreshold m a
  refine ⟨A, hA, ?_⟩
  intro X G _ _ _ _ _ I _ n B _ J _ U b hb o _ _ _ _ μ _ _ ν _ _
    R σ hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall L₀ P δ hP hδ hδsmall hδP
    hX hK hI hn hJ hAP hL₀P hCP hVP hRP hσP τ hτ hτhalf hτP hτdim p hp hm
    stride hs Rrank S hS hSP hstride N hsize hrank hRrank T hT
  let scale := selectedLayerSamplerScale (G := G) B U b R σ hR hσ L₀
  let sites := layerSamplerIntegerBox B U b scale
  let P' := selectedFourierInputBudget m P
  have hP' : 0 ≤ P' := selectedFourierInputBudget_nonneg m hP
  have hPP' : P ≤ P' := le_selectedFourierInputBudget m hP
  have heP : Real.exp P ≤ Real.exp P' := Real.exp_le_exp.mpr hPP'
  have hscale : (scale.value : ℝ) ≤ Real.exp P' :=
    selectedLayerSamplerScale_input_bound B U b R σ hR hσ L₀ hP hK hn hRP hσP hAP hL₀P
  have hsite (root : sites) (k) : |(root.val k : ℝ)| ≤ Real.exp P' :=
    layerSamplerIntegerBox_root_bound B U b scale hscale root.property k
  obtain ⟨hQ, hW, hZ, hD, hclose, hsupport, hresidue, hlifts, hdom, hmix, hcollision⟩ :=
    hsampler (S₀ := sites) B U b hb o μ ν R σ hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall L₀
      hP' hδ hδsmall (hδP.trans heP) (hX.trans hPP') (hK.trans hPP')
      (fun j => (hI j).trans hPP') (fun j => (hn j).trans hPP') (fun j => (hJ j).trans hPP')
      (hAP.trans heP) (hL₀P.trans heP) (fun j => (hCP j).trans heP) (fun j => (hVP j).trans heP)
      (fun j => (hRP j).trans heP) (fun j => (hσP j).trans heP)
      (fun root : sites => root.val) Subtype.val_injective hsite
      τ hτ hτhalf (hτP.trans heP) hτdim p hp hm stride hs hS (hSP.trans heP) hstride
      N (fun k => (hthreshold P hP).trans (hsize k)) hrank ((hthreshold P hP).trans hRrank) T hT
  refine ⟨(selectedLayerSamplerScale_bounds B U b R σ hR hσ L₀).1, hscale,
    (fun k => ⟨layerSamplerSides_pos B U b R scale.positive k,
      layerSamplerSides_le B U b R scale.positive k⟩),
    layerSamplerSides_attains_scale B U b scale, layerSamplerIntegerBox_nonempty B U b scale,
    hQ, hW, hZ, hD, hclose, ?_, hresidue, hlifts, ?_, ?_, ?_, ?_, hcollision⟩
  · intro root hroot z
    exact hsupport root (hsite ⟨root,hroot⟩) z
  · intro root hroot center φ hφ
    exact hdom root (hsite ⟨root,hroot⟩) center φ hφ
  · intro root hroot φ hφ
    exact hmix root (hsite ⟨root,hroot⟩) φ hφ
  · intro center φ hφ
    exact Finset.expect_le (layerSamplerIntegerBox_nonempty B U b scale)
      (fun root hroot => hdom root (hsite ⟨root,hroot⟩) center φ hφ)
  · intro φ hφ
    exact norm_finset_expect_sub_const_le sites (layerSamplerIntegerBox_nonempty B U b scale) _ _
      (fun root hroot => hmix root (hsite ⟨root,hroot⟩) φ hφ)

end Erdos3.BooleanCubeKernel

end

end OAI

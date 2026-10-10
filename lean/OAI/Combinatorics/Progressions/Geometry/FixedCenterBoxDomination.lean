import OAI.Combinatorics.Progressions.Sampling.TranslatedSamplerDomination

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open Module Submodule MeasureTheory VectorPolynomial
open scoped BigOperators NNReal

theorem exists_fixed_center_selected_sampler_box_domination (m : ℕ) :
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
    (N margin : X → ℕ) (_hmargin : ∀ i, 2 * margin i < N i)
    (_hfit : ∀ i, physicalSiteWidth root W i ≤ (margin i : ℝ))
    (_hloss : (∑ i, 2 * (margin i : ℝ) / N i) ≤ 1/2),
    let pa := fun (a : X → ℤ) j => translate (fun i => (a i : ℝ)) (p j)
    let hma := fun (a : X → ℤ) j => coefficients_translate_mem (U j) (fun i => (a i : ℝ)) (p j) (hm j)
    let D := fun a center => translatedSelectedPhysicalDensity (G := G) B U b hb o R σ hR hσ L₀
      center (pa a) (hma a)
    let Z := fun a center => selectedResidueDensityMass stride T W (D a center)
    let M := ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (V j)
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T W z,
    ∃ hD : ∀ a center, 0 < Z a center,
      (∀ a center, |Z a center-1| ≤ 3*δ ∧ 1/2 ≤ Z a center ∧ Z a center ≤ 3/2) ∧
      ∀ center (φ : (X → ℝ) → ℝ), (∀ v, φ v ∈ Set.Icc (0 : ℝ) 1) →
        (𝔼 a ∈ trimmedIntegerBox N margin,
          ∑' z, (selectedResidueDensityPMF stride T W hW hZ (D a center)
            (translatedSelectedPhysicalDensity_nonneg (G := G) B U b hb o R σ hR hσ L₀
              center (pa a) (hma a)) (hD a center) z).toReal *
              φ ((fun i => (a i : ℝ)) + physicalAffineSite root z)) ≤
            2*M*(𝔼 x ∈ integerBox N, φ (fun i => (x i : ℝ))) + 6*δ := by
  obtain ⟨A, hA, hlaw⟩ := exists_translated_selected_sampler_oneSite_domination m
  refine ⟨A, hA, ?_⟩
  intro X G _ _ _ I _ n B _ J _ U b hb o _ _ _ _ μ _ _ ν _ _
    R σ hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall L₀ P δ hP hδ hδsmall hδP
    hX hK hI hn hJ hAP hL₀P hCP hVP hRP hσP root hroot p hp hm stride hs Rrank S ρ
    hS hSP hstride hρ hρP H hsize hrank hRrank T hT W hW hwidth N margin hmargin hfit hloss
  let pa := fun (a : X → ℤ) j => translate (fun i => (a i : ℝ)) (p j)
  let hma := fun (a : X → ℤ) j => coefficients_translate_mem (U j) (fun i => (a i : ℝ)) (p j) (hm j)
  have hlocal (a : X → ℤ) := hlaw B U b hb o μ ν R σ hR hσ hσ1 C V hC hV
    Cinv hCinv hchart hsmall L₀ hP hδ hδsmall hδP hX hK hI hn hJ hAP hL₀P hCP hVP hRP hσP
    root hroot (pa a)
    (fun j => degreeLE_translate (1 : X → ℕ) (fun _ => by norm_num) _ (p j) (hp j))
    (hma a) stride hs hS hSP hstride hρ hρP H hsize
    (fun j => (hasLayerSamplingRank_translate_iff _ _ H Rrank (U j) (p j) (hp j)).mpr (hrank j))
    hRrank T hT W hW hwidth
  choose hZ hcenters using hlocal
  choose hD hrest using fun a center => hcenters a center
  refine ⟨hZ 0, hD, fun a center => ⟨(hrest a center).1, (hrest a center).2.1,
    (hrest a center).2.2.1⟩, ?_⟩
  intro center φ hφ
  have hM : 0 ≤ ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (V j) :=
    Finset.prod_nonneg (fun j _ => earlyConstantDensityCap_nonneg _ _ (hR j) (V j).coe_nonneg)
  refine selectedResidue_trimmed_domination_transfer root N margin hmargin hloss stride T W hW (hZ 0)
    hfit (fun x => φ (fun i => (x i : ℝ))) (fun x _ => (hφ _).1) _ hM ?_
  intro a _
  have h := (hrest a center).2.2.2 (fun v => φ ((fun i => (a i : ℝ)) + v)) (fun v => hφ _)
  have hcast (z : Option (LayerSamplerVariables G I n B) × X → ℤ) :
      (fun i => ((a + integerPhysicalSite root z) i : ℝ)) =
        (fun i => (a i : ℝ)) + physicalAffineSite root z := by
    funext i
    simp only [Pi.add_apply, Int.cast_add, integerPhysicalSite_cast_apply]
  simpa only [hcast] using h

end Erdos3.BooleanCubeKernel

end

end OAI

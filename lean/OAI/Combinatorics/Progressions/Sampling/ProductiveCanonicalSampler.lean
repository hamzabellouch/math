import OAI.Combinatorics.Progressions.Sampling.JointMeasureProductiveNarrowSampler

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open Module Submodule MeasureTheory VectorPolynomial
open scoped BigOperators NNReal Classical

theorem exists_productive_canonical_sampler (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {X G S₀ : Type*} [Fintype X] [DecidableEq X] [Nonempty X] [Fintype G] [DecidableEq G]
    [Fintype S₀] [DecidableEq S₀] [Nonempty S₀]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
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
    (rootBudget : ℝ) (_hrootBudget : 0 ≤ rootBudget) (_hrootBudgetP : rootBudget ≤ Real.exp P)
    (_hsitebound : ∀ q, (∑ k, |(site q k : ℝ)|) ≤ rootBudget)
    (ξ : ℝ) (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (τ : ℝ) (_hτ : 0 < τ) (_hτhalf : τ ≤ 1/2) (_hτP : τ⁻¹ ≤ Real.exp P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val+1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ) (_hs : ∀ k, 0 < stride k)
    {Rrank S : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (N : X → ℕ) (_hsize : ∀ k, Real.exp ((P+A)^A) ≤ (N k : ℝ))
    (_hrank : ∀ j, HasLayerSamplingRank (j.val+1) (fun i => (N i : ℝ)) Rrank (U j) (p j))
    (_hRrank : Real.exp ((P+A)^A) ≤ Rrank)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty),
    let S := selectedLayerSamplerScale B U b R σ hR hσ L₀
    let W := narrowTrimmedSpatialWidths (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) rootBudget τ ξ N
    let Q := trimmedIntegerBox N (spatialTrimMargin τ N)
    ∃ hN : ∀ i, 0 < N i,
    ∃ hQ : Q.Nonempty,
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T W z,
    ∀ (test : (X → ℝ) → ℝ), (∀ x, |test x| ≤ 1) →
    ∀ gain : ℝ, 0 < gain →
    δ ≤ gain / 16 → 12 * δ + 2 * (Fintype.card X : ℝ) * τ ≤ gain / 8 →
    gain ≤ (𝔼 x ∈ integerBox N, test (fun i => (x i : ℝ))) →
    ∃ c : ∀ j, U j,
    let pc := fun j => subtractConstant (c j).val (p j)
    let hpc := fun j => coefficients_subtractConstant_mem (U j) (c j) (p j) (hm j)
    ∃ htotal : 0 < selectedJointDensityMass Q stride T W
        (allocatedJointBaseDensity B U b hb o hR hσ S X pc hpc),
    let law := allocatedOriginalPathLaw B U b hb o hR hσ S X pc hpc
      N hN _hrootBudget _hτ _hξ stride T hZ Q hQ htotal
    gain / 4 ≤ law.mass (Finset.univ.filter (fun z =>
      Function.Injective (fun q => jointIntegerPhysicalSite (site q) (z.1.val, z.2.val)) ∧
      gain / 2 ≤ 𝔼 q : S₀, test (fun i => (jointIntegerPhysicalSite (site q) (z.1.val, z.2.val) i : ℝ)))) ∧
    (∀ z, 0 < law.weight z →
      allocatedAffineDensity B U b hb o hR hσ S p hm c
        (fun k v => (jointIntegerFrame (z.1.val, z.2.val) k v : ℝ)) ≠ 0) ∧
    ∀ z : Q × rectangularWeightIndices 0 W 1, ∀ q,
      jointIntegerPhysicalSite (site q) (z.1.val, z.2.val) ∈ integerBox N := by
  obtain ⟨A, hA, hsampler⟩ := exists_productive_narrow_sampler m
  refine ⟨A, hA, ?_⟩
  intro X G S₀ _ _ _ _ _ _ _ _ I _ _ n B _ _ J _ U b hb o _ _ _ _ μ _ _ ν _ _
    R σ hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall L₀ P δ hP hδ hδsmall hδP
    hX hK hI hn hJ hAP hL₀P hCP hVP hRP hσP site hsite
    rootBudget hrootBudget hrootBudgetP hsitebound ξ hξ hξ1 hξP τ hτ hτhalf hτP p hp hm
    stride hs Rrank strideBound hS hSP hstride N hsize hrank hRrank T hT S W Q
  obtain ⟨hQ, hW, hZ, hD, hproductive⟩ :=
    hsampler B U b hb o μ ν R σ hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall L₀
      hP hδ hδsmall hδP hX hK hI hn hJ hAP hL₀P hCP hVP hRP hσP site hsite
      rootBudget hrootBudget hrootBudgetP hsitebound ξ hξ hξ1 hξP τ hτ hτhalf hτP p hp hm
      stride hs hS hSP hstride N hsize hrank hRrank T hT
  have hN (i) : 0 < N i := by exact_mod_cast (Real.exp_pos _).trans_le (hsize i)
  refine ⟨hN, hQ, hZ, ?_⟩
  intro test htest gain hgain hbad herror hscore
  obtain ⟨center, c, hc, hprod, _, hinside⟩ := hproductive test htest gain hgain hbad herror hscore
  have hdensity := allocatedJointBaseDensity_subtractConstant_selected B U b hb o hR hσ
    S p hm c L₀ rfl center hc
  have htotal : 0 < selectedJointDensityMass Q stride T W
      (allocatedJointBaseDensity B U b hb o hR hσ S X
        (fun j => subtractConstant (c j).val (p j))
        (fun j => coefficients_subtractConstant_mem (U j) (c j) (p j) (hm j))) := by
    rw [hdensity]
    exact hD center
  refine ⟨c, htotal, ?_, ?_, hinside⟩
  · rw [allocatedOriginalPathLaw_subtractConstant_eq_selected B U b hb o hR hσ S p hm c
      N hN hrootBudget hτ hξ stride T hZ Q hQ htotal L₀ rfl center hc (hD center)]
    exact hprod
  · intro z hz
    exact allocatedOriginalPathLaw_positive_affine B U b hb o hR hσ S p hm c
      N hN hrootBudget hτ hξ stride T hZ Q hQ htotal z hz

end Erdos3.BooleanCubeKernel

end

end OAI

import OAI.Combinatorics.Progressions.Dynamics.SelectedParameterBudget
import OAI.Combinatorics.Progressions.Lattices.LayerSamplerIntegerBox
import OAI.Combinatorics.Progressions.Sampling.AnchoredSamplerGeometry

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators NNReal Classical

theorem exists_full_parameter_anchored_geometry (m : ℕ) :
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
    (anchor : Option (LayerSamplerVariables G I n B) × X → ℤ)
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
    let scale := selectedLayerSamplerScale (G := G) B U b R σ hR hσ L₀
    let sides := layerSamplerSides (G := G) B U b R scale.value
    let sites := layerSamplerIntegerBox B U b scale
    let D := selectedPhysicalDensity (G := G) B U b hb o R σ hR hσ L₀ p hm
    let Z := selectedResidueDensityMass stride T W (fun z => D (anchor + z))
    L₀ ≤ scale.value ∧ (scale.value : ℝ) ≤ Real.exp (selectedFourierInputBudget m P) ∧
    (∀ k, 0 < sides k ∧ sides k ≤ scale.value) ∧
    (∃ k, sides k = scale.value) ∧ sites.Nonempty ∧
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T W z,
    ∃ hD : 0 < Z,
    let law := translatedSelectedResidueDensityPMF anchor stride T W hW hZ D
      (selectedPhysicalDensity_nonneg B U b hb o R σ hR hσ L₀ p hm) hD
    |Z-1| ≤ 3*δ ∧ 1/2 ≤ Z ∧ Z ≤ 3/2 ∧
      (∀ z, 0 < (law z).toReal →
        z - anchor ∈ rectangularWeightIndices 0 W 1 ∧
        columnResiduePattern stride (z - anchor) ∈ T ∧ 0 < D z) ∧
      (∀ z, 0 < (law z).toReal →
        HasQuarterAffinePolynomialLifts p (fun _ => 0) (fun k x => (z (k,x) : ℝ))
          (layerSamplerBox B U b (selectedLayerSamplerScale B U b R σ hR hσ L₀))) ∧
      (∑' z, (law z).toReal *
        noninjectivityIndicator (fun q : sites => integerPhysicalSite q.val z)) ≤ δ := by
  obtain ⟨a, _, hgeometry⟩ := exists_anchored_sampler_geometry m
  obtain ⟨A, hA, hthreshold⟩ := exists_selectedParameterThreshold m a
  refine ⟨A, hA, ?_⟩
  intro X G _ _ _ _ _ I _ n B _ J _ U b hb o _ _ _ _ μ _ _ ν _ _
    R σ hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall L₀ P δ hP hδ hδsmall hδP
    hX hK hI hn hJ hAP hL₀P hCP hVP hRP hσP anchor p hp hm stride hs Rrank S ρ
    hS hSP hstride hρ hρP H hsize hrank hRrank T hT W hW hwidth
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
  have hresult := hgeometry (Q := sites) B U b hb o μ ν R σ hR hσ hσ1 C V hC hV
    Cinv hCinv hchart hsmall L₀ hP' hδ hδsmall (hδP.trans heP) (hX.trans hPP') (hK.trans hPP')
    (fun j => (hI j).trans hPP') (fun j => (hn j).trans hPP') (fun j => (hJ j).trans hPP')
    (hAP.trans heP) (hL₀P.trans heP) (fun j => (hCP j).trans heP) (fun j => (hVP j).trans heP)
    (fun j => (hRP j).trans heP) (fun j => (hσP j).trans heP)
    (fun root : sites => root.val) Subtype.val_injective hsite anchor p hp hm stride hs
    hS (hSP.trans heP) hstride hρ (hρP.trans heP) H
    (fun k => (hthreshold P hP).trans (hsize k)) hrank ((hthreshold P hP).trans hRrank)
    T hT W hW hwidth
  exact ⟨(selectedLayerSamplerScale_bounds B U b R σ hR hσ L₀).1, hscale,
    (fun k => ⟨layerSamplerSides_pos B U b R scale.positive k,
      layerSamplerSides_le B U b R scale.positive k⟩),
    layerSamplerSides_attains_scale B U b scale, layerSamplerIntegerBox_nonempty B U b scale,
    hresult⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators NNReal Classical

theorem exists_centered_full_parameter_anchored_geometry (m : ℕ) :
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
    (x : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    (anchor : Option (LayerSamplerVariables G I n B) × X → ℤ)
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
    let scale := selectedLayerSamplerScale (G := G) B U b R σ hR hσ L₀
    let sides := layerSamplerSides (G := G) B U b R scale.value
    let sites := layerSamplerIntegerBox B U b scale
    let center := coefficientConstantCenter U x
    let D := translatedSelectedPhysicalDensity (G := G) B U b hb o R σ hR hσ L₀ center p hm
    let Z := selectedResidueDensityMass stride T W (fun z => D (anchor + z))
    L₀ ≤ scale.value ∧ (scale.value : ℝ) ≤ Real.exp (selectedFourierInputBudget m P) ∧
    (∀ k, 0 < sides k ∧ sides k ≤ scale.value) ∧
    (∃ k, sides k = scale.value) ∧ sites.Nonempty ∧
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T W z,
    ∃ hD : 0 < Z,
    let law := translatedSelectedResidueDensityPMF anchor stride T W hW hZ D
      (translatedSelectedPhysicalDensity_nonneg B U b hb o R σ hR hσ L₀ center p hm) hD
    |Z-1| ≤ 3*δ ∧ 1/2 ≤ Z ∧ Z ≤ 3/2 ∧
      (∀ z, 0 < (law z).toReal →
        z - anchor ∈ rectangularWeightIndices 0 W 1 ∧
        columnResiduePattern stride (z - anchor) ∈ T ∧ 0 < D z) ∧
      (∃ c : ∀ j, U j, center = -(QuotientAddGroup.mk' (coefficientIntegerLattice U)
          (constantCoefficientArray U (fun s => c s.1))) ∧
        ∀ z, 0 < (law z).toReal →
          HasQuarterAffinePolynomialLifts p (fun j => (c j).val) (fun k v => (z (k,v) : ℝ))
            (layerSamplerBox B U b (selectedLayerSamplerScale B U b R σ hR hσ L₀))) ∧
      (∑' z, (law z).toReal *
        noninjectivityIndicator (fun q : sites => integerPhysicalSite q.val z)) ≤ δ := by
  obtain ⟨A, hA, hgeometry⟩ := exists_full_parameter_anchored_geometry m
  refine ⟨A, hA, ?_⟩
  intro X G _ _ _ _ _ I _ n B _ J _ U b hb o _ _ _ _ μ _ _ ν _ _
    R σ hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall L₀ P δ hP hδ hδsmall hδP
    hX hK hI hn hJ hAP hL₀P hCP hVP hRP hσP x anchor p hp hm stride hs Rrank S ρ
    hS hSP hstride hρ hρP H hsize hrank hRrank T hT W hW hwidth
  obtain ⟨c, hc⟩ := exists_subtractive_constant_center (K := LayerSamplerVariables G I n B) U x
  let p' := fun j => subtractConstant (c j).val (p j)
  let hm' := fun j => coefficients_subtractConstant_mem (U j) (c j) (p j) (hm j)
  have hp' (j) : DegreeLE (1 : X → ℕ) (j.val+1) (p' j) := (hp j).subtractConstant _
  have hrank' (j) : HasLayerSamplingRank (j.val+1) H Rrank (U j) (p' j) :=
    (hasLayerSamplingRank_subtractConstant_iff (Nat.zero_lt_succ _) H Rrank (U j) _ (p j)).mpr (hrank j)
  have he : selectedPhysicalDensity (G := G) B U b hb o R σ hR hσ L₀ p' hm' =
      translatedSelectedPhysicalDensity (G := G) B U b hb o R σ hR hσ L₀
        (coefficientConstantCenter U x) p hm := by
    funext z
    simpa only [p', hm', ← hc] using selectedPhysicalDensity_subtractConstant B U b hb o R σ hR hσ L₀ p hm c z
  have hresult := hgeometry B U b hb o μ ν R σ hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall L₀
    hP hδ hδsmall hδP hX hK hI hn hJ hAP hL₀P hCP hVP hRP hσP anchor p' hp' hm' stride hs
    hS hSP hstride hρ hρP H hsize hrank' hRrank T hT W hW hwidth
  simp only [he] at hresult
  obtain ⟨hL₀, hL, hsides, hmax, hsites, hZ, hD, hclose, hlower, hupper,
    hsupport, hlifts, hcollision⟩ := hresult
  refine ⟨hL₀, hL, hsides, hmax, hsites, hZ, hD, hclose, hlower, hupper,
    hsupport, ⟨c, hc, ?_⟩, hcollision⟩
  intro z hz
  exact HasQuarterAffinePolynomialLifts.of_subtractConstant (p := p) (c := fun j => (c j).val)
    (hlifts z hz)

end Erdos3.VectorPolynomial

end

end OAI

import OAI.Combinatorics.Progressions.Linear.SmallKernelAllSites
import OAI.Combinatorics.Progressions.Sampling.KernelSamplerThreshold

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators NNReal Classical

theorem exists_kernel_full_parameter_geometry (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {X G : Type*} [Fintype X] [DecidableEq X] [Nonempty X] [Fintype G] [Nonempty G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables (G × X) I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables (G × X) I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables (G × X) I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables (G × X) I n B) U))
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
    (_hK : (Fintype.card (LayerSamplerVariables (G × X) I n B) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P) (_hL₀P : (L₀ : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (τ : ℝ) (_hτ : 0 < τ) (_hτ1 : τ ≤ 1) (_hτP : 1/τ ≤ Real.exp P)
    (x : CoefficientTorus (K := LayerSamplerVariables (G × X) I n B) U)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val+1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ) (_hs : ∀ k, 0 < stride k)
    {Rrank S : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (N : X → ℕ) (_hN : ∀ i, 4 ≤ N i)
    (_hsize : ∀ k, Real.exp ((P+A)^A) ≤ (N k : ℝ))
    (_hrank : ∀ j, HasLayerSamplingRank (j.val+1) (fun i => (N i : ℝ)) Rrank (U j) (p j))
    (_hRrank : Real.exp ((P+A)^A) ≤ Rrank)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables (G × X) I n B)) X stride)) (_hT : T.Nonempty),
    let scale := selectedLayerSamplerScale (G := G × X) B U b R σ hR hσ L₀
    let sides := layerSamplerSides (G := G × X) B U b R scale.value
    let sites := layerSamplerIntegerBox B U b scale
    let F := PrincipalTupleIndex B (layerSamplerDegree I n)
    let a := kernelAnchorScale G X F
    let η := kernelNoiseScale G X F
    let spatialSides := fun k => (sides k : ℝ)
    let anchor := kernelSpatialAnchor N spatialSides a
    let W := kernelSpatialWidths N spatialSides η τ
    let hW := kernelSpatialWidths_pos N (fun i => Nat.lt_of_lt_of_le (by decide : 0 < 4) (_hN i))
      spatialSides (fun k => by
        dsimp only [spatialSides, sides]
        exact_mod_cast layerSamplerSides_pos B U b R scale.positive k)
      (kernelSpatial_scales G X F).2.1 _hτ
    let center := coefficientConstantCenter U x
    let D := translatedSelectedPhysicalDensity (G := G × X) B U b hb o R σ hR hσ L₀ center p hm
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
        noninjectivityIndicator (fun q : sites => integerPhysicalSite q.val z)) ≤ δ ∧
      (∀ z, 0 < (law z).toReal →
        (∀ g, (matrixSupCLM (normalizedKernelBlock N spatialSides z g)).IsInvertible ∧
          ‖(matrixSupCLM (normalizedKernelBlock N spatialSides z g)).inverse‖ ≤
            32 * ((Fintype.card (LayerSamplerVariables (G × X) I n B) : ℝ) + 1)) ∧
        (∀ root : LayerSamplerVariables (G × X) I n B → ℤ,
          (∀ k, |(root k : ℝ)| ≤ spatialSides k) → integerPhysicalSite root z ∈ integerBox N) ∧
        (∀ root : LayerSamplerVariables (G × X) I n B → ℤ,
          (∀ k, |(root k : ℝ)| ≤ spatialSides k) → ∀ i,
          |∑ f : F, (root (.inr f) : ℝ) * (z (some (.inr f), i) : ℝ)| ≤ τ * (N i : ℝ) / 16)) := by
  obtain ⟨a₀, _, hgeometry⟩ := exists_centered_full_parameter_anchored_geometry m
  obtain ⟨A, hA, hthreshold⟩ := exists_kernelSamplerThreshold m a₀
  refine ⟨A, hA, ?_⟩
  intro X G _ _ _ _ _ I _ n B _ J _ U b hb o _ _ _ _ μ _ _ ν _ _
    R σ hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall L₀ P δ hP hδ hδsmall hδP
    hX hK hI hn hJ hAP hL₀P hCP hVP hRP hσP τ hτ hτ1 hτP x p hp hm stride hs Rrank S
    hS hSP hstride N hN hsize hrank hRrank T hT
  let scale := selectedLayerSamplerScale (G := G × X) B U b R σ hR hσ L₀
  let sides := layerSamplerSides (G := G × X) B U b R scale.value
  let spatialSides := fun k => (sides k : ℝ)
  let F := PrincipalTupleIndex B (layerSamplerDegree I n)
  let a := kernelAnchorScale G X F
  let η := kernelNoiseScale G X F
  let anchor := kernelSpatialAnchor N spatialSides a
  let W := kernelSpatialWidths N spatialSides η τ
  have hpositive (i) : 0 < N i := by have := hN i; omega
  have hsidepos (k) : 0 < spatialSides k := by
    dsimp only [spatialSides, sides]
    exact_mod_cast layerSamplerSides_pos B U b R scale.positive k
  have hLpos : (0 : ℝ) < scale.value := by exact_mod_cast scale.positive
  have hL1 : (1 : ℝ) ≤ scale.value := by exact_mod_cast scale.positive
  have hsidele (k) : spatialSides k ≤ (scale.value : ℝ) := by
    dsimp only [spatialSides, sides]
    exact_mod_cast layerSamplerSides_le B U b R scale.positive k
  have hscales := kernelSpatial_scales G X F
  have hW := kernelSpatialWidths_pos N hpositive spatialSides hsidepos hscales.2.1 hτ
  let Q := selectedFourierInputBudget m P
  let P' := kernelSamplerBudget m P
  have hP' : 0 ≤ P' := kernelSamplerBudget_nonneg m hP
  have hPP' : P ≤ P' := le_kernelSamplerBudget m hP
  have heP : Real.exp P ≤ Real.exp P' := Real.exp_le_exp.mpr hPP'
  have hL : (scale.value : ℝ) ≤ Real.exp Q :=
    selectedLayerSamplerScale_input_bound B U b R σ hR hσ L₀ hP hK hn hRP hσP hAP hL₀P
  let ρ := τ * η / (scale.value : ℝ)
  have hρ := kernelSpatial_relative_width_budget hK hX hτ hτP hLpos hL
  have hwidth (z) : ρ * (N z.2 : ℝ) ≤ W z :=
    kernelSpatialWidths_lower_bound N spatialSides hsidepos hL1 hsidele
      hscales.2.1.le hscales.2.2.1 hτ.le hτ1 z
  have hNlarge (i) : Real.exp (Q + 2 * P + 64) ≤ (N i : ℝ) := by
    have hb : Q + 2 * P + 64 ≤ P' := by dsimp [P', kernelSamplerBudget, Q]; linarith
    exact (Real.exp_le_exp.mpr hb).trans ((hthreshold P hP).1.trans (hsize i))
  have hround := kernelSpatial_rounding_scale hK hX hLpos hL N hNlarge spatialSides hsidepos hsidele
  have hresult := hgeometry B U b hb o μ ν R σ hR hσ hσ1 C V hC hV Cinv hCinv hchart hsmall L₀
    hP' hδ hδsmall (hδP.trans heP) (hX.trans hPP') (hK.trans hPP')
    (fun j => (hI j).trans hPP') (fun j => (hn j).trans hPP') (fun j => (hJ j).trans hPP')
    (hAP.trans heP) (hL₀P.trans heP) (fun j => (hCP j).trans heP) (fun j => (hVP j).trans heP)
    (fun j => (hRP j).trans heP) (fun j => (hσP j).trans heP)
    x anchor p hp hm stride hs hS (hSP.trans heP) hstride hρ.1 hρ.2 (fun i => (N i : ℝ))
    (fun i => (hthreshold P hP).2.trans (hsize i)) hrank ((hthreshold P hP).2.trans hRrank)
    T hT W hW hwidth
  obtain ⟨hL₀, _, hsides, hmax, hsites, hZ, hD, hclose, hlower, hupper,
    hsupport, hlifts, hcollision⟩ := hresult
  refine ⟨hL₀, hL, hsides, hmax, hsites, hZ, hD, hclose, hlower, hupper,
    hsupport, hlifts, hcollision, ?_⟩
  intro z hz
  exact canonicalKernelSpatial_support N hN spatialSides hsidepos hτ hτ1 hround stride T hZ
    (translatedSelectedPhysicalDensity (G := G × X) B U b hb o R σ hR hσ L₀
      (coefficientConstantCenter U x) p hm)
    (translatedSelectedPhysicalDensity_nonneg (G := G × X) B U b hb o R σ hR hσ L₀
      (coefficientConstantCenter U x) p hm) hD z hz

end Erdos3.VectorPolynomial

end

end OAI

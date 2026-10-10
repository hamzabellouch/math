import OAI.Combinatorics.Progressions.Estimates.AllocatedFixedPositiveComparison
import OAI.Combinatorics.Progressions.Estimates.AllocatedTrimmedNormalization

namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

theorem exists_allocated_positive_spatial_approximation (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {G : Type*} [Fintype G] [DecidableEq G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    [DecidableEq (LayerSamplerVariables G I n B)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox (Fin q) S.value)
    {P W κ : ℝ} (_hP : 0 ≤ P) (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P) (_hW : 0 ≤ W)
    (_hbudget : allocatedPhysicalRootBudget B U basis S c ≤ W)
    (_hWP : W ≤ Real.exp P) (_hL : (S.value : ℝ) ≤ Real.exp P)
    (selection : Fin q ↪ G) (_hκ : 0 < κ) {M : ℕ}
    (_hx : GoodScalarKernelTuple selection κ M x) (_hMP : (M : ℝ) ≤ Real.exp P)
    (_hκP : κ⁻¹ ≤ Real.exp P),
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ Real.exp ((P + A) ^ A) ∧
    ∀ (y : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin q) (allocatedPrincipalSides B U basis S))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (SiteTorus (Finset (Fin q)) U)] [BorelSpace (SiteTorus (Finset (Fin q)) U)]
    (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ V j)
    (_hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    (_hmSize : (m : ℝ) ≤ P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)],
    let density := allocatedCoefficientDensity B U basis hb o hR hσ S
    let cap := (allocatedAmbientFactorCap (G := G) B R σ S.value V : ℝ) ^
      Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
    let root := allocatedPhysicalCubeRoot B U basis S c x y
    let dirs := allocatedPhysicalCubeDirections B U basis S x y
    let F := euclideanCoefficientJetMap U root dirs
      (fun j => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q)))
    let cover := quotientIntegerCover (coefficientIntegerLattice U) D
    let ξ := Measure.pi (fun j => Measure.pi (fun _ : BoundedBooleanJet (Fin q) (j.val + 1) => ν j))
    ∃ f : EuclideanJetLayers U (fun j => BoundedBooleanJet (Fin q) (j.val + 1)) → ℝ,
      Continuous f ∧ (∀ z, f z ∈ Set.Icc (0 : ℝ) cap) ∧ Integrable f ξ ∧
      (∫ z, f z ∂ξ) = 1 ∧
      (realDensityMeasure μ (fun z => density (cover z))).map F = realDensityMeasure ξ f ∧
      ∀ {X : Type*} [Fintype X] [DecidableEq X]
    (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (base : X → ℤ)
    (stride : X → ℕ) (hs : ∀ d, 0 < stride d) (_hsP : ∀ d, (stride d : ℝ) ≤ Real.exp P)
    {τ : ℝ} (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (_hsize : ∀ d, Real.exp ((P + A) ^ A) ≤ (N d : ℝ))
    {rank : ℝ} (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (_hRank : Real.exp ((P + A) ^ A) ≤ rank)
    (test : Finset (Fin q) → (X → ℝ) → ℂ) (_htest : ∀ s v, ‖test s v‖ ≤ 1)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty)
    {Z : ℝ} (_hZnorm : 0 < Z) (_hZi : Z⁻¹ ≤ Real.exp P),
    let V := trimmedSpatialWidths (K := LayerSamplerVariables G I n B) W τ N
    let root := allocatedPhysicalCubeRoot B U basis S c x y
    let dirs := allocatedPhysicalCubeDirections B U basis S x y
    let pa := fun j => translate (fun d => (base d : ℝ)) (p j)
    let hma := fun j => coefficients_translate_mem (U j) (fun d => (base d : ℝ)) (p j) (hm j)
    let sel := selection.trans (Function.Embedding.inl : G ↪ LayerSamplerVariables G I n B)
    let out := fun d => physicalSpatialOutputScale (Fin q)
      (trimmedSpatialRootScale τ N stride d) (trimmedSpatialSlopeScale W τ N stride d) S.value
    ∃ (hV : ∀ z, 0 < V z) (hOut : ∀ d i, 0 < out d i)
      (hpivot : ((physicalCubeCoefficient root dirs).submatrix id (physicalCubePivotIndex sel)).det ≠ 0)
      (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T V z),
      ‖(∑' z, ((selectedResidueSmoothPMF stride T V hV hZ z).toReal : ℂ) *
        (physicalCubeSiteTest test (physicalCubeRootDifferences root dirs base z) *
          (density (affineSampleCoefficientTorus U pa hma (fun k d => (z (k, d) : ℝ))) : ℂ))) / (Z : ℂ) -
        (∑ r : T, (selectedResidueCellWeight stride T V r : ℂ) *
          ∫ v, (shiftedProductGridProxy (fun _ : X => physicalCubeCoefficient root dirs)
            (fun _ => physicalCubePivotIndex sel) (fun _ => hpivot)
            (residueProfileCenter (boundedColumnResidueRepresentative stride r.val) stride)
            (residueProfileWidth stride V) out (residueProfileWidth_pos stride V hs hV) hOut v : ℂ) *
            physicalCubePositiveTest U D p hm f test
              (physicalResidueReconstruct root dirs base
                (boundedColumnResidueRepresentative stride r.val) stride v) ∂Measure.count) / (Z : ℂ)‖ ≤
          Real.exp (-P) := by
  classical
  obtain ⟨A₀, _, hcomparison⟩ := exists_allocated_fixed_positive_comparison m q
  obtain ⟨b, _, hbnd⟩ := exists_positiveComparisonDataBudget_bound m q
  obtain ⟨A, hA, hbudget⟩ := exists_natPolynomial_eval_budget
    (((Polynomial.X + Polynomial.C b) ^ b + Polynomial.C A₀) ^ A₀)
  refine ⟨A, hA, ?_⟩
  intro G _ _ I _ n B _ _ J _ U basis R σ S c x P W κ hP hK hW hroot hWP hL
    selection hκ M hx hMP hκP
  let Q := positiveComparisonDataBudget m q P
  have hbounds := positiveComparisonDataBudget_bounds m q hP
  have hQ : 0 ≤ Q := hbounds.1
  have hPQ : P ≤ Q := hbounds.2.1
  have hExp := Real.exp_le_exp.mpr hPQ
  have hcut : (Q + A₀) ^ A₀ ≤ (P + A) ^ A := by
    have hbase : Q + (A₀ : ℝ) ≤ (P + b) ^ b + A₀ := by
      have h := hbnd P hP
      change Q ≤ (P + b) ^ b at h
      linarith
    calc
      _ ≤ ((P + b) ^ b + A₀) ^ A₀ :=
        pow_le_pow_left₀ (add_nonneg hQ (Nat.cast_nonneg A₀)) hbase A₀
      _ ≤ _ := by simpa [Polynomial.eval₂_pow] using hbudget P hP
  obtain ⟨D, hD, hDP, hfamily⟩ := hcomparison B U basis S c x hQ (hK.trans hPQ) hW hroot
    (hWP.trans hExp) (hL.trans hExp) selection hκ hx (hMP.trans hExp) (hκP.trans hExp)
  refine ⟨D, hD, hDP.trans (Real.exp_le_exp.mpr hcut), ?_⟩
  intro y _ _ _ _ _ _ hb o hR hσ C Vcap hC hVcap hσ1 Cinv hCinv hchart hsmallChart
    hmSize hRP hσP hcount hI hn hJ hAP hCP hVP μ _ _ ν _ _ density cap root dirs Fmap cover ξ
  obtain ⟨hcap, F, inst, frequency, coeff, hfreq, hcoeff, happ⟩ :=
    exists_allocated_positive_fourier_data B U basis hb o S C Vcap hC hVcap q
      hR hσ hσ1 Cinv hCinv hchart hsmallChart hP hmSize hK hRP hσP hcount hI hn hJ hAP hL hCP hVP
  let _ := inst
  obtain ⟨f, hfc, hfb, hfi, hfmass, hflaw, hcomp⟩ :=
    hfamily y hb o hR hσ C Vcap hC hVcap hσ1 Cinv hCinv hchart hsmallChart μ ν
  refine ⟨f, hfc, hfb, hfi, hfmass, hflaw, ?_⟩
  intro X _ _ hX hdim p hp hm base stride hs hsP τ hτ hτP N hsize rank hrank hRank test htest T hT Z hZnorm hZi
  let bcap := allocatedFourierLogBudget m (2 * P + 4)
  have hbcap : 0 ≤ bcap := allocatedFourierLogBudget_nonneg m (by linarith)
  have hacc := positiveComparisonAccuracy_spec q P bcap
  have hηQ : (positiveProjectionAccuracy P)⁻¹ ≤ Real.exp Q := by
    rw [hacc.2.2.1]
    exact Real.exp_le_exp.mpr hbounds.2.2.1
  have hεQ : (positiveSpatialAccuracy q P bcap)⁻¹ ≤ Real.exp Q := by
    rw [hacc.2.2.2]
    exact Real.exp_le_exp.mpr hbounds.2.2.2.2
  have herr := positiveComparison_error_budget q hP hbcap hX hK hcap hZnorm hZi
  obtain ⟨hV, hOut, hpivot, hZ, he⟩ := hcomp (hX.trans hPQ) (hdim.trans hPQ) frequency hfreq coeff hcoeff
    p hp hm base stride hs (fun d => (hsP d).trans hExp) hτ (hτP.trans hExp)
    hacc.1 hηQ hacc.2.1 hεQ N (fun d => (Real.exp_le_exp.mpr hcut).trans (hsize d))
    herr.1 hrank ((Real.exp_le_exp.mpr hcut).trans hRank) test htest T hT hacc.1.le happ hZnorm
  exact ⟨hV, hOut, hpivot, hZ, he.trans herr.2⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

theorem exists_allocated_normalized_spatial_approximation (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {G : Type*} [Fintype G] [DecidableEq G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    [DecidableEq (LayerSamplerVariables G I n B)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox (Fin q) S.value)
    {P W κ : ℝ} (_hP : 0 ≤ P) (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P) (_hW : 0 ≤ W)
    (_hbudget : allocatedPhysicalRootBudget B U basis S c ≤ W)
    (_hWP : W ≤ Real.exp P) (_hL : (S.value : ℝ) ≤ Real.exp P)
    (selection : Fin q ↪ G) (_hκ : 0 < κ) {M : ℕ}
    (_hx : GoodScalarKernelTuple selection κ M x) (_hMP : (M : ℝ) ≤ Real.exp P)
    (_hκP : κ⁻¹ ≤ Real.exp P),
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ Real.exp ((P + A) ^ A) ∧
    ∀ (y : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin q) (allocatedPrincipalSides B U basis S))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (SiteTorus (Finset (Fin q)) U)] [BorelSpace (SiteTorus (Finset (Fin q)) U)]
    (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ V j)
    (_hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    (_hmSize : (m : ℝ) ≤ P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)],
    let density := allocatedCoefficientDensity B U basis hb o hR hσ S
    let cap := (allocatedAmbientFactorCap (G := G) B R σ S.value V : ℝ) ^
      Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
    let root := allocatedPhysicalCubeRoot B U basis S c x y
    let dirs := allocatedPhysicalCubeDirections B U basis S x y
    let F := euclideanCoefficientJetMap U root dirs
      (fun j => (Subtype.val : BoundedBooleanJet (Fin q) (j.val + 1) → Finset (Fin q)))
    let cover := quotientIntegerCover (coefficientIntegerLattice U) D
    let ξ := Measure.pi (fun j => Measure.pi (fun _ : BoundedBooleanJet (Fin q) (j.val + 1) => ν j))
    ∃ f : EuclideanJetLayers U (fun j => BoundedBooleanJet (Fin q) (j.val + 1)) → ℝ,
      Continuous f ∧ (∀ z, f z ∈ Set.Icc (0 : ℝ) cap) ∧ Integrable f ξ ∧
      (∫ z, f z ∂ξ) = 1 ∧
      (realDensityMeasure μ (fun z => density (cover z))).map F = realDensityMeasure ξ f ∧
      ∀ {X : Type*} [Fintype X] [DecidableEq X]
    (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (base : X → ℤ)
    (stride : X → ℕ) (hs : ∀ d, 0 < stride d) (_hsP : ∀ d, (stride d : ℝ) ≤ Real.exp P)
    {τ : ℝ} (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (_hsize : ∀ d, Real.exp ((P + A) ^ A) ≤ (N d : ℝ))
    {rank : ℝ} (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (_hRank : Real.exp ((P + A) ^ A) ≤ rank)
    (test : Finset (Fin q) → (X → ℝ) → ℂ) (_htest : ∀ s v, ‖test s v‖ ≤ 1)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty)
    (bases : Finset (X → ℤ)) (_hbases : bases.Nonempty),
    let V := trimmedSpatialWidths (K := LayerSamplerVariables G I n B) W τ N
    let root := allocatedPhysicalCubeRoot B U basis S c x y
    let dirs := allocatedPhysicalCubeDirections B U basis S x y
    let pa := fun j => translate (fun d => (base d : ℝ)) (p j)
    let hma := fun j => coefficients_translate_mem (U j) (fun d => (base d : ℝ)) (p j) (hm j)
    let sel := selection.trans (Function.Embedding.inl : G ↪ LayerSamplerVariables G I n B)
    let out := fun d => physicalSpatialOutputScale (Fin q)
      (trimmedSpatialRootScale τ N stride d) (trimmedSpatialSlopeScale W τ N stride d) S.value
    let baseDensity := fun (a : X → ℤ) z => density (affineSampleCoefficientTorus U
      (fun j => translate (fun d => (a d : ℝ)) (p j))
      (fun j => coefficients_translate_mem (U j) (fun d => (a d : ℝ)) (p j) (hm j))
      (fun k d => (z (k, d) : ℝ)))
    let Z := selectedJointDensityMass bases stride T V baseDensity
    ∃ (hV : ∀ z, 0 < V z) (hOut : ∀ d i, 0 < out d i)
      (hpivot : ((physicalCubeCoefficient root dirs).submatrix id (physicalCubePivotIndex sel)).det ≠ 0)
      (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T V z),
      (|Z - 1| ≤ Real.exp (-P) ∧ Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ 0 < Z ∧ Z⁻¹ ≤ 2) ∧
      ‖(∑' z, ((selectedResidueSmoothPMF stride T V hV hZ z).toReal : ℂ) *
        (physicalCubeSiteTest test (physicalCubeRootDifferences root dirs base z) *
          (density (affineSampleCoefficientTorus U pa hma (fun k d => (z (k, d) : ℝ))) : ℂ))) / (Z : ℂ) -
        (∑ r : T, (selectedResidueCellWeight stride T V r : ℂ) *
          ∫ v, (shiftedProductGridProxy (fun _ : X => physicalCubeCoefficient root dirs)
            (fun _ => physicalCubePivotIndex sel) (fun _ => hpivot)
            (residueProfileCenter (boundedColumnResidueRepresentative stride r.val) stride)
            (residueProfileWidth stride V) out (residueProfileWidth_pos stride V hs hV) hOut v : ℂ) *
            physicalCubePositiveTest U D p hm f test
              (physicalResidueReconstruct root dirs base
                (boundedColumnResidueRepresentative stride r.val) stride v) ∂Measure.count) / (Z : ℂ)‖ ≤
          Real.exp (-P) := by
  classical
  obtain ⟨Ac, _, hcomparison⟩ := exists_allocated_positive_spatial_approximation m q
  obtain ⟨An, _, hnormalization⟩ := exists_allocated_trimmed_normalization m
  obtain ⟨A, hA, hbudget⟩ := exists_natPolynomial_eval_budget
    ((Polynomial.X + Polynomial.C (2 + Ac)) ^ Ac + (Polynomial.X + Polynomial.C An) ^ An)
  refine ⟨A, hA, ?_⟩
  intro G _ _ I _ n B _ _ J _ U basis R σ S c x P W κ hP hK hW hroot hWP hL
    selection hκ M hx hMP hκP
  have hP2 : 0 ≤ P + 2 := by linarith
  have hPP2 : P ≤ P + 2 := by linarith
  have hExp := Real.exp_le_exp.mpr hPP2
  have hsum : (P + 2 + Ac) ^ Ac + (P + An) ^ An ≤ (P + A) ^ A := by
    have h := hbudget P hP
    simpa [Polynomial.eval₂_pow, add_assoc] using h
  have hcompCut : (P + 2 + Ac) ^ Ac ≤ (P + A) ^ A := by
    linarith [pow_nonneg (add_nonneg hP (Nat.cast_nonneg An)) An]
  have hnormCut : (P + An) ^ An ≤ (P + A) ^ A := by
    linarith [pow_nonneg (add_nonneg hP2 (Nat.cast_nonneg Ac)) Ac]
  obtain ⟨D, hD, hDP, hfamily⟩ := hcomparison B U basis S c x hP2 (hK.trans hPP2) hW hroot
    (hWP.trans hExp) (hL.trans hExp) selection hκ hx (hMP.trans hExp) (hκP.trans hExp)
  refine ⟨D, hD, hDP.trans (Real.exp_le_exp.mpr hcompCut), ?_⟩
  intro y _ _ _ _ _ _ hb o hR hσ C Vcap hC hVcap hσ1 Cinv hCinv hchart hsmall
    hmSize hRP hσP hcount hI hn hJ hAP hCP hVP μ _ _ ν _ _ density cap root dirs Fmap cover ξ
  obtain ⟨f, hfc, hfb, hfi, hfmass, hflaw, hcomp⟩ :=
    hfamily y hb o hR hσ C Vcap hC hVcap hσ1 Cinv hCinv hchart hsmall
      (hmSize.trans hPP2) (fun j => (hRP j).trans hExp) (fun j => (hσP j).trans hExp)
      (fun j => (hcount j).trans hPP2) (fun j => (hI j).trans hPP2)
      (fun j => (hn j).trans hPP2) (fun j => (hJ j).trans hPP2)
      (hAP.trans hExp) (fun j => (hCP j).trans hExp) (fun j => (hVP j).trans hExp) μ ν
  refine ⟨f, hfc, hfb, hfi, hfmass, hflaw, ?_⟩
  intro X _ _ hX hdim p hp hm base stride hs hsP τ hτ hτP N hsize rank hrank hRank
    test htest T hT bases hbases V root' dirs' pa hma sel out baseDensity Z
  obtain ⟨_, _, _, hglobal⟩ := hnormalization B U basis S hb o μ ν
    hR hσ hσ1 C Vcap hC hVcap Cinv hCinv hchart hsmall hP hmSize hK hX hdim
    hRP hσP hcount hI hn hJ hAP hL hCP hVP p hp hm stride hs hsP hW hWP hτ hτP
    N (fun d => (Real.exp_le_exp.mpr hnormCut).trans (hsize d)) hrank
    ((Real.exp_le_exp.mpr hnormCut).trans hRank) T hT
  have hnormal := hglobal bases hbases
  change |Z - 1| ≤ Real.exp (-P) ∧ Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧
    0 < Z ∧ Z⁻¹ ≤ 2 at hnormal
  have hZi : Z⁻¹ ≤ Real.exp (P + 2) :=
    hnormal.2.2.2.trans (by linarith [Real.add_one_le_exp (P + 2)])
  obtain ⟨hV, hOut, hpivot, hZ, he⟩ := hcomp (hX.trans hPP2) (hdim.trans hPP2)
    p hp hm base stride hs (fun d => (hsP d).trans hExp) hτ (hτP.trans hExp)
    N (fun d => (Real.exp_le_exp.mpr hcompCut).trans (hsize d)) hrank
    ((Real.exp_le_exp.mpr hcompCut).trans hRank) test htest T hT hnormal.2.2.1 hZi
  exact ⟨hV, hOut, hpivot, hZ, hnormal,
    he.trans (Real.exp_le_exp.mpr (by linarith))⟩

end Erdos3.VectorPolynomial

end

end OAI

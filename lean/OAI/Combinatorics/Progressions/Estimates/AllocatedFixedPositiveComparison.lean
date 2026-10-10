import OAI.Combinatorics.Progressions.Geometry.AllocatedPositiveSpatialComparison

namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

theorem exists_allocated_fixed_positive_comparison (m q : ℕ) :
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
    {F : Type*} [Fintype F]
    (frequency : F → ∀ j, (LayerSamplerVariables G I n B →₀ ℕ) → J j → ℤ)
    (_hfrequency : ∀ a j d, d.degree ≤ j.val + 1 → ∀ t, |(frequency a j d t : ℝ)| ≤ Real.exp P)
    (coeff : F → ℂ) (_hcoeff : (∑ a, ‖coeff a‖) ≤ Real.exp P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (base : X → ℤ)
    (stride : X → ℕ) (hs : ∀ d, 0 < stride d) (_hsP : ∀ d, (stride d : ℝ) ≤ Real.exp P)
    {τ δ ε : ℝ} (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hδ : 0 < δ) (_hδP : δ⁻¹ ≤ Real.exp P) (_hε : 0 < ε) (_hεP : ε⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (_hsize : ∀ d, Real.exp ((P + A) ^ A) ≤ (N d : ℝ))
    (_hsmall : (∑ _d : X, shiftedMatrixCountFactor (Unit ⊕ Fin q)
      (Option (LayerSamplerVariables G I n B)) * ε) ≤ 1)
    {rank : ℝ} (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (_hRank : Real.exp ((P + A) ^ A) ≤ rank)
    (test : Finset (Fin q) → (X → ℝ) → ℂ) (_htest : ∀ s v, ‖test s v‖ ≤ 1)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty)
    {η : ℝ} (_hη : 0 ≤ η)
    (_happrox : ∀ z, ‖(density z : ℂ) - coefficientTorusFourierSum U frequency coeff z‖ ≤ η)
    {Z : ℝ} (_hZnorm : 0 < Z),
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
          (2 * η + δ + cap * (2 * ∑ _d : X,
            shiftedMatrixCountFactor (Unit ⊕ Fin q) (Option (LayerSamplerVariables G I n B)) * ε)) / Z := by
  classical
  obtain ⟨A₀, _, hcover⟩ := exists_allocated_fixed_positive_density m q
  obtain ⟨A₁, _, hcomparison⟩ := exists_allocated_positive_spatial_comparison m q
  obtain ⟨A, hA, hbudget⟩ := exists_natPolynomial_eval_budget
    ((Polynomial.X + Polynomial.C A₀) ^ A₀ + (Polynomial.X + Polynomial.C A₁) ^ A₁)
  refine ⟨A, hA, ?_⟩
  intro G _ _ I _ n B _ _ J _ U basis R σ S c x P W κ hP hK hW hroot hWP hL
    selection hκ M hx hMP hκP
  have hsum : (P + A₀) ^ A₀ + (P + A₁) ^ A₁ ≤ (P + A) ^ A := by
    simpa [Polynomial.eval₂_pow] using hbudget P hP
  have hc0 : (P + A₀) ^ A₀ ≤ (P + A) ^ A := by
    linarith [pow_nonneg (add_nonneg hP (Nat.cast_nonneg A₁)) A₁]
  have hc1 : (P + A₁) ^ A₁ ≤ (P + A) ^ A := by
    linarith [pow_nonneg (add_nonneg hP (Nat.cast_nonneg A₀)) A₀]
  have hG : (Fintype.card G : ℝ) ≤ P :=
    (Nat.cast_le.mpr (allocatedKernelVariables_card_le_variables (G := G) B)).trans hK
  obtain ⟨D, hD, hDP, hfamily⟩ := hcover B U basis S c x hP hG
    (fun g => (allocatedPhysicalRootBudget_constant_le B U basis S c (.inl g)).trans (hroot.trans hWP))
    hL hx.2
  refine ⟨D, hD, hDP.trans (Real.exp_le_exp.mpr hc0), ?_⟩
  intro y _ _ _ _ _ _ hb o hR hσ C Vcap hC hVcap hσ1 Cinv hCinv hchart hsmallChart
    μ _ _ ν _ _ density cap root dirs Fmap cover ξ
  obtain ⟨f, hfc, hfb, hfi, hfmass, hflaw, hpositive⟩ :=
    hfamily y hb o hR hσ C Vcap hC hVcap hσ1 Cinv hCinv hchart hsmallChart μ ν
  refine ⟨f, hfc, hfb, hfi, hfmass, hflaw, ?_⟩
  intro X _ _ hX hdim F _ frequency hfrequency coeff hcoeff p hp hm base stride hs hsP
    τ δ ε hτ hτP hδ hδP hε hεP N hsize hsmall rank hrank hRank test htest T hT η hη happrox Z hZnorm
  let pa := fun j => translate (fun d => (base d : ℝ)) (p j)
  let hma := fun j => coefficients_translate_mem (U j) (fun d => (base d : ℝ)) (p j) (hm j)
  have hpa (j) : DegreeLE (1 : X → ℕ) (j.val + 1) (pa j) :=
    degreeLE_translate (1 : X → ℕ) (fun _ => by norm_num) _ (p j) (hp j)
  have happ (z) : ‖coefficientTorusFourierSum U frequency coeff z - (density z : ℂ)‖ ≤ η := by
    simpa only [norm_sub_rev] using happrox z
  exact hcomparison B U basis S c x hP hK hW hroot hWP hL selection hκ hx hMP hκP y
    hX hdim frequency hfrequency coeff hcoeff p hp hm base stride hs hsP hτ hτP hδ hδP hε hεP
    N (fun d => (Real.exp_le_exp.mpr hc1).trans (hsize d)) hsmall hrank
    ((Real.exp_le_exp.mpr hc1).trans hRank) test htest T hT density D f hfb hη happrox hZnorm
    (fun z => hpositive frequency coeff happ pa hpa hma (fun k d => (z (k, d) : ℝ)))

end Erdos3.VectorPolynomial

end

end OAI

import OAI.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateGeneratedFreezingSuccessor

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realChartSubstitute realPolynomialGroupMap associatedGradedMap gradedRefiltrationMap
  PolynomialRationalGrid PolynomialSlowBound

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalCandidateProblem

variable {L M : Type} {nMarkedBasis : ℕ} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {d f : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L 1 d}
    (Fmark : RationalFilteredNilmanifold M 1 f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    {marked : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P₀ : AllocatedExternalCandidateProblem (E := E) A D Fmark.filtration φ marked
      observable weight cost massThreshold scoreThreshold)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : P₀.productive, (P₀.chart z).keep = keep)

variable (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    {inputDenominator k e : ℕ} {pGeo : ℝ}
    (sectionMap : M →ₗ[ℚ] L)
    (hSectionFilt : ∀ j, ∀ y ∈ Fmark.filtration.layer j, sectionMap y ∈ D.filtration.layer j)
    (c : Basis (Fin nMarkedBasis) ℚ M)
    (ν : Fin nMarkedBasis → ℕ)
    (hF : ∀ j, Fmark.filtration.layer j = span ℚ (c '' {i | j ≤ ν i}))
    {g : (Fmark.filtration.realification.adaptedPolynomialFiltration
      (fullTaggedVariableWeight (X := X) J)).Group}
    {EF RF : Fmark.filtration.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J)}
    (factors : GlobalMarkedNativeFactors Fmark.filtration c ν hF (fullTaggedVariableWeight J)
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)) g EF RF)
    {slow : ℝ} {denominator : ℕ}
    (reset : AllocatedExternalGlobalNativeResetFamily
      Fmark φ hφ P₀ keep hkeep W factors slow denominator)
    (tests : (X → ℤ) → D.Niltest (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1))
    (htests : ∀ x, (tests x).observable = observable x)
    (hσ1 : ∀ j, σ j ≤ 1) (H : Fin m → ℝ) (hH : ∀ j, 0 ≤ H j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ H j * ‖v‖)
    (hsmall : ∀ j, H j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))

include htests hσ1 H hH hchart hsmall hp

theorem conclusion_of_generatedCovered_nativeReset_degreeOne
    {Bweight Bobs Lip densityCost p budgetLog massLog : ℝ}
    (C : ℕ) (hp0 : 0 ≤ p) (hC : 2 ≤ C)
    (dictionary : RationalFilteredNilmanifold.ExternalMarkedAffineSliceFreezing.Dictionary
      (X := X → ℤ) D Fmark.filtration c φ hφ
      (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1) sectionMap hSectionFilt denominator
      (fun i : { i : LayerSamplerVariables G I n B // keep i } => (A.sides i.val : ℝ)) slow (finiteFreezingInitialPrecision p) (Real.exp budgetLog))
    (hslowMark : ∀ z, Fmark.filtration.PolynomialSlowBound c (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1)
      (fun i : { i : LayerSamplerVariables G I n B // keep i } => (A.sides i.val : ℝ)) slow (Fmark.filtration.weightedAdaptedRealChartHom (fullTaggedVariableWeight J) (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1) (integerSampledRealChart ((P₀.withKeep keep hkeep).chart z).integerChart) ((P₀.withKeep keep hkeep).chart z).integerChart_support factors.left))
    (hgrid : Fmark.filtration.PolynomialRationalGrid c
      (fullTaggedVariableWeight (X := X) J) denominator factors.right)
    (hdensity : ∀ z : (P₀.withKeep keep hkeep).productive,
      IsDenseCommonStrideBox
        (fun i : ((P₀.withKeep keep hkeep).chart z).Variables => A.sides i.val)
        densityCost ((P₀.withKeep keep hkeep).chart z).slice.integerPoints)
    (hfloor : ∀ i : { i : LayerSamplerVariables G I n B // keep i },
      Real.exp densityCost * max 2 (2 * (Real.exp budgetLog) * max 1 (Real.exp budgetLog)) ≤ (A.sides i.val : ℝ))
    (hBweight : 0 ≤ Bweight) (hBobs : 0 ≤ Bobs) (hLip : 0 ≤ Lip)
    (hweight : ∀ x, ‖weight x‖ ≤ Bweight)
    (hnorm : ∀ x, ((tests x).normBound : ℝ) ≤ Bobs)
    (hlip : ∀ x, ((tests x).lipBound : ℝ) ≤ Lip)
    (hweightCap : Bweight ≤ Real.exp p) (hobsCap : Bobs ≤ Real.exp p)
    (hlipCap : Lip ≤ Real.exp p) (hscoreInput : Real.exp (-p) ≤ scoreThreshold)
    (hcostInput : cost ≤ (p + C) ^ C) (hdensityInput : densityCost ≤ (p + C) ^ C)
    (hbudgetLog0 : 0 ≤ budgetLog) (hbudgetLog : budgetLog ≤ (p + C) ^ C)
    (hcount : (Fintype.card { i : LayerSamplerVariables G I n B // keep i } : ℝ) ≤ (p + C) ^ C)
    (hmassLog : massLog ≤ (p + C) ^ C) (hmassInput : Real.exp (-massLog) ≤ massThreshold)
    (hsection : Function.RightInverse sectionMap φ)
    (dw : Fin d → ℕ)
    (hdb : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ dw i}))
    (hW : BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis dw hdb) dw W.toSubmodule)
    (hsurj : ∀ j, ∀ y ∈ Fmark.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    (hξ1 : ξ ≤ 1)
    (ℓ : ℝ≥0) (hpGeo : 1 ≤ pGeo) (hDGeo : D.GeometryComplexityLE pGeo)
    (hpGeoInput : p ≤ pGeo)
    (hpGeoRec : pGeo ≤ finiteFreezingRecursiveParameter C p)
    (hcoveredRec : ((pGeo + RationalFilteredNilmanifold.allocatedCoveredLowerExponent 0 k) ^ RationalFilteredNilmanifold.allocatedCoveredLowerExponent 0 k) ≤ finiteFreezingRecursiveParameter C p)
    (hℓ : (ℓ : ℝ) ≤ Real.exp pGeo)
    (pRight : ℝ) (hpRight : 0 ≤ pRight) (hDRight : D.GeometryComplexityLE pRight)
    (hinputDenominator : 0 < inputDenominator)
    (hinputDenominatorBound : (inputDenominator : ℝ) ≤ Real.exp pRight)
    (hRightBudget : (pRight + RationalFilteredNilmanifold.allocatedRightDictionaryExponent 1) ^
      RationalFilteredNilmanifold.allocatedRightDictionaryExponent 1 ≤ pGeo)
    (hOriginalLip : ∀ x, letI := D.metricSpace; LipschitzWith ℓ (observable x))
    (hpositive : ∀ x y, (observable x y).im = 0 ∧
      0 ≤ (observable x y).re ∧ (observable x y).re ≤ 1)
    (hFGeo : Fmark.GeometryComplexityLE pGeo)
    {Generator : Type} [Fintype Generator]
    (generators : Generator → D.filtration.AssociatedGraded)
    (hspan : span ℚ (Set.range generators) = W.toSubmodule)
    (hgeneratorCount : (Fintype.card Generator : ℝ) ≤ pGeo)
    (hmarkedBasis : ∀ i j, rationalLogHeight (Fmark.basis.repr (c i) j) ≤ pGeo)
    (hmarkHeight : ∀ i j, rationalLogHeight (Fmark.basis.repr (φ (D.basis i)) j) ≤ pGeo)
    (hgeneratorHeight : ∀ i j,
      rationalLogHeight ((D.filtration.associatedGradedBasis D.basis dw hdb).repr (generators i) j) ≤ pGeo)
    (htopKernel : ∀ x : L, x ∈ D.filtration.gradedRefiltrationLayer W 1 → φ x = 0 → x = 0)
    (hOriginalNet : ∀ η : ℝ, 0 < η → η ≤ 1 → ∃ n : ℕ,
      (n : ℝ) ≤ Real.exp ((pGeo + Real.log (1 / η) + e) ^ e) ∧
      ∃ oc : Fin n → {x : X → ℤ // x ∈ integerBox N},
        ∀ x ∈ integerBox N, ∃ i, ∀ y, ‖observable x y - observable (oc i).val y‖ ≤ η)
    (hfullLeft : ∀ ij : (Fin d → Fin (dictionary.grid + 1)) × Fin dictionary.rightCount,
      ∀ x ∈ integerBox N, ∀ i,
      |(D.basis.baseChange ℝ).repr
        (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
          ((P₀.withKeep keep hkeep).physicalIntegerPoint x)
          (D.filtration.frozenMarkedLeftOrbit Fmark.filtration (fullTaggedVariableWeight J)
            sectionMap hSectionFilt reset.leftMark (dictionary.left ij.1))).coord i| ≤
        Real.exp ((pGeo + 2) ^ k))
    (hfullRight : ∀ ij : (Fin d → Fin (dictionary.grid + 1)) × Fin dictionary.rightCount,
      ∀ x ∈ integerBox N,
      (D.basis.baseChange ℝ).equivFun
        (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
          ((P₀.withKeep keep hkeep).physicalIntegerPoint x)
          (D.filtration.frozenMarkedRightOrbit Fmark.filtration (fullTaggedVariableWeight J)
            sectionMap hSectionFilt reset.rightMark (dictionary.right ij.2))).coord ∈
        realDenominatorGrid inputDenominator)
    : Nonempty (P₀.Conclusion (finiteFreezingRecursiveParameter C p)
      (Real.exp (-(finiteFreezingRecursiveParameter C p)))
      (Real.exp (-(finiteFreezingRecursiveParameter C p)))) := by
  exact P₀.conclusion_of_generatedCovered_nativeReset_degreeRule Fmark φ hφ keep hkeep W
    sectionMap hSectionFilt c ν hF factors reset tests htests hσ1 H hH hchart hsmall hp
    C hp0 hC dictionary hslowMark hgrid hdensity hfloor
    hBweight hBobs hLip hweight hnorm hlip hweightCap hobsCap hlipCap hscoreInput
    hcostInput hdensityInput hbudgetLog0 hbudgetLog hcount hmassLog hmassInput
    hsection dw hdb hW hsurj hξ1 ℓ hpGeo hDGeo hpGeoInput hpGeoRec hcoveredRec hℓ
    pRight hpRight hDRight hinputDenominator hinputDenominatorBound hRightBudget
    hOriginalLip hpositive hFGeo generators hspan hgeneratorCount hmarkedBasis
    hmarkHeight hgeneratorHeight htopKernel hOriginalNet hfullLeft hfullRight
    (finiteFreezingRecursiveParameter C p)
    (A.degreeGlobalizationAt_zero (E := E) weight
      (RationalFilteredNilmanifold.refilteredQuotientNetExponent.{0, 0, 0} 0 k e + 2)
      (finiteFreezingRecursiveParameter C p))

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI

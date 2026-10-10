import OAI.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateStepZero
import OAI.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateUniformSuccessor

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
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

variable {L M κ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {d f nD nF : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L (0 + 1) d}
    (Fmark : RationalFilteredNilmanifold M (0 + 1) f)
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
    (Dref : RationalFilteredNilmanifold
      (D.filtration.gradedRefiltrationSubalgebra W) (0 + 1) nD)
    (hDref : Dref.filtration = D.filtration.gradedRefiltration W)
    (Fref : RationalFilteredNilmanifold
      (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (0 + 1) nF)
    (markedMiddle : Fref.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (middle : ∀ z : (P₀.withKeep keep hkeep).productive,
      AllocatedExternalLocalCandidate ((P₀.withKeep keep hkeep).chart z) Dref Fref.filtration
        (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) markedMiddle)
    (sectionMap : M →ₗ[ℚ] L)
    (hSectionFilt : ∀ j, ∀ y ∈ Fmark.filtration.layer j, sectionMap y ∈ D.filtration.layer j)
    (c : Basis κ ℚ M)
    (leftMark rightMark : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (localLeft localRight : (P₀.withKeep keep hkeep).productive →
      (D.filtration.realification.adaptedPolynomialFiltration (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1)).Group)
    (localLeftMark localRightMark : (P₀.withKeep keep hkeep).productive →
      (Fmark.filtration.realification.adaptedPolynomialFiltration (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1)).Group)
    (hfactor : ∀ z : (P₀.withKeep keep hkeep).productive,
      (show (D.filtration.realification.adaptedPolynomialFiltration
          (fun _ : ((P₀.withKeep keep hkeep).chart z).Variables => 1)).Group from localLeft z) *
        (P₀.withKeep keep hkeep).refilteredLocalCoordinates A Fmark φ hφ W Dref hDref Fref
          markedMiddle middle z *
        (show (D.filtration.realification.adaptedPolynomialFiltration
          (fun _ : ((P₀.withKeep keep hkeep).chart z).Variables => 1)).Group from localRight z) =
      D.filtration.realification.polynomialOrbitCoordinates _ ((P₀.withKeep keep hkeep).candidate z).orbit)
    (hprojLeft : ∀ z, D.filtration.realPolynomialGroupMap Fmark.filtration φ hφ
      (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1) (localLeft z) = localLeftMark z)
    (hprojRight : ∀ z, D.filtration.realPolynomialGroupMap Fmark.filtration φ hφ
      (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1) (localRight z) = localRightMark z)
    (hleft : ∀ z : (P₀.withKeep keep hkeep).productive, ∀ u ∈ ((P₀.withKeep keep hkeep).chart z).slice.integerPoints,
      Fmark.filtration.adaptedPolynomialRealValueHom (fun _ => 1) (fun i => (u i : ℝ))
        (localLeftMark z) =
      Fmark.filtration.realification.polynomialOrbitRealEval (fullTaggedVariableWeight (X := X) J)
        (fun i => (((P₀.withKeep keep hkeep).chart z).chartValues u i : ℝ)) leftMark)
    (hright : ∀ z : (P₀.withKeep keep hkeep).productive, ∀ u ∈ ((P₀.withKeep keep hkeep).chart z).slice.integerPoints,
      Fmark.filtration.adaptedPolynomialRealValueHom (fun _ => 1) (fun i => (u i : ℝ))
        (localRightMark z) =
      Fmark.filtration.realification.polynomialOrbitRealEval (fullTaggedVariableWeight (X := X) J)
        (fun i => (((P₀.withKeep keep hkeep).chart z).chartValues u i : ℝ)) rightMark)
    (tests : (X → ℤ) → D.Niltest (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1))
    (htests : ∀ x, (tests x).observable = observable x)
    (hσ1 : ∀ j, σ j ≤ 1) (H : Fin m → ℝ) (hH : ∀ j, 0 ≤ H j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ H j * ‖v‖)
    (hsmall : ∀ j, H j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))

variable (hFref : Fref.filtration = Fmark.filtration.gradedRefiltration
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))
    {nQ nQF : ℕ}
    (Qquot : RationalFilteredNilmanifold
      ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ Dref.filtration.layerIdeal (0 + 1)) 0 nQ)
    (hQquot : Qquot.filtration = Dref.filtration.quotientTop)
    (Fquot : RationalFilteredNilmanifold
      ((Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) ⧸
        Fref.filtration.layerIdeal (0 + 1)) 0 nQF)
    (hFquot : Fquot.filtration = Fref.filtration.quotientTop)
    [PseudoMetricSpace Qquot.Space] [PseudoMetricSpace Fref.Space]
    (K : ℝ≥0)

include hFref hFquot hQquot hDref hfactor hprojLeft hprojRight hleft hright htests hσ1 H hH hchart hsmall hp

theorem conclusion_of_dictionary_degreeOne
    {l : ℕ} {slow ε budget Bweight Bobs Lip frozenThreshold θ densityCost : ℝ}
    (dictionary : RationalFilteredNilmanifold.ExternalMarkedAffineSliceFreezing.Dictionary
      (X := X → ℤ) D Fmark.filtration c φ hφ
      (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1) sectionMap hSectionFilt l
      (fun i : { i : LayerSamplerVariables G I n B // keep i } => (A.sides i.val : ℝ)) slow ε budget)
    (hslowLeft : ∀ z, D.filtration.PolynomialSlowBound D.basis (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1)
      (fun i : { i : LayerSamplerVariables G I n B // keep i } => (A.sides i.val : ℝ)) slow (localLeft z))
    (hslowMark : ∀ z, Fmark.filtration.PolynomialSlowBound c (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1)
      (fun i : { i : LayerSamplerVariables G I n B // keep i } => (A.sides i.val : ℝ)) slow (localLeftMark z))
    (hrationalRight : ∀ z, D.filtration.PolynomialRationalGrid D.basis
      (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1) l (localRight z))
    (hrationalMark : ∀ z, Fmark.filtration.PolynomialRationalGrid c
      (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1) l (localRightMark z))
    (hdensity : ∀ z : (P₀.withKeep keep hkeep).productive,
      IsDenseCommonStrideBox
        (fun i : ((P₀.withKeep keep hkeep).chart z).Variables => A.sides i.val)
        densityCost ((P₀.withKeep keep hkeep).chart z).slice.integerPoints)
    (hfloor : ∀ i : { i : LayerSamplerVariables G I n B // keep i },
      Real.exp densityCost * max 2 (2 * budget * max 1 budget) ≤ (A.sides i.val : ℝ))
    (hBweight : 0 ≤ Bweight) (hBobs : 0 ≤ Bobs) (hLip : 0 ≤ Lip) (hε : 0 ≤ ε)
    (hweight : ∀ x, ‖weight x‖ ≤ Bweight)
    (hnorm : ∀ x, ((tests x).normBound : ℝ) ≤ Bobs)
    (hlip : ∀ x, ((tests x).lipBound : ℝ) ≤ Lip)
    (hthreshold : 0 ≤ frozenThreshold) (hθ : 0 < θ)
    (hbudget : frozenThreshold + Bweight * (Lip * ε) + (Bweight * Bobs) * θ < scoreThreshold)
    (hsection : Function.RightInverse sectionMap φ)
    (hmass : 0 ≤ massThreshold)
    (dw : Fin d → ℕ)
    (hdb : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ dw i}))
    (fw : κ → ℕ)
    (hfb : ∀ j, Fmark.filtration.layer j = Submodule.span ℚ (c '' {i | j ≤ fw i}))
    (hW : BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis dw hdb) dw W.toSubmodule)
    (hsurj : ∀ j, ∀ y ∈ Fmark.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    (hξ1 : ξ ≤ 1)
    (hrecovery : ∀ ij : (Fin d → Fin (dictionary.grid + 1)) × Fin dictionary.rightCount, ∀ x, x ∈ integerBox N → ∀ source,
      positiveImageSlice
        (Dref.markedTopQuotientDiagram Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Qquot) K
        ((P₀.withKeep keep hkeep).refilteredFrozenObservable A Fmark φ W Dref (D.filtration.frozenMarkedLeftOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt leftMark (dictionary.left ij.1)) (D.filtration.frozenMarkedRightOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt rightMark (dictionary.right ij.2)) x)
        (Dref.markedTopQuotientDiagram Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Qquot source).2
        (Dref.markedTopQuotientDiagram Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Qquot source).1 =
        (P₀.withKeep keep hkeep).refilteredFrozenObservable A Fmark φ W Dref (D.filtration.frozenMarkedLeftOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt leftMark (dictionary.left ij.1)) (D.filtration.frozenMarkedRightOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt rightMark (dictionary.right ij.2)) x source)
    (recursionParameter : ℝ)
    (hcostRec : (max cost (densityCost + Real.log ((4 * budget * max 1 budget * (Fintype.card { i : LayerSamplerVariables G I n B // keep i } + 1 : ℝ)) / θ))) ≤ recursionParameter)
    (hmassRec : Real.exp (-recursionParameter) ≤ massThreshold / budget ^ 2)
    (hscoreRec : Real.exp (-recursionParameter) ≤ frozenThreshold)
    : Nonempty (P₀.Conclusion recursionParameter
      (Real.exp (-recursionParameter)) (Real.exp (-recursionParameter))) := by
  apply P₀.conclusion_of_dictionary_successor Fmark φ hφ keep hkeep W Dref hDref Fref
    markedMiddle middle sectionMap hSectionFilt c leftMark rightMark
    localLeft localRight localLeftMark localRightMark hfactor hprojLeft hprojRight
    hleft hright tests htests hσ1 H hH hchart hsmall hp
    hFref Qquot hQquot Fquot hFquot K
    dictionary hslowLeft hslowMark hrationalRight hrationalMark hdensity hfloor
    hBweight hBobs hLip hε hweight hnorm hlip hthreshold hθ hbudget
    hsection hmass dw hdb fw hfb hW hsurj hξ1 hrecovery
    recursionParameter hcostRec hmassRec hscoreRec
  intro ij lowerProblem
  exact lowerProblem.conclusion_stepZero _ _ _ _ _ _ _

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI

import OAI.Combinatorics.Progressions.Estimates.InheritedTaggedQuotientPrecenterMasks

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

namespace AllocatedExternalLocalChart

variable {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d f nD nF nQ : ℕ}
    (D : RationalFilteredNilmanifold L (s + 1) d)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (Dref : RationalFilteredNilmanifold
      (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nD)
    (hDref : Dref.filtration = D.filtration.gradedRefiltration W)
    (left right : D.filtration.realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J))
    (middle : Dref.filtration.realification.PolynomialOrbit (fun _ : C.Variables => 1))

noncomputable def originalDegreeRefilteredBinOrbit :
    D.filtration.realification.PolynomialOrbit (fun _ : C.Variables => 1) :=
  D.externalCandidateOrbit W Dref hDref (fun _ => 1)
    (D.filtration.polynomialOrbitRealChart (fullTaggedVariableWeight J) (fun _ => 1)
      (integerSampledRealChart C.integerChart) C.integerChart_support left)
    (D.filtration.polynomialOrbitRealChart (fullTaggedVariableWeight J) (fun _ => 1)
      (integerSampledRealChart C.integerChart) C.integerChart_support right)
    middle

theorem originalDegreeRefilteredBinOrbit_eval (u : C.Variables → ℤ) :
    D.filtration.realification.polynomialOrbitEval (fun _ => 1) u
      (C.originalDegreeRefilteredBinOrbit D W Dref hDref left right middle) =
    D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight J)
        (C.chartValues u) left *
      realificationMap (hnil := Dref.filtration.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot)
        (D.filtration.gradedRefiltrationSubalgebra W).incl
        (Dref.filtration.realification.polynomialOrbitEval (fun _ => 1) u middle) *
      D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight J)
        (C.chartValues u) right := by
  have he := D.externalCandidateOrbit_realEval W Dref hDref (fun _ : C.Variables => 1)
    (D.filtration.polynomialOrbitRealChart (fullTaggedVariableWeight J) (fun _ => 1)
      (integerSampledRealChart C.integerChart) C.integerChart_support left)
    (D.filtration.polynomialOrbitRealChart (fullTaggedVariableWeight J) (fun _ => 1)
      (integerSampledRealChart C.integerChart) C.integerChart_support right)
    middle (fun i => (u i : ℝ))
  unfold chartValues
  simpa only [originalDegreeRefilteredBinOrbit, polynomialOrbitRealEval_integer,
    polynomialOrbitIntegerChart_eval] using he

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {σtest : Type*} {w : σtest → ℕ} (bin : D.Niltest w)

noncomputable def originalDegreeRefilteredBinTest : D.Niltest (fun _ : C.Variables => 1) :=
  bin.withOrbit (C.originalDegreeRefilteredBinOrbit D W Dref hDref left right middle)

theorem originalDegreeRefilteredBinTest_complexity (p : ℝ) :
    (C.originalDegreeRefilteredBinTest D W Dref hDref left right middle bin).ComplexityLE p ↔
      bin.ComplexityLE p := Iff.rfl

@[simp] theorem originalDegreeRefilteredBinTest_normBound :
    (C.originalDegreeRefilteredBinTest D W Dref hDref left right middle bin).normBound =
      bin.normBound := rfl

noncomputable def originalDegreeBinFrozen (u : C.Variables → ℤ)
    (source : Dref.RealGroup) : ℂ :=
  bin.observable (QuotientGroup.mk
    (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight J)
        (C.chartValues u) left *
      realificationMap (hnil := Dref.filtration.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot)
        (D.filtration.gradedRefiltrationSubalgebra W).incl source *
      D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight J)
        (C.chartValues u) right))

theorem originalDegreeRefilteredBinTest_eval (u : C.Variables → ℤ) :
    (C.originalDegreeRefilteredBinTest D W Dref hDref left right middle bin).eval u =
      C.originalDegreeBinFrozen D W Dref left right bin u
        (Dref.filtration.realification.polynomialOrbitEval (fun _ => 1) u middle) := by
  rw [originalDegreeRefilteredBinTest, RationalFilteredNilmanifold.Niltest.withOrbit_eval,
    C.originalDegreeRefilteredBinOrbit_eval]
  rfl

variable (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    (Fref : RationalFilteredNilmanifold
      (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
    (Q : RationalFilteredNilmanifold
      ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ Dref.filtration.layerIdeal (s + 1)) s nQ)
    (hQ : Q.filtration = Dref.filtration.quotientTop)
    [PseudoMetricSpace Q.Space] [PseudoMetricSpace Fref.Space]
    (markedMiddle : Fref.filtration.realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J))
    (candidate : AllocatedExternalLocalCandidate C Dref Fref.filtration
      (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) markedMiddle)
    (K : ℝ≥0)

theorem originalDegreeRefilteredBinTest_positiveImage_on_slice
    (hrecovery : ∀ u ∈ C.slice.integerPoints, ∀ source,
      positiveImageSlice (Dref.markedTopQuotientDiagram Fref
        (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q) K
        (C.originalDegreeBinFrozen D W Dref left right bin u)
        (Dref.markedTopQuotientDiagram Fref
          (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q source).2
        (Dref.markedTopQuotientDiagram Fref
          (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q source).1 =
        C.originalDegreeBinFrozen D W Dref left right bin u source)
    (u : C.Variables → ℤ) (hu : u ∈ C.slice.integerPoints) :
    taggedRefilteredQuotientOperator D Fmark φ hφ W Dref Fref Q K
      (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight J)
        (C.chartValues u) left)
      (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight J)
        (C.chartValues u) right)
      (QuotientGroup.mk (Fref.filtration.realification.polynomialOrbitEval
        (fullTaggedVariableWeight J) (C.chartValues u) markedMiddle))
      bin.observable
      (QuotientGroup.mk (Q.filtration.realification.polynomialOrbitEval (fun _ => 1) u
        (Dref.topQuotientOrbit Q hQ candidate.orbit))) =
    (C.originalDegreeRefilteredBinTest D W Dref hDref left right candidate.orbit bin).eval u := by
  rw [C.originalDegreeRefilteredBinTest_eval, Dref.topQuotientOrbit_eval]
  have he := hrecovery u hu
    (Dref.filtration.realification.polynomialOrbitEval (fun _ => 1) u candidate.orbit)
  unfold originalDegreeBinFrozen at he ⊢
  simpa only [taggedRefilteredQuotientOperator,
    RationalFilteredNilmanifold.markedTopQuotientDiagram, candidate.mark_on_slice u hu] using he

noncomputable def originalDegreeRefilteredBinNative
    (hnorm : bin.normBound ≤ 1) {p : ℝ} (hcomplexity : bin.ComplexityLE p)
    (hrecovery : ∀ u ∈ C.slice.integerPoints, ∀ source,
      positiveImageSlice (Dref.markedTopQuotientDiagram Fref
        (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q) K
        (C.originalDegreeBinFrozen D W Dref left right bin u)
        (Dref.markedTopQuotientDiagram Fref
          (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q source).2
        (Dref.markedTopQuotientDiagram Fref
          (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q source).1 =
        C.originalDegreeBinFrozen D W Dref left right bin u source)
    : NativeSampleModel (fun _ : C.Variables => 1) (s + 1) p
      (fun u : C.slice.integerPoints =>
        commonStrideIndex (fun i => (C.slice.start i : ℤ)) C.step u.val)
      (fun u => taggedRefilteredQuotientOperator D Fmark φ hφ W Dref Fref Q K
      (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight J)
        (C.chartValues u.val) left)
      (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight J)
        (C.chartValues u.val) right)
      (QuotientGroup.mk (Fref.filtration.realification.polynomialOrbitEval
        (fullTaggedVariableWeight J) (C.chartValues u.val) markedMiddle))
      bin.observable
      (QuotientGroup.mk (Q.filtration.realification.polynomialOrbitEval (fun _ => 1) u.val
        (Dref.topQuotientOrbit Q hQ candidate.orbit)))) where
  L := L
  dim := d
  model := D
  test := (C.originalDegreeRefilteredBinTest D W Dref hDref left right candidate.orbit bin).commonStridePullback (fun i => (C.slice.start i : ℤ)) C.step
  norm := hnorm
  complexity := hcomplexity
  eval u := by
    apply (C.originalDegreeRefilteredBinTest_positiveImage_on_slice D W Dref hDref
      left right bin Fmark φ hφ Fref Q hQ markedMiddle candidate K
      hrecovery u.val u.property).trans
    apply ((C.originalDegreeRefilteredBinTest D W Dref hDref left right candidate.orbit bin).commonStridePullback_eval_index_of_mem
        (fun i => (C.slice.start i : ℤ)) C.step C.slice.length u.val _).symm
    rw [← C.slice.integerPoints_eq_commonStrideBox]
    exact u.property

end AllocatedExternalLocalChart
end Erdos3.VectorPolynomial

end

end OAI

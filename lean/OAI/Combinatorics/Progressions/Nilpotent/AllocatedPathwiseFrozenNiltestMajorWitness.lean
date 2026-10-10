import OAI.Combinatorics.Progressions.Dynamics.AllocatedPathwiseFrozenMajorDetection
import OAI.Combinatorics.Progressions.Nilpotent.AllocatedKeptCommonCurrentGradeLocalNiltest

namespace OAI

section

namespace Erdos3
open Module VectorPolynomial Submodule BooleanCubeKernel RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X] [DecidableEq X]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {J : Fin m → Type} [∀ j, Fintype (J j)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {btag : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U btag R σ}
    {hb : ∀ j, span ℤ (Set.range (btag j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (A : AllocatedExternalCandidateSampler B U btag S hb o hR hσ N poly hm τ ξ stride cells center)

namespace NilpotentLieFiltration

theorem exists_allocated_full_chart_major_correlation_witness_of_pathwise_frozen_local_niltests
    {k t : ℕ} {L ι η : Type} [Fintype η]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
      OrdinaryPolynomialPhase.weight t)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
      OrdinaryPolynomialPhase.weight t)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
      OrdinaryPolynomialPhase.weight t)]
    [T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
      OrdinaryPolynomialPhase.weight t)]
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (fast : Submodule ℚ F.AssociatedGraded)
    (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
    (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    (htk : t < k)
    (hpoly : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
    (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)
    (pSlice pTest pNative pMajor Rrank : ℝ) (C : ℕ)
    (hpNative : 2 ≤ pNative) (hη : (Fintype.card η : ℝ) ≤ pNative)
    (hNativeMajor : pNative ≤ pMajor) (hproduct : productNiltestBudget pNative ≤ pMajor)
    (hdim : ((Fintype.card X + Fintype.card (Σ j, J j) : ℕ) : ℝ) ≤ pMajor)
    (hN : ∀ i, Real.exp ((pMajor + C) ^ C) ≤ (N i : ℝ))
    (hRrank : Real.exp ((pMajor + C) ^ C) ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) Rrank (U j) (poly j))
    (good : η → Finset A.Path)
    (keep : A.Path → LayerSamplerVariables G I n B → Prop)
    (cost Bshort : ℝ) (hcost : 0 ≤ cost)
    (hBshort : 1 ≤ Bshort) (hshort : ∀ z i, ¬keep z i → (A.sides i : ℝ) ≤ Bshort)
    (hξ : ξ ≤ 1)
    (α : ℝ) (hmass : ∀ j, α ≤ (9 / 10 : ℝ) * A.law.mass (good j))
    (hdirect : A.NativeDetection t pSlice pTest pNative α)
    (hslice : max cost (Real.log Bshort) ≤ pSlice)
    (htest : OrdinaryPolynomialPhase.budget t ≤ pTest)
    (strideBound : η → A.Path → ℕ)
    (score : η → ∀ z : A.Path, ({i : LayerSamplerVariables G I n B // keep z i} → ℤ) → ℝ)
    (hlocal : ∀ j z, z ∈ good j →
      ∃ fixed : {i // ¬keep z i} → ℤ,
        (∀ i, 0 ≤ fixed i ∧ fixed i < A.sides i.val) ∧
      ∃ q : ℕ, 0 < q ∧ q ≤ strideBound j z ∧
      ∃ slice : ResidueBoxSlice (fun i : {i // keep z i} => A.sides i.val) q,
        IsDenseCommonStrideBox (fun i : {i // keep z i} => A.sides i.val) cost slice.integerPoints ∧
        (𝔼 x : (∀ i : {i // keep z i}, Fin (A.sides i.val)),
          score j z (fun i => ((x i).val : ℤ))) ≤
          (𝔼 x ∈ slice.integerPoints, score j z x) ∧
      ∃ T : (OrdinaryPolynomialPhase.nilmanifold t).Niltest (fun _ : {i // keep z i} => 1),
        T.normBound = 1 ∧ T.ComplexityLE (OrdinaryPolynomialPhase.budget t) ∧
        (9 / 10 : ℝ) ≤ ‖𝔼 x ∈ slice.integerPoints,
          majorPhasePlateauSignal J k poly c
            (coordinate (basis.coord j).toAddMonoidHom
              (lowTaggedVectorRestrict J k (F.realSymbolGradeQuotientPolynomial b ω hF
                (fullTaggedVariableWeight (X := X) J) fast k (left⁻¹ * Z * right⁻¹).coord)))
            (jointIntegerPhysicalSite (finiteSplitPoint (keep z) x fixed) (z.1.val, z.2.val)) *
              star (T.eval (commonStrideIndex (fun i => (slice.start i : ℤ)) q x))‖) :
    Nonempty (FullChartMajorCorrelationWitness F b ω hF J k fast basis
      Z left right N poly U pMajor Rrank C) := by
  apply exists_allocated_full_chart_major_correlation_witness_of_pathwise_frozen_local_tests
    A F b ω hF fast basis Z left right htk hpoly c pSlice pTest pNative pMajor Rrank C
    hpNative hη hNativeMajor hproduct hdim hN hRrank hrank good keep cost Bshort
    hcost hBshort hshort hξ α hmass hdirect hslice htest
  intro j z hz
  obtain ⟨fixed, hfixed, q, hq, _, slice, hdense, _, T, hnorm, hcomplex, hcorr⟩ := hlocal j z hz
  let packet : LocalMajorSliceTest (OrdinaryPolynomialPhase.nilmanifold t)
      (fun i : {i // keep z i} => A.sides i.val) cost (OrdinaryPolynomialPhase.budget t) :=
    { stride := q
      stride_pos := hq
      slice := slice
      dense := hdense
      test := T
      norm := by rw [hnorm]; norm_num
      complexity := hcomplex }
  exact ⟨fixed, hfixed, packet, hcorr⟩

end NilpotentLieFiltration
end Erdos3

end

end OAI

import OAI.Combinatorics.Progressions.Estimates.AllocatedOrdinaryLongPhysicalTerminalConclusion
import OAI.Combinatorics.Progressions.Geometry.AllocatedExternalCandidateSpatialNativeAutomaticLongGeometry

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

attribute [local irreducible] polynomialOrbitRealChart piRealOrbit
  weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom realSymbolGradeEvaluation
  CertifiedFullChartFiniteHistory.outer
  CertifiedFullChartFiniteHistory.earlyForwardBranchTree realGradedSymbolPolynomial

noncomputable section

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X] [DecidableEq X]
    {I J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
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

namespace AllocatedExternalCandidateSpatialNativeFamily

variable {Deck : Fin m → Type} {Pivot : Type} [Fintype Pivot]
    {LG LM : Type}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    {s d₀ : ℕ} {D : RationalFilteredNilmanifold LG s d₀}
    {Fmark : NilpotentLieFiltration LM s} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {keep : LayerSamplerVariables G I n B → Prop}
    {cost p pLocal pNative r periodCap coverCap : ℝ} {Lip : ℝ≥0}
    (F : AllocatedExternalCandidateSpatialNativeFamily A Deck A.Path Pivot D Fmark φ marked
      keep cost p pLocal pNative r periodCap coverCap Lip)

    (H : Finset A.Path)
    (sourceCenter : ∀ j, U j)
    (hpath : ∀ a ∈ H, (F.sourceChart a).path = a)
    (hcenter : ∀ a ∈ H, (F.sourceChart a).centerLift = sourceCenter)
    (hfrozen : ∀ a ∈ H, ∀ i : {i // ¬keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost)
    (observable : (X → ℤ) → D.Space → ℂ) (weight : (X → ℤ) → ℂ)
    (scoreThreshold : ℝ)
    (hscore : ∀ a ∈ H, scoreThreshold ≤ (F.sourceCandidate a).score observable weight)

variable {α : Type} [Fintype α]
    (e : Basis α ℚ (∀ i : Option Pivot, optionLieSpace LG (fun j => (F.native j).L) i))
    (ω : α → ℕ)
    (hF : ∀ k, (optionProduct D (fun j => (F.native j).model)).filtration.layer k =
      Submodule.span ℚ (e '' {i | k ≤ ω i}))
    (js : List Pivot)
    {dQ : ℕ}
    (Q : RationalFilteredNilmanifold (LG ⧸ D.filtration.pivotAnnihilatorIdeal φ F.η js) s dQ)
    (hQ : Q.filtration = D.filtration.pivotQuotientFiltration φ F.η js)
    (hker : ∀ x ∈ D.filtration.pivotAnnihilatorIdeal φ F.η js, φ x = 0)
    (descended : (X → ℤ) → Q.Space → ℂ)
    (hrecovery : ∀ x (g : D.RealGroup),
      descended x (QuotientGroup.mk
        (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := Q.filtration.lowerCentralSeries_eq_bot)
          (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal φ F.η js)) g)) =
        observable x (QuotientGroup.mk g))
    (adapted : (optionProduct Q (fun j => (F.native j).model)).AdaptedModelData)

local notation "countConstants" => (fun n => fullChartStageCountConstant (n + 1) 254)

theorem ActualAdaptedPivotQuotientFactors.exists_affine_physical_terminal
    {qVertical qCommon pProj : ℝ}
    (hproduced : F.ActualAdaptedPivotQuotientFactors H sourceCenter hpath hcenter hfrozen
      observable weight scoreThreshold hscore e ω hF js Q hQ hker descended hrecovery adapted
      qVertical qCommon pProj)
    (stageKeep : ℕ → LayerSamplerVariables G I n B → Prop)
    {κ : Type} [Fintype κ]
    (bMark : Basis κ ℚ (∀ i : Option Pivot, optionLieSpace LM (fun j => (F.native j).L) i))
    (ν : κ → ℕ)
    (hMark : ∀ k, (NilpotentLieFiltration.pi (optionFiltrations Fmark (fun j => ((fun j => (F.native j).model) j).filtration))).layer k = Submodule.span ℚ (bMark '' {i | k ≤ ν i}))
    (hmarkΦ : ∀ k, ∀ z ∈ (adapted.model.filtration).layer k, (optionMarkedLieMap (L := fun j => (F.native j).L) (quotientInducedMark (D.filtration.pivotAnnihilatorIdeal φ F.η js) φ hker)) z ∈ (NilpotentLieFiltration.pi (optionFiltrations Fmark (fun j => ((fun j => (F.native j).model) j).filtration))).layer k)
    [Fintype (SymbolBasisIndex (fun _ : LayerSamplerVariables G I n B => 1) adapted.weight)]
    [Fintype (SymbolBasisIndex (fun _ : LayerSamplerVariables G I n B => 1) ν)]
    [∀ r, Fintype (SymbolBasisIndex
      (fun _ : {i : LayerSamplerVariables G I n B // stageKeep r i} => 1) adapted.weight)]
    [∀ r, Fintype (SymbolBasisIndex
      (fun _ : {i : LayerSamplerVariables G I n B // stageKeep r i} => 1) ν)]
    [∀ r, TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [∀ r, IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [∀ r, ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [∀ r, T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    (pGeometry Rrank : ℝ) (Hbr : ℕ)
    (hpGeometry : 0 ≤ pGeometry)
    (hSourceGeometry : (finrank ℚ (∀ i : Option Pivot,
      optionLieSpace (LG ⧸ D.filtration.pivotAnnihilatorIdeal φ F.η js)
        (fun j => (F.native j).L) i) : ℝ) ≤ pGeometry)
    (hMarkedGeometry : (Fintype.card κ : ℝ) ≤ pGeometry)
    (hGeneratorGeometry : (Fintype.card α : ℝ) ≤ pGeometry)
    (hSamplerGeometry : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ pGeometry)
    (hQuotientGeometry : (pProj + 2) ^ 4 ≤ pGeometry)
    (scheduleExponent : ℕ) (x gainLog stageLog : ℝ)
    (hx : 0 ≤ x) (hgain : gainLog ∈ Set.Icc 0 x) (hstage : stageLog ∈ Set.Icc 0 x)
    (Cprimitive Csource : ℕ) (sourceNative pTest detectionLoss : ℕ → ℝ)
    (hSourceNonneg : ∀ r < s, 0 ≤ sourceNative r)
    (hSourceBound : ∀ r < s, sourceNative r ≤
      (preparedFiniteForwardSourcePrecision scheduleExponent countConstants r x gainLog stageLog +
        preparedFiniteForwardWork scheduleExponent countConstants r x + Csource) ^ Csource)
    (hBaseExponent : allocatedCandidateStageBaseExponent s m Cprimitive ≤ scheduleExponent)
    (hphaseExponent : ∀ r < s,
      allocatedCandidateCompositePhaseConstant s m 1
        (allocatedCandidatePromotedMajorConstant Csource) r ≤ scheduleExponent)
    (hCprimitive : 1 ≤ Cprimitive)
    (hGeometryBase : allocatedCandidateCommonFastBudget s pGeometry ≤ x)
    (hHbr : 1 ≤ Hbr)
    (hTagsBase : (Fintype.card (X ⊕ (Σ j, J j)) : ℝ) ≤ x)
    (hmEarly : (m : ℝ) ≤ x)
    (hblocksEarly : ((s * (Fintype.card κ * m) : ℕ) : ℝ) ≤ x)
    (hHbrBase : (Hbr : ℝ) ≤ Real.exp x)
    (hcost : cost ≤ (x + Cprimitive) ^ Cprimitive)
    (HMap : ℕ) (hHMap : 1 ≤ HMap)
    (hHMapGeometry : (HMap : ℝ) ≤ Real.exp pGeometry)
    (hNativeBase : (pProj + 2) ^ 3 + qCommon ≤ (x + Cprimitive) ^ Cprimitive)
    (hentries : ∀ i j, RationalHeightLE (bMark.repr ((optionMarkedLieMap (L := fun j => (F.native j).L) (quotientInducedMark (D.filtration.pivotAnnihilatorIdeal φ F.η js) φ hker)) (adapted.model.basis j)) i) HMap)
    (hbracket : ∀ i j z, RationalHeightLE (bMark.repr ⁅bMark i, bMark j⁆ z) Hbr)
    (hkept : ∀ r, ∀ i, stageKeep r i → Real.exp (allocatedCandidateStageSlice s m Cprimitive
      (preparedFiniteForwardParameter scheduleExponent countConstants r x)) ≤ (A.sides i : ℝ))
    (hfrozenStage : ∀ r, ∀ i, ¬stageKeep r i → (A.sides i : ℝ) ≤ Real.exp
      (allocatedCandidateStageSlice s m Cprimitive
        (preparedFiniteForwardParameter scheduleExponent countConstants r x)))
    (hTest : ∀ r < s, OrdinaryPolynomialPhase.budget r ≤ pTest r)
    (hDetectionLoss : ∀ r < s, detectionLoss r ≤ (9 / 10 : ℝ) *
      (Real.exp (-(verticalDecompositionBudget qVertical * Fintype.card Pivot +
        ((qCommon + 2) ^ 5 + qCommon))) * A.law.mass H))
    (hdirect : ∀ r < s, A.NativeDetection r (allocatedCandidateStageSlice s m Cprimitive
      (preparedFiniteForwardParameter scheduleExponent countConstants r x))
      (pTest r) (sourceNative r) (detectionLoss r))
    (hN : ∀ i, Real.exp (preparedFiniteForwardCumulative scheduleExponent countConstants s x) ≤ (N i : ℝ))
    (hRrank : Real.exp (preparedFiniteForwardCumulative scheduleExponent countConstants s x) ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) Rrank (U j) (poly j))
    (hs : 0 < s) (separation : ℝ)
    (hseparation : certifiedAffineLongSideBound
      (preparedFiniteForwardCumulative scheduleExponent countConstants s x) ≤ separation) :
    ∃ (retained : Finset A.Path) (hsub : retained ⊆ H)
      (hmass : Real.exp (-(verticalDecompositionBudget qVertical * Fintype.card Pivot +
        ((qCommon + 2) ^ 5 + qCommon))) * A.law.mass H ≤ A.law.mass retained),
      0 < A.law.mass retained ∧
      ∃ W : LieSubalgebra ℚ ((optionProduct D (fun j => (F.native j).model)).filtration).AssociatedGraded,
        let V := W.map (((optionProduct D (fun j => (F.native j).model)).filtration).associatedGradedMap (adapted.model.filtration) (optionMarkedLieMap (L := fun j => (F.native j).L) (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal φ F.η js))) (D.optionQuotientMap_mem_layer (D.filtration.pivotAnnihilatorIdeal φ F.η js) (by rw [D.filtration.terminal]; exact bot_le) Q hQ (fun j => (F.native j).model)))
        (∀ z ∈ (adapted.model.filtration).gradedRefiltrationLayer V s, (optionMarkedLieMap (L := fun j => (F.native j).L) (quotientInducedMark (D.filtration.pivotAnnihilatorIdeal φ F.η js) φ hker)) z = 0 → z = 0) ∧
        let source := F.actualSourceProblemOn H sourceCenter hpath hcenter hfrozen observable weight
          scoreThreshold hscore retained hsub hmass
        let target := (source.withKeep keep (fun _ => rfl)).adaptedOptionQuotient
          (fun j => (F.native j).model) (fun j => ((F.native j).test.fullTaggedSpatial J).orbit)
          (D.filtration.pivotAnnihilatorIdeal φ F.η js)
          (by rw [D.filtration.terminal]; exact bot_le) Q hQ hker descended hrecovery adapted
        target.NativeCommonPhysicalTerminal bMark ν hMark hmarkΦ V
          scheduleExponent Cprimitive x separation := by
  classical
  obtain ⟨retained, hsub, hmass, hpos, theta, W, v, den, hv, hW, hvH, hzero,
    hden, hdenBound, denQ, hdenQ, hdenQBound, hdiv, hvQ, hWQ, hvQH, hfactorQ,
    htop, hgradedTop⟩ := hproduced
  let source := F.actualSourceProblemOn H sourceCenter hpath hcenter hfrozen observable weight
    scoreThreshold hscore retained hsub hmass
  let target := (source.withKeep keep (fun _ => rfl)).adaptedOptionQuotient
    (fun j => (F.native j).model) (fun j => ((F.native j).test.fullTaggedSpatial J).orbit) (D.filtration.pivotAnnihilatorIdeal φ F.η js)
    (by rw [D.filtration.terminal]; exact bot_le) Q hQ hker descended hrecovery adapted
  let V := W.map (((optionProduct D (fun j => (F.native j).model)).filtration).associatedGradedMap (adapted.model.filtration) (optionMarkedLieMap (L := fun j => (F.native j).L) (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal φ F.η js))) (D.optionQuotientMap_mem_layer (D.filtration.pivotAnnihilatorIdeal φ F.η js) (by rw [D.filtration.terminal]; exact bot_le) Q hQ (fun j => (F.native j).model)))
  let vQ := ((optionProduct D (fun j => (F.native j).model)).filtration).gradedImageSpanningFamily (adapted.model.filtration) (optionMarkedLieMap (L := fun j => (F.native j).L) (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal φ F.η js))) (D.optionQuotientMap_mem_layer (D.filtration.pivotAnnihilatorIdeal φ F.η js) (by rw [D.filtration.terminal]; exact bot_le) Q hQ (fun j => (F.native j).model)) v
  have hpGeometryX : pGeometry ≤ x :=
    (allocatedCandidateCommonFastBudget_bounds s hpGeometry).2.2.trans hGeometryBase
  have hprimitive : x ≤ (x + Cprimitive) ^ Cprimitive := by
    have hC : (1 : ℝ) ≤ Cprimitive := by exact_mod_cast hCprimitive
    have hbase : 1 ≤ x + Cprimitive := by linarith
    exact (le_add_of_nonneg_right (Nat.cast_nonneg Cprimitive)).trans
      (by simpa only [pow_one] using pow_le_pow_right₀ hbase hCprimitive)
  have hdenQBase : (denQ : ℝ) ≤ Real.exp ((x + Cprimitive) ^ Cprimitive) :=
    hdenQBound.trans (Real.exp_le_exp.mpr
      ((hQuotientGeometry.trans hpGeometryX).trans hprimitive))
  have hOriginal (z : target.productive) :
      (adapted.model.filtration).HasCommonRefilteredOrbitFactors adapted.model.basis adapted.weight adapted.model_layers
        (fun i : (target.chart z).Variables => (A.sides i.val : ℝ))
        ((pProj + 2) ^ 3 + qCommon) denQ V
        ((adapted.model.filtration).realification.polynomialOrbitCoordinates (fun _ => 1) (target.candidate z).orbit) :=
    hfactorQ z
  have hselectedMass : 0 < Real.exp
      (-(verticalDecompositionBudget qVertical * Fintype.card Pivot +
        ((qCommon + 2) ^ 5 + qCommon))) * A.law.mass H := by
    apply mul_pos (Real.exp_pos _)
    apply hpos.trans_le
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun a _ _ => A.law.nonneg a)
  have ht := target.exists_native_common_affine_physical_terminal stageKeep
    adapted.model.basis adapted.weight adapted.model_layers bMark ν hMark hmarkΦ V
    vQ hvQ hWQ pGeometry Rrank Hbr hpGeometry
    (by simpa only [Fintype.card_fin] using hSourceGeometry) hMarkedGeometry
    (by simpa only [Fintype.card_fin] using hGeneratorGeometry) hSamplerGeometry
    (fun a i => (hvQH a i).trans hQuotientGeometry)
    scheduleExponent x gainLog stageLog hx hgain hstage Cprimitive Csource
    sourceNative pTest detectionLoss hSourceNonneg hSourceBound hBaseExponent hphaseExponent
    hCprimitive hGeometryBase hHbr hTagsBase hmEarly hblocksEarly hHbrBase hcost
    HMap denQ ((pProj + 2) ^ 3 + qCommon) hHMap hdenQ hHMapGeometry hdenQBase
    hNativeBase hentries hbracket hOriginal F.hτ1 F.hξ F.hσ1 F.Cgeo F.hCgeo F.hchart F.hsmall
    F.hpoly hkept hfrozenStage hTest hDetectionLoss hdirect hN hRrank hrank
    hs hselectedMass separation hseparation
  obtain ⟨qDim, hdim, eQ, lift, hfast, hsection, hterminal⟩ := ht
  refine ⟨retained, hsub, hmass, hpos, W, htop, ?_⟩
  have hηBase : (Fintype.card (Fin qDim) : ℝ) ≤ x := by
    simpa only [Fintype.card_fin] using
      (Nat.cast_le.mpr hdim).trans (hMarkedGeometry.trans hpGeometryX)
  have hblocks : ((s * (Fintype.card (Fin qDim) * m) : ℕ) : ℝ) ≤ x := by
    simpa only [Fintype.card_fin] using
      (Nat.cast_le.mpr (Nat.mul_le_mul_left s (Nat.mul_le_mul_right m hdim))).trans hblocksEarly
  have hXEarly : (Fintype.card X : ℝ) ≤ x := by
    have hsum : (Fintype.card X : ℝ) + (Fintype.card (Σ j, J j) : ℝ) ≤ x := by
      simpa only [Fintype.card_sum, Nat.cast_add] using hTagsBase
    exact (le_add_of_nonneg_right (Nat.cast_nonneg _)).trans hsum
  have hJEarly : (Fintype.card (Σ j, J j) : ℝ) ≤ x := by
    have hsum : (Fintype.card X : ℝ) + (Fintype.card (Σ j, J j) : ℝ) ≤ x := by
      simpa only [Fintype.card_sum, Nat.cast_add] using hTagsBase
    exact (le_add_of_nonneg_left (Nat.cast_nonneg _)).trans hsum
  have hNEarly : ∀ i, 1 ≤ N i := by
    intro i
    have hpositive : 0 < N i := by exact_mod_cast ((Real.exp_pos _).trans_le (hN i))
    exact Nat.succ_le_iff.mpr hpositive
  refine ⟨qDim, hdim, eQ, lift, hfast, hsection, hx, hXEarly, hmEarly, hJEarly,
    hηBase, hblocks, hNEarly, ?_⟩
  dsimp only at hterminal ⊢
  exact hterminal

end AllocatedExternalCandidateSpatialNativeFamily

end

end Erdos3.VectorPolynomial

end

end OAI

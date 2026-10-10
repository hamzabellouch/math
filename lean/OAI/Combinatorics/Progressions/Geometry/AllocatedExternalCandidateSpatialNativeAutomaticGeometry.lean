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

noncomputable section

theorem exists_allocatedExternalCandidateSpatialNativeFamily_native_geometry_factors
    (s : ℕ) (hs : 1 ≤ s) :
    ∃ Cgeometry C Cbasis K T : ℕ, 2 ≤ Cgeometry ∧ 2 ≤ C ∧ 2 ≤ Cbasis ∧ 2 ≤ K ∧ 2 ≤ T ∧
    ∀ {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
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

    {Deck : Fin m → Type*} {Pivot : Type*} [Fintype Pivot]
    {LG LM : Type}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    {d₀ : ℕ} {D : RationalFilteredNilmanifold LG s d₀}
    {Fmark : NilpotentLieFiltration LM s} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {keep : LayerSamplerVariables G I n B → Prop}
    {cost p pLocal pNative r periodCap coverCap : ℝ} {Lip : ℝ≥0}
    (F : AllocatedExternalCandidateSpatialNativeFamily A Deck A.Path Pivot D Fmark φ marked
      keep cost p pLocal pNative r periodCap coverCap Lip),
    ∀ {qVertical : ℝ}, pNative ≤ qVertical → pLocal + r + 1 ≤ qVertical →
      verticalDecompositionBudget qVertical ≤ p →
      r + verticalDecompositionBudget qVertical + 2 ≤ p →
    ∀ (H : Finset A.Path), 0 < A.law.mass H →
      (∀ a ∈ H, ∀ j, Real.exp (-r) ≤ ‖F.correlation a j‖) →
    ∀ (pGeometry : ℝ), 2 ≤ pGeometry → D.GeometryComplexityLE pGeometry →
      pNative ≤ pGeometry → (Fintype.card Pivot : ℝ) ≤ pGeometry →
    ∀ (js : List Pivot) {dQ : ℕ}
      (Q : RationalFilteredNilmanifold
        (LG ⧸ D.filtration.pivotAnnihilatorIdeal φ F.η js) s dQ)
      (hQ : Q.filtration = D.filtration.pivotQuotientFiltration φ F.η js)
      (hker : ∀ x ∈ D.filtration.pivotAnnihilatorIdeal φ F.η js, φ x = 0),
      Q.GeometryComplexityLE pGeometry →
      (∀ i j, rationalLogHeight
        (Q.basis.repr (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal φ F.η js)
          (D.basis j)) i) ≤ pGeometry) →
      let pGeo := (pGeometry + 2) ^ 2
      let jointGeo := (pGeometry + 3) ^ 2
      let adaptedBudget := (jointGeo + 2) ^ Cgeometry
      let bnd := adaptedBudget + (pGeo + 3) ^ 5 + pGeo + jointGeo + pGeometry + p + 2
      let localCost := allocatedFrozenTaggedPairBudget s C Cbasis pGeo p
      let jointCost := allocatedFrozenTaggedFamilyInputBudget bnd localCost
      let P := jointCost + (jointCost + K) ^ K
    ∀ [Nonempty {i // keep i}],
      (∀ i : {i // keep i}, Real.exp ((p + 2 + C) ^ C + 7 * p + 22) ≤
        (A.sides i.val : ℝ)) →
      (∀ i : {i // keep i}, Real.exp ((P + 2) ^ T) ≤ (A.sides i.val : ℝ)) →
      let qCommon := (P + 2) ^ T + (((P + 2) ^ 2 + 2) ^ 63 + 1) + P + 1
      let pProj := max qCommon 0 + adaptedBudget + 1
    ∀ (sourceCenter : ∀ j, U j)
      (hpath : ∀ a ∈ H, (F.sourceChart a).path = a)
      (hcenter : ∀ a ∈ H, (F.sourceChart a).centerLift = sourceCenter)
      (hfrozen : ∀ a ∈ H, ∀ i : {i // ¬keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost)
      (observable : (X → ℤ) → D.Space → ℂ) (weight : (X → ℤ) → ℂ)
      (scoreThreshold : ℝ)
      (hscore : ∀ a ∈ H, scoreThreshold ≤ (F.sourceCandidate a).score observable weight)
      (descended : (X → ℤ) → Q.Space → ℂ)
      (hrecovery : ∀ x (g : D.RealGroup),
        descended x (QuotientGroup.mk
          (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := Q.filtration.lowerCentralSeries_eq_bot)
            (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal φ F.η js)) g)) =
          observable x (QuotientGroup.mk g)),
      ∃ geometry : (optionProduct D (fun j => (F.native j).model)).AdaptedMapGeometryData
          (optionProduct Q (fun j => (F.native j).model))
          (optionMarkedLieMap (L := fun j => (F.native j).L)
            (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal φ F.η js)))
          jointGeo adaptedBudget,
        F.ActualAdaptedPivotQuotientFactors H sourceCenter hpath hcenter hfrozen observable weight
          scoreThreshold hscore geometry.source.basis geometry.source.weight geometry.source.layers
          js Q hQ hker descended hrecovery geometry.target qVertical qCommon pProj := by
  obtain ⟨Cgeometry, hCgeometry, hgeometry⟩ := exists_native_adapted_map_geometry
  obtain ⟨C, Cbasis, K, T, hC, hCbasis, hK, hT, hfactor⟩ :=
    exists_allocatedExternalCandidateSpatialNativeFamily_actual_adapted_quotient_factors s hs
  refine ⟨Cgeometry, C, Cbasis, K, T, hCgeometry, hC, hCbasis, hK, hT, ?_⟩
  intro m G X _ _ I J _ _ n B _ U b R σ S hb o hR hσ N poly hm τ ξ stride cells center
    _ A Deck Pivot _ LG LM _ _ _ _ _ _ _ _ d₀ D Fmark φ marked
    keep cost p pLocal pNative r periodCap coverCap Lip F
    qVertical hpq hprecision hfrequency hbudget H hH hcorr
    pGeometry hpGeometry hD hpNative hPivot js dQ Q hQ hker hQGeometry hmap
    pGeo jointGeo adaptedBudget bnd localCost jointCost P _ hlong hcommonLong qCommon pProj
    sourceCenter hpath hcenter hfrozen observable weight scoreThreshold hscore descended hrecovery
  have hpGeometry0 : 0 ≤ pGeometry := (by norm_num : (0 : ℝ) ≤ 2).trans hpGeometry
  have hnative (j : Pivot) : (F.native j).model.GeometryComplexityLE pGeometry :=
    (F.native j).complexity.1.mono (F.native j).model hpNative
  have hpGeo : 0 ≤ pGeo := by dsimp [pGeo]; positivity
  have hjointGeo : 0 ≤ jointGeo := by dsimp [jointGeo]; positivity
  have hGeometryJoint : pGeometry ≤ jointGeo := by dsimp [jointGeo]; nlinarith
  have hsourceGeo := optionProduct_geometry D (fun j => (F.native j).model)
    hpGeometry0 hPivot hD hnative
  have htargetGeo := optionProduct_geometry Q (fun j => (F.native j).model)
    hpGeometry0 hPivot hQGeometry hnative
  have hmapJoint := optionMarkedLieMap_native_logHeight D Q
    (fun j => (F.native j).model)
    (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal φ F.η js)) hpGeometry0 hmap
  obtain ⟨geometry⟩ := hgeometry
    (optionProduct D (fun j => (F.native j).model))
    (optionProduct Q (fun j => (F.native j).model))
    (optionMarkedLieMap (L := fun j => (F.native j).L)
      (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal φ F.η js)))
    hjointGeo hsourceGeo htargetGeo (fun i j => (hmapJoint j i).trans hGeometryJoint)
  refine ⟨geometry, ?_⟩
  have hpair (j : Pivot) : (pi (pairModels D (F.native j).model)).GeometryComplexityLE pGeo := by
    apply pi_geometry _ hpGeometry0
    · simpa only [Fintype.card_bool, Nat.cast_ofNat] using hpGeometry
    · intro k
      cases k
      · exact hnative j
      · exact hD
  have hadapted : 0 ≤ adaptedBudget := geometry.budget_nonneg
  have hpow : 0 ≤ (pGeo + 3) ^ 5 := by positivity
  have hbnd : 0 ≤ bnd := by dsimp only [bnd]; linarith only [hadapted, hpow, hpGeo, hjointGeo, hpGeometry0, F.hp]
  have habnd : adaptedBudget ≤ bnd := by dsimp only [bnd]; linarith only [hadapted, hpow, hpGeo, hjointGeo, hpGeometry0, F.hp]
  have hpbnd : p ≤ bnd := by dsimp only [bnd]; linarith only [hadapted, hpow, hpGeo, hjointGeo, hpGeometry0]
  have hgbnd : jointGeo + 1 ≤ bnd := by dsimp only [bnd]; linarith only [hadapted, hpow, hpGeo, hjointGeo, hpGeometry0, F.hp]
  have hsourceDim : (Fintype.card (Fin (finrank ℚ
      (∀ i : Option Pivot, optionLieSpace LG (fun j => (F.native j).L) i))) : ℝ) ≤ bnd := by
    simpa only [Fintype.card_fin] using geometry.source_dimension.trans (by linarith only [hgbnd] : jointGeo ≤ bnd)
  have hProj : 0 ≤ pProj :=
    add_nonneg (add_nonneg (le_max_right qCommon 0) hadapted) zero_le_one
  have hqProj : qCommon ≤ pProj :=
    (le_max_left qCommon 0).trans
      ((le_add_of_nonneg_right hadapted).trans (le_add_of_nonneg_right zero_le_one))
  have haProj : adaptedBudget ≤ pProj :=
    (le_add_of_nonneg_left (le_max_right qCommon 0)).trans
      (le_add_of_nonneg_right zero_le_one)
  have hJointProj : jointGeo ≤ pProj :=
    (le_add_of_nonneg_right (zero_le_one : (0 : ℝ) ≤ 1)).trans
      (geometry.forward_budget.trans haProj)
  exact hfactor F hpq hprecision hfrequency hbudget H hH hcorr
    (α := Fin (finrank ℚ (∀ i : Option Pivot, optionLieSpace LG (fun j => (F.native j).L) i)))
    (pGeo := pGeo) (bnd := bnd) hpGeo hbnd hpair
    (by dsimp only [bnd]; linarith only [hadapted, hpow, hpGeo, hjointGeo, hpGeometry0, F.hp])
    (by dsimp only [bnd]; linarith only [hadapted, hpow, hpGeo, hjointGeo, hpGeometry0, F.hp]) hsourceDim
    (hPivot.trans (by dsimp only [bnd]; linarith only [hadapted, hpow, hpGeo, hjointGeo, hpGeometry0, F.hp]))
    geometry.source.basis geometry.source.weight geometry.source.layers
    (fun i j k => (geometry.source_structure i j k).trans habnd)
    (fun i k => (geometry.source_forward i k).trans hgbnd)
    (F.hK.trans hpbnd) hlong hcommonLong
    sourceCenter hpath hcenter hfrozen observable weight scoreThreshold hscore
    js Q hQ hker descended hrecovery geometry.target
    (height := geometry.entries_height) (pProj := pProj) geometry.entries hProj hqProj
    (by simpa only [Fintype.card_fin] using geometry.source_dimension.trans hJointProj)
    (geometry.target_dimension.trans hJointProj)
    (geometry.entries_bound.trans (Real.exp_le_exp.mpr haProj))

end

end Erdos3.VectorPolynomial

end

end OAI

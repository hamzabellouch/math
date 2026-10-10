import OAI.Combinatorics.Progressions.Polynomial.PreparedFiniteForwardDegreeModelAttachment

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {nX : ℕ} (stride N : Fin nX → ℕ)
variable (Pdetect : Polynomial ℕ) (Vtail : Fin m → ℝ≥0) (τ : ℝ)
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable [∀ j, IsZLattice ℝ (latticeSection
  (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [IsProbabilityMeasure μ]
local notation "Ctail" => (4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (Vtail j))

variable {Stage : Type} [Fintype Stage] (degree : Stage → ℕ)
variable (selection : ∀ k, Fin (degree k + 1) ↪ G) (kModel : Stage)
variable (uSource modelLog sliceLog uModel pInput forecastCap : Stage → ℝ)
variable (Good : ∀ (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ)),
  (∀ j ex, coefficients (poly j) ex ∈ U j) →
  ∀ (width : Option (LayerSamplerVariables G I n B) × Fin nX → ℝ)
    (bases : Finset (Fin nX → ℤ)),
    (CoefficientTorus (K := LayerSamplerVariables G I n B) U →
      FiniteProbabilityWeights (bases × rectangularWeightIndices 0 width 1)) → Prop)

def PreparedFiniteScheduleLocalDegreeModelExtensionInterface
    (Pchart Qstride : ℝ) (Pmaster : Stage → ℝ) (Plate : ℝ)
    (Pphysical : Stage → ℝ) (coarseTarget extraRequired : ℝ) : Prop :=
    ∀ (_hstride : ∀ i, 0 < stride i) (_hstrideBound : ∀ i, (stride i : ℝ) ≤ Real.exp Qstride)
    (C : Fin m → ℝ) (_hC : ∀ j, 0 ≤ C j) (_hCbound : ∀ j, C j ≤ Real.exp Pchart)
    (_hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤ C j * ‖v‖)
    (Cforward : Fin m → ℝ≥0)
    (_hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) v‖ ≤ Cforward j * ‖v‖)
    (_hForward : ∀ j, (Cforward j : ℝ) ≤ Real.exp Pchart)
    (_hVtail : ∀ j, (Vtail j : ℝ) ≤ Real.exp Pchart)
    (_hVactual : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ Vtail j)
    (_hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Pchart)
    (_hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Pchart),
    ∀ {E : ℝ},
    ∀ (hτSpatial : 0 < τ), (∀ k, τ⁻¹ ≤ Real.exp (Pphysical k)) →
    τ ≤ 1 / 2 → (nX : ℝ) * τ ≤ 1 / 2 →
    let r := fun k => preparedModularGeneralDetectorResources
      (preparedModularGeneralDetectorConstants m (degree k)) (degree k + 1) (Pmaster k) Plate
    let W := allocatedPhysicalRootBudget B U basis S (fun _ => 0)
    ∀ {ξn : ℝ} (hξn : 0 < ξn)
      (hξle : ∀ k, ξn ≤ normalizedTupleNarrowWidth (Fin nX)
        (PrincipalTupleIndex B (layerSamplerDegree I n)) (selection k)
        (allocatedDetectedKernelCutoff (degree k) G (Fintype.card (LayerSamplerVariables G I n B)) Pdetect (allocatedModelTestLog (uSource k) (modelLog k))
          (allocatedModelTestLog (uSource k) (modelLog k))
          (forecastAugmentedUnitThreshold (uModel k) (pInput k)
            (Real.exp (sliceLog k * Fintype.card (LayerSamplerVariables G I n B)))
            (max 1 Ctail) (forecastCap k) / 2))
        (Pphysical k) coarseTarget),
    ξn⁻¹ ≤ Real.exp Plate →
    let hW := allocatedPhysicalRootBudget_nonneg B U basis S (fun _ => 0)
    let hξone : ξn ≤ 1 := (hξle kModel).trans (min_le_left _ _)
    let modelRequired := fun k => max (r k).required
      ((max (r k).Pproj E + preparedCenteredMarginalExponent m) ^ preparedCenteredMarginalExponent m)
    let required := max (∑ k, max 0 (modelRequired k)) extraRequired
    ∀ (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride))
      (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
      (_hp : ∀ j, DegreeLE (1 : (Fin nX) → ℕ) (j.val + 1) (poly j))
      (hmem : ∀ j ex, coefficients (poly j) ex ∈ U j)
      {Rrank : ℝ},
    (∀ i, Real.exp required ≤ (N i : ℝ)) →
    (∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j)) →
    Real.exp required ≤ Rrank →
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξn N
    cells.Nonempty →
    let bases := trimmedIntegerBox N (spatialTrimMargin τ N)
    let Z := selectedJointDensityMass bases stride cells V
      (allocatedJointBaseDensity B U basis hb o hR hσ S (Fin nX) poly hmem)
    ∃ (hN : ∀ i, 0 < N i) (hbases : bases.Nonempty) (hbox : (integerBox N).Nonempty)
      (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells V z)
      (_hnormalizer : |Z - 1| ≤ Real.exp (-(r kModel).E) ∧ Z ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧ 0 < Z ∧ Z⁻¹ ≤ 2)
      (_hmargin : ∀ i, 2 * spatialTrimMargin τ N i ≤ N i),
    let Path := bases × rectangularWeightIndices 0 V 1
    let Zcenter := fun center => selectedJointDensityMass bases stride cells V
      (allocatedCenteredJointDensity B U basis hb o hR hσ S poly hmem center)
    ∃ hnormalizerCenter : ∀ center,
      |Zcenter center - 1| ≤ Real.exp (-E) ∧
      Zcenter center ∈ Set.Icc (1 / 2 : ℝ) (3 / 2) ∧
      0 < Zcenter center ∧ (Zcenter center)⁻¹ ≤ 2,
    let centeredLaw := fun center => selectedJointFiniteLaw bases hbases stride cells V
      (narrowTrimmedSpatialWidths_pos hW hτSpatial hξn N hN) hmass
      (allocatedCenteredJointDensity B U basis hb o hR hσ S poly hmem center)
      (allocatedCenteredJointDensity_nonneg B U basis hb o hR hσ S poly hmem center) (hnormalizerCenter center).2.2.1
    ∃ hweight : ∀ z, Measurable (fun center => (centeredLaw center).weight z),
    Good poly hmem V bases centeredLaw ∧
    let pathLaw := centeredFiniteMarginal μ centeredLaw hweight
    let sides := Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U basis S)
    let Sites := integerBox sides
    let e : Sites → LayerSamplerVariables G I n B → ℤ := Subtype.val
    letI : Nonempty Sites := by
      have hpos (k : LayerSamplerVariables G I n B) : 0 < sides k := by
        cases k with
        | inl g => exact S.positive
        | inr j => exact allocatedPrincipalSides_pos B U basis S j
      let : ∀ k, NeZero (sides k) := fun k => ⟨(hpos k).ne'⟩
      exact (integerBox_nonempty sides).to_subtype
    let hrootSum := fun t : Sites => allocatedParameterBox_root_bound B U basis S t
    let physical := narrowPhysicalSiteMap (G := G)
      (J := PrincipalTupleIndex B (layerSamplerDegree I n)) hW hτSpatial hξone N hN
      _hmargin e hrootSum
    (FiniteProbabilityWeights.uniformFinset (integerBox N) hbox).excessMass
      (pathLaw.siteLaw physical) Ctail ≤ 6 * positiveProjectionAccuracy E ∧
    ∀ k, PreparedFiniteScheduleDegreeModelsAtLaw B U basis S N Pdetect μ poly hbox
      centeredLaw hweight physical (degree k) (uModel k) (pInput k) (forecastCap k) (sliceLog k)
      (allocatedModelTestLog (uSource k) (modelLog k)) (r k).nativeBudget E

theorem preparedFiniteScheduleLocalDegreeModelAttachment
    (Pchart Qstride : ℝ) (Pmaster : Stage → ℝ) (Plate : ℝ)
    (Pphysical : Stage → ℝ) (coarseTarget extraRequired : ℝ)
    (pGain : Stage → ℝ)
    (hModels : ∀ k, SharedWidthPreparedCenteredForecastModelDegreeInterface
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection k) (stride := stride) (N := N)
      (Pdetect := Pdetect) (uSource := uSource k) (pModel := modelLog k)
      (pSlice := sliceLog k) (Vtail := Vtail) (τ := τ)
      (u := uModel k) (p := pInput k) (forecastCap := forecastCap k)
      (hb := hb) (o := o) (μ := μ)
      Pchart Qstride (Pmaster k) Plate (pGain k) (Pphysical k) coarseTarget)
    (hGoodModel : SharedWidthPreparedCenteredForecastDegreeModelExtensionInterface
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection kModel) (stride := stride) (N := N)
      (Pdetect := Pdetect) (uSource := uSource kModel) (pModel := modelLog kModel)
      (pSlice := sliceLog kModel) (Vtail := Vtail) (τ := τ)
      (u := uModel kModel) (p := pInput kModel) (forecastCap := forecastCap kModel)
      (hb := hb) (o := o) (μ := μ) (Good := Good)
      Pchart Qstride (Pmaster kModel) Plate (pGain kModel) (Pphysical kModel) coarseTarget extraRequired) :
    PreparedFiniteScheduleLocalDegreeModelExtensionInterface
      B U basis hR hσ S stride N Pdetect Vtail τ hb o μ
      degree selection kModel uSource modelLog sliceLog uModel pInput forecastCap Good
      Pchart Qstride Pmaster Plate Pphysical coarseTarget extraRequired := by
  intro hstride hstrideBound C hC hCbound hchart Cforward hforward hForward
    hVtail hVactual hprofile hcutoff E hτSpatial hτInv hτHalf hτDim
    r W ξn hξn hξle hξLate hW hξone modelRequired required cells poly hpoly hmem Rrank
    hsize hrank hRank V hCells bases Z
  have hstageRequired (k : Stage) : modelRequired k ≤ required := by
    have hs : max 0 (modelRequired k) ≤ ∑ j, max 0 (modelRequired j) :=
      Finset.single_le_sum (fun j _ => le_max_left _ _) (Finset.mem_univ k)
    exact (le_max_right _ _).trans (hs.trans (le_max_left _ _))
  have hanchorRequired : max (modelRequired kModel) extraRequired ≤ required :=
    max_le (hstageRequired kModel) (le_max_right _ _)
  have hsizeAnchor (i) : Real.exp (max (modelRequired kModel) extraRequired) ≤ (N i : ℝ) :=
    (Real.exp_le_exp.mpr hanchorRequired).trans (hsize i)
  have hRankAnchor : Real.exp (max (modelRequired kModel) extraRequired) ≤ Rrank :=
    (Real.exp_le_exp.mpr hanchorRequired).trans hRank
  obtain ⟨hN, hbases, hbox, hmass, hnormalizer, hmargin, hnormalizerCenter,
      hweight, hgood, hexcess, _hbaseModel⟩ :=
    hGoodModel hstride hstrideBound C hC hCbound hchart Cforward hforward hForward
      hVtail hVactual hprofile hcutoff (E := E) hτSpatial (hτInv kModel) hτHalf hτDim
      hξn (hξle kModel) hξLate cells poly hpoly hmem hsizeAnchor hrank hRankAnchor hCells
  refine ⟨hN, hbases, hbox, hmass, hnormalizer, hmargin, ?_⟩
  intro Path Zcenter
  refine ⟨hnormalizerCenter, ?_⟩
  intro centeredLaw
  refine ⟨hweight, hgood, ?_⟩
  intro pathLaw sides Sites e hrootSum physical
  let : Nonempty Sites := by
    have hpos (k : LayerSamplerVariables G I n B) : 0 < sides k := by
      cases k with
      | inl g => exact S.positive
      | inr j => exact allocatedPrincipalSides_pos B U basis S j
    let : ∀ k, NeZero (sides k) := fun k => ⟨(hpos k).ne'⟩
    exact (integerBox_nonempty sides).to_subtype
  refine ⟨hexcess, ?_⟩
  intro k
  have hsizeStage (i) : Real.exp (modelRequired k) ≤ (N i : ℝ) :=
    (Real.exp_le_exp.mpr (hstageRequired k)).trans (hsize i)
  have hRankStage : Real.exp (modelRequired k) ≤ Rrank :=
    (Real.exp_le_exp.mpr (hstageRequired k)).trans hRank
  obtain ⟨_hNk, _hbasesk, _hboxk, _hmassk, _hnormk, _hmargink,
      _hnormCenterk, _hweightk, _hexcessk, hstage⟩ :=
    hModels k hstride hstrideBound C hC hCbound hchart Cforward hforward hForward
      hVtail hVactual hprofile hcutoff (E := E) hτSpatial (hτInv k) hτHalf hτDim
      hξn (hξle k) hξLate cells poly hpoly hmem hsizeStage hrank hRankStage hCells
  unfold PreparedFiniteScheduleDegreeModelsAtLaw
  intro pathLaw' sides' Sites' e' Tests instTests Ldetect instLie instAlg dims
    instTopo instAdd instSmul instT2 Ddetect Vdetect slices cdetect stepdetect Hdetect
    hstep hSlices hDense hnum hcomplex hcap tests Forecast instForecast forecast
    PforecastNative massLog hForecastNative hMassLog hModelPrecision
    Term instTerm coefficient centerConstant twists hCoeffMass hApprox hForecast
    Branch instBranch input hinput commonBudget Qmodel native localSeminorm selectedLocal
  have hsingle := hstage Ddetect Vdetect slices cdetect stepdetect Hdetect
    hstep hSlices hDense hnum hcomplex hcap forecast hForecastNative hMassLog
    hModelPrecision Term coefficient centerConstant twists hCoeffMass hApprox hForecast
  have hsingleModel : ∀ f : integerBox N → ℂ, (∀ v, ‖f v‖ ≤ Real.exp (pInput k)) →
      ∃ model : CenteredForecastModel (integerBox N),
        CenteredForecastModelBounds (centeredFiniteProbabilityMeasure μ centeredLaw)
          native (FiniteProbabilityWeights.uniformFinset (integerBox N) hbox) forecast
          localSeminorm selectedLocal f (Real.exp (Qmodel + 2)) (Real.exp (-uModel k))
          (Real.exp (2 * Qmodel + 2 * uModel k + 4 * pInput k + 34)) model := by
    intro f hf
    obtain ⟨nterms, hpos, models, coeff, err, hspec⟩ := hsingle f hf
    exact ⟨⟨nterms, hpos, models, coeff, err⟩, hspec⟩
  exact exists_centeredFiniteForecastModels
    (centeredFiniteProbabilityMeasure μ centeredLaw) native
    (FiniteProbabilityWeights.uniformFinset (integerBox N) hbox) forecast
    localSeminorm selectedLocal input (Real.exp (pInput k)) (Real.exp (Qmodel + 2))
    (Real.exp (-uModel k)) (Real.exp (2 * Qmodel + 2 * uModel k + 4 * pInput k + 34))
    hinput hsingleModel

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {nX : ℕ} (stride N : Fin nX → ℕ)
variable (Pdetect : Polynomial ℕ) (Vtail : Fin m → ℝ≥0) (τ : ℝ)
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable [∀ j, IsZLattice ℝ (latticeSection
  (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [IsProbabilityMeasure μ]
local notation "Ctail" => (4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (Vtail j))

variable {Stage : Type} [Fintype Stage] (degree : Stage → ℕ)
variable (selection : ∀ k, Fin (degree k + 1) ↪ G) (kModel : Stage)
variable (uSource modelLog sliceLog uModel pInput forecastCap : Stage → ℝ)
variable (Good : ∀ (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ)),
  (∀ j ex, coefficients (poly j) ex ∈ U j) →
  ∀ (width : Option (LayerSamplerVariables G I n B) × Fin nX → ℝ)
    (bases : Finset (Fin nX → ℤ)),
    (CoefficientTorus (K := LayerSamplerVariables G I n B) U →
      FiniteProbabilityWeights (bases × rectangularWeightIndices 0 width 1)) → Prop)

theorem preparedFiniteScheduleLocalDegreeModelAttachment_of_availability
    (Pchart Qstride : ℝ) (Pmaster : Stage → ℝ) (Plate : ℝ)
    (Pphysical : Stage → ℝ) (coarseTarget extraRequired : ℝ)
    (pGain : Stage → ℝ)
    (hAvailable : ∀ k, PreparedScheduledDegreeModelAvailability
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection k) (stride := stride) (N := N)
      (Pdetect := Pdetect) (sourceU := uSource k) (pModel := modelLog k)
      (pSlice := sliceLog k) (Vtail := Vtail) (τ := τ) (hb := hb) (o := o) (μ := μ)
      Pchart Qstride (Pmaster k) Plate (pGain k) (Pphysical k) coarseTarget)
    (hsource : ∀ k, uSource k = uModel k + 2 * pInput k + 1)
    (hu : ∀ k, 0 ≤ uModel k) (hp : ∀ k, 0 ≤ pInput k)
    (hslice : ∀ k, sliceLog k * Fintype.card (LayerSamplerVariables G I n B) ≤ pInput k)
    (htail : ∀ k, Ctail ≤ Real.exp (pInput k))
    (hcap : ∀ k, 0 ≤ forecastCap k) (hcapP : ∀ k, forecastCap k ≤ Real.exp (pInput k))
    (hGoodModel : SharedWidthPreparedCenteredForecastDegreeModelExtensionInterface
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection kModel) (stride := stride) (N := N)
      (Pdetect := Pdetect) (uSource := uSource kModel) (pModel := modelLog kModel)
      (pSlice := sliceLog kModel) (Vtail := Vtail) (τ := τ)
      (u := uModel kModel) (p := pInput kModel) (forecastCap := forecastCap kModel)
      (hb := hb) (o := o) (μ := μ) (Good := Good)
      Pchart Qstride (Pmaster kModel) Plate (pGain kModel) (Pphysical kModel) coarseTarget extraRequired) :
    PreparedFiniteScheduleLocalDegreeModelExtensionInterface
      B U basis hR hσ S stride N Pdetect Vtail τ hb o μ
      degree selection kModel uSource modelLog sliceLog uModel pInput forecastCap Good
      Pchart Qstride Pmaster Plate Pphysical coarseTarget extraRequired ∧
    0 < Real.exp (-Plate) ∧ (Real.exp (-Plate))⁻¹ = Real.exp Plate ∧
    ∀ k, Real.exp (-Plate) ≤ normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex B (layerSamplerDegree I n)) (selection k)
      (allocatedDetectedKernelCutoff (degree k) G (Fintype.card (LayerSamplerVariables G I n B))
        Pdetect (allocatedModelTestLog (uSource k) (modelLog k))
        (allocatedModelTestLog (uSource k) (modelLog k))
        (forecastAugmentedUnitThreshold (uModel k) (pInput k)
          (Real.exp (sliceLog k * Fintype.card (LayerSamplerVariables G I n B)))
          (max 1 Ctail) (forecastCap k) / 2)) (Pphysical k) coarseTarget := by
  have hstage (k) := hAvailable k (uModel k) (pInput k) (forecastCap k)
    (hsource k) (hu k) (hp k) (hslice k) (htail k) (hcap k) (hcapP k)
  refine ⟨?_, ?_⟩
  · exact preparedFiniteScheduleLocalDegreeModelAttachment B U basis hR hσ S stride N Pdetect
      Vtail τ hb o μ degree selection kModel uSource modelLog sliceLog uModel pInput forecastCap Good
      Pchart Qstride Pmaster Plate Pphysical coarseTarget extraRequired pGain
      (fun k => (hstage k).1) hGoodModel
  · exact sharedWidthNormalizedTuplePreparedChoice (fun k : Stage => degree k + 1)
      (fun k => allocatedDetectedKernelCutoff (degree k) G
        (Fintype.card (LayerSamplerVariables G I n B)) Pdetect
        (allocatedModelTestLog (uSource k) (modelLog k))
        (allocatedModelTestLog (uSource k) (modelLog k))
        (forecastAugmentedUnitThreshold (uModel k) (pInput k)
          (Real.exp (sliceLog k * Fintype.card (LayerSamplerVariables G I n B)))
          (max 1 Ctail) (forecastCap k) / 2))
      selection Pphysical (fun _ => coarseTarget) Plate
      (fun k => (hstage k).2)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {nX : ℕ} (stride N : Fin nX → ℕ)
variable (Pdetect : Polynomial ℕ) (Vtail : Fin m → ℝ≥0) (τ : ℝ)
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable [∀ j, IsZLattice ℝ (latticeSection
  (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [IsProbabilityMeasure μ]
local notation "Ctail" => (4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (Vtail j))

variable (depth A Cslice : ℕ) (stageCountConstant : ℕ → ℕ)
variable (selection : ∀ k : Fin (depth + 1), Fin ((Fin.val k) + 1) ↪ G)
variable (x gainLog stageLog : ℝ)
local notation "Stage" => Fin (depth + 1)
local notation "sourceU" => fun k : Stage =>
  preparedFiniteForwardSourcePrecision A stageCountConstant (Fin.val k) x gainLog stageLog
local notation "modelLog" => fun k : Stage => preparedFiniteForwardWork A stageCountConstant (Fin.val k) x
local notation "sliceLog" => fun k : Stage =>
  (preparedFiniteForwardParameter A stageCountConstant (Fin.val k) x + Cslice) ^ Cslice
local notation "uModel" => fun k : Stage =>
  preparedFiniteForwardModelPrecision A stageCountConstant (Fin.val k) x gainLog stageLog
local notation "cap" => fun k : Stage => Real.exp (modelLog k)
variable (Good : ∀ (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ)),
  (∀ j ex, coefficients (poly j) ex ∈ U j) →
  ∀ (width : Option (LayerSamplerVariables G I n B) × Fin nX → ℝ)
    (bases : Finset (Fin nX → ℤ)),
    (CoefficientTorus (K := LayerSamplerVariables G I n B) U →
      FiniteProbabilityWeights (bases × rectangularWeightIndices 0 width 1)) → Prop)

theorem preparedFiniteForwardLocalDegreeModelAttachment
    (hA : 2 ≤ A) (hSliceExponent : Cslice + 1 ≤ A) (hx : 0 ≤ x)
    (hg : gainLog ∈ Set.Icc 0 x) (hstage : stageLog ∈ Set.Icc 0 x)
    (hcount : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ x)
    (Pchart Qstride : ℝ) (Pmaster : Stage → ℝ) (Plate : ℝ)
    (Pphysical : Stage → ℝ) (coarseTarget extraRequired : ℝ)
    (pGain : Stage → ℝ)
    (hAvailable : ∀ k, PreparedScheduledDegreeModelAvailability
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection k) (stride := stride) (N := N)
      (Pdetect := Pdetect) («sourceU» := sourceU k) (pModel := modelLog k)
      (pSlice := sliceLog k) (Vtail := Vtail) (τ := τ) (hb := hb) (o := o) (μ := μ)
      Pchart Qstride (Pmaster k) Plate (pGain k) (Pphysical k) coarseTarget)
    (htail : Ctail ≤ Real.exp (modelLog 0))
    (hGoodModel : SharedWidthPreparedCenteredForecastDegreeModelExtensionInterface
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection 0) (stride := stride) (N := N)
      (Pdetect := Pdetect) (uSource := sourceU 0) (pModel := modelLog 0)
      (pSlice := sliceLog 0) (Vtail := Vtail) (τ := τ)
      (u := uModel 0) (p := modelLog 0) (forecastCap := cap 0)
      (hb := hb) (o := o) (μ := μ) (Good := Good)
      Pchart Qstride (Pmaster 0) Plate (pGain 0) (Pphysical 0) coarseTarget extraRequired) :
    PreparedFiniteScheduleLocalDegreeModelExtensionInterface
      B U basis hR hσ S stride N Pdetect Vtail τ hb o μ
      (fun k : Stage => (Fin.val k)) selection 0 sourceU modelLog sliceLog uModel modelLog cap Good
      Pchart Qstride Pmaster Plate Pphysical coarseTarget extraRequired ∧
    0 < Real.exp (-Plate) ∧ (Real.exp (-Plate))⁻¹ = Real.exp Plate ∧
    ∀ k : Stage, Real.exp (-Plate) ≤ normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex B (layerSamplerDegree I n)) (selection k)
      (allocatedDetectedKernelCutoff (Fin.val k) G (Fintype.card (LayerSamplerVariables G I n B))
        Pdetect (allocatedModelTestLog (sourceU k) (modelLog k))
        (allocatedModelTestLog (sourceU k) (modelLog k))
        (forecastAugmentedUnitThreshold (uModel k) (modelLog k)
          (Real.exp (sliceLog k * Fintype.card (LayerSamplerVariables G I n B)))
          (max 1 Ctail) (cap k) / 2)) (Pphysical k) coarseTarget := by
  have hscalar (k : Stage) := preparedFiniteForward_model_scalar_bounds A stageCountConstant
    (Fin.val k) (Fintype.card (LayerSamplerVariables G I n B)) hA hx hcount
  have hslices (k : Stage) := preparedFiniteForward_controlled_slice_bounds A Cslice stageCountConstant
    (Fin.val k) (Fintype.card (LayerSamplerVariables G I n B)) hA hSliceExponent hx hcount
  have hprecision (k : Stage) :=
    preparedFiniteForward_model_precision_bounds A stageCountConstant (Fin.val k) hx hg hstage
  have htailStage (k : Stage) : Ctail ≤ Real.exp (modelLog k) := by
    apply htail.trans
    apply Real.exp_le_exp.mpr
    simp only [preparedFiniteForwardWork_eq]
    exact pow_le_pow_left₀
      (add_nonneg (preparedFiniteForwardParameter_nonneg A stageCountConstant 0 hx)
        (Nat.cast_nonneg A))
      (add_le_add
        (preparedFiniteForwardParameter_monotone A stageCountConstant hx (Nat.zero_le (Fin.val k))) (le_refl (A : ℝ))) A
  exact preparedFiniteScheduleLocalDegreeModelAttachment_of_availability
    B U basis hR hσ S stride N Pdetect Vtail τ hb o μ
    (fun k : Stage => (Fin.val k)) selection 0 sourceU modelLog sliceLog uModel modelLog cap Good
    Pchart Qstride Pmaster Plate Pphysical coarseTarget extraRequired pGain hAvailable
    (fun k => (hprecision k).2.2.1) (fun k => (hprecision k).1)
    (fun k => (hscalar k).1) (fun k => (hslices k).2.2) htailStage
    (fun k => Real.exp_nonneg _) (fun _ => le_rfl) hGoodModel

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {m : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {nX : ℕ} (stride N : Fin nX → ℕ)
variable (Pdetect : Polynomial ℕ) (Vtail : Fin m → ℝ≥0) (τ : ℝ)
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable [∀ j, IsZLattice ℝ (latticeSection
  (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [IsProbabilityMeasure μ]
local notation "Ctail" => (4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (Vtail j))

variable (depth A Cslice : ℕ) (stageCountConstant : ℕ → ℕ)
variable (degree : Fin (depth + 1) → ℕ)
variable (selection : ∀ k : Fin (depth + 1), Fin (degree k + 1) ↪ G)
variable (x gainLog stageLog : ℝ)
local notation "Stage" => Fin (depth + 1)
local notation "sourceU" => fun k : Stage =>
  preparedFiniteForwardSourcePrecision A stageCountConstant (Fin.val k) x gainLog stageLog
local notation "modelLog" => fun k : Stage => preparedFiniteForwardWork A stageCountConstant (Fin.val k) x
local notation "sliceLog" => fun k : Stage =>
  (preparedFiniteForwardParameter A stageCountConstant (Fin.val k) x + Cslice) ^ Cslice
local notation "uModel" => fun k : Stage =>
  preparedFiniteForwardModelPrecision A stageCountConstant (Fin.val k) x gainLog stageLog
local notation "cap" => fun k : Stage => Real.exp (modelLog k)
variable (Good : ∀ (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ)),
  (∀ j ex, coefficients (poly j) ex ∈ U j) →
  ∀ (width : Option (LayerSamplerVariables G I n B) × Fin nX → ℝ)
    (bases : Finset (Fin nX → ℤ)),
    (CoefficientTorus (K := LayerSamplerVariables G I n B) U →
      FiniteProbabilityWeights (bases × rectangularWeightIndices 0 width 1)) → Prop)

theorem preparedFiniteForwardPrescribedDegreeModelAttachment
    (hA : 2 ≤ A) (hSliceExponent : Cslice + 1 ≤ A) (hx : 0 ≤ x)
    (hg : gainLog ∈ Set.Icc 0 x) (hstage : stageLog ∈ Set.Icc 0 x)
    (hcount : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ x)
    (Pchart Qstride : ℝ) (Pmaster : Stage → ℝ) (Plate : ℝ)
    (Pphysical : Stage → ℝ) (coarseTarget extraRequired : ℝ)
    (pGain : Stage → ℝ)
    (hAvailable : ∀ k, PreparedScheduledDegreeModelAvailability
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection k) (stride := stride) (N := N)
      (Pdetect := Pdetect) («sourceU» := sourceU k) (pModel := modelLog k)
      (pSlice := sliceLog k) (Vtail := Vtail) (τ := τ) (hb := hb) (o := o) (μ := μ)
      Pchart Qstride (Pmaster k) Plate (pGain k) (Pphysical k) coarseTarget)
    (htail : Ctail ≤ Real.exp (modelLog 0))
    (hGoodModel : SharedWidthPreparedCenteredForecastDegreeModelExtensionInterface
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection 0) (stride := stride) (N := N)
      (Pdetect := Pdetect) (uSource := sourceU 0) (pModel := modelLog 0)
      (pSlice := sliceLog 0) (Vtail := Vtail) (τ := τ)
      (u := uModel 0) (p := modelLog 0) (forecastCap := cap 0)
      (hb := hb) (o := o) (μ := μ) (Good := Good)
      Pchart Qstride (Pmaster 0) Plate (pGain 0) (Pphysical 0) coarseTarget extraRequired) :
    PreparedFiniteScheduleLocalDegreeModelExtensionInterface
      B U basis hR hσ S stride N Pdetect Vtail τ hb o μ
      degree selection 0 sourceU modelLog sliceLog uModel modelLog cap Good
      Pchart Qstride Pmaster Plate Pphysical coarseTarget extraRequired ∧
    0 < Real.exp (-Plate) ∧ (Real.exp (-Plate))⁻¹ = Real.exp Plate ∧
    ∀ k : Stage, Real.exp (-Plate) ≤ normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex B (layerSamplerDegree I n)) (selection k)
      (allocatedDetectedKernelCutoff (degree k) G (Fintype.card (LayerSamplerVariables G I n B))
        Pdetect (allocatedModelTestLog (sourceU k) (modelLog k))
        (allocatedModelTestLog (sourceU k) (modelLog k))
        (forecastAugmentedUnitThreshold (uModel k) (modelLog k)
          (Real.exp (sliceLog k * Fintype.card (LayerSamplerVariables G I n B)))
          (max 1 Ctail) (cap k) / 2)) (Pphysical k) coarseTarget := by
  have hscalar (k : Stage) := preparedFiniteForward_model_scalar_bounds A stageCountConstant
    (Fin.val k) (Fintype.card (LayerSamplerVariables G I n B)) hA hx hcount
  have hslices (k : Stage) := preparedFiniteForward_controlled_slice_bounds A Cslice stageCountConstant
    (Fin.val k) (Fintype.card (LayerSamplerVariables G I n B)) hA hSliceExponent hx hcount
  have hprecision (k : Stage) :=
    preparedFiniteForward_model_precision_bounds A stageCountConstant (Fin.val k) hx hg hstage
  have htailStage (k : Stage) : Ctail ≤ Real.exp (modelLog k) := by
    apply htail.trans
    apply Real.exp_le_exp.mpr
    simp only [preparedFiniteForwardWork_eq]
    exact pow_le_pow_left₀
      (add_nonneg (preparedFiniteForwardParameter_nonneg A stageCountConstant 0 hx)
        (Nat.cast_nonneg A))
      (add_le_add
        (preparedFiniteForwardParameter_monotone A stageCountConstant hx (Nat.zero_le (Fin.val k))) (le_refl (A : ℝ))) A
  exact preparedFiniteScheduleLocalDegreeModelAttachment_of_availability
    B U basis hR hσ S stride N Pdetect Vtail τ hb o μ
    degree selection 0 sourceU modelLog sliceLog uModel modelLog cap Good
    Pchart Qstride Pmaster Plate Pphysical coarseTarget extraRequired pGain hAvailable
    (fun k => (hprecision k).2.2.1) (fun k => (hprecision k).1)
    (fun k => (hscalar k).1) (fun k => (hslices k).2.2) htailStage
    (fun k => Real.exp_nonneg _) (fun _ => le_rfl) hGoodModel

end Erdos3.VectorPolynomial

end

end OAI

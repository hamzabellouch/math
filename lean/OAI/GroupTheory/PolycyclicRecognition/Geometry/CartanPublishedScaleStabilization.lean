import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanPublishedAffineMean
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanPublishedMixedScaleConcentration
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanActualScaleComparison
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanCellProfileConcentration
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanUniformBoxProfiles
import OAI.GroupTheory.PolycyclicRecognition.Analysis.AffineMeanApproximation
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ProfileLawIntegral
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanOrdinaryBoxCover
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBoxRadiusProbability
import OAI.GroupTheory.PolycyclicRecognition.Analysis.IndependentCellConcentration
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSubexponentialGroupChain
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanUniformSuffixMetric
import OAI.GroupTheory.PolycyclicRecognition.Geometry.UniversalCartanProfiles
import OAI.GroupTheory.PolycyclicRecognition.Analysis.MeasurableProbeProfiles
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanNeighborChainConcentration
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanNeighborSamplingRow
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanUniformCommonAffinity
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanPolarConeModels
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanNeighborRowOffsetsEqual
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanFixedPolarTargets
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanFixedSamplingGeometry
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanCanonicalPolarSamplers
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanContactStepBridge
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SmallFactorCell
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanOffsetThreshold

namespace OAI

/-! # Published-input comparison of canonical affine labels at adjacent scales -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Filter Set
open scoped Manifold Topology ENNReal NNReal BigOperators

attribute [local instance] stationaryL2Action zeroMeanL2Action

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [IsTopologicalGroup G] [IsIsometricSMul G G] [ProperSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W] [SecondCountableTopology W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H) [Nonempty (Fin M.letterCount)]
  [Nonempty (Fin (finrank ℝ (cartanRootIdeal H)))]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  [IsTopologicalGroup F.N.carrier] [SecondCountableTopology F.N.carrier]
  [IsTopologicalGroup F.D.carrier] [SecondCountableTopology F.D.carrier]
  [Fintype I] [DecidableEq I] {Λ : ℝ≥0}
  [MeasurableSpace (NormalizedPair G Λ)] [BorelSpace (NormalizedPair G Λ)]
  [MeasurableSpace C((Fin (finrank ℝ H) → ℝ), W)]
  [BorelSpace C((Fin (finrank ℝ H) → ℝ), W)]

local notation "Eall" => M.samplingPolytope T hunimod eW

/-- The canonical ordinary-cell labels agree across nearby scales, and their
mean offsets agree after conversion to the source-scale normalization. -/
theorem exists_published_adjacent_scale_labels
    (hExp : IsGroupExponential Exp) (hinj : Function.Injective Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ x, chartN x = F.ExpN x)
    (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
    (hchartD : ∀ x, chartD x = F.ExpD x)
    (m : Measure G) [m.IsHaarMeasure] [m.IsMulRightInvariant]
    (νD : Measure F.D.carrier) [νD.IsHaarMeasure] [SigmaFinite νD]
    (π : G →* Multiplicative W)
    (hπExp : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
    (hdec : ErgodicDecompositionInput G (NormalizedPair G Λ))
    (hvan : ∀ (μ : Measure (NormalizedPair G Λ)) [IsProbabilityMeasure μ]
      [ErgodicSMul G (NormalizedPair G Λ) μ],
      ReducedCohomologyInput G (ZeroMeanL2 (W := W) μ))
    (hΛ : 0 < (Λ : ℝ)) {Kπ : ℝ≥0}
    (hπ : LipschitzWith Kπ (fun g => (π g).toAdd))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ : M.Bases)
    (hγ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList bN)
      (M.boxCost T hunimod eW Eall) γ.val)
    (X : I → H) {d : ℕ} (hDnil : lowerCentralSeries ℝ H H d = ⊥)
    (hDletters : ∀ i : I, FreeMagma.of i ∈ boundedBracketWords d)
    (bD₀ : Basis (Fin (finrank ℝ H)) ℝ H)
    (βD : WordBasisSelections X (boundedBracketWords d))
    (hβD : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords d) bD₀)
      (fun w => bracketWordExponent (fun _ : I => 1) w) βD.val)
    {c₀ : ℕ} (aN : DynkinCoefficients c₀ 2)
    (hmN : ∀ x y, F.ExpN (finiteDynkinPolynomial aN ![x, y]) = F.ExpN x * F.ExpN y)
    {cD : ℕ} (aD : DynkinCoefficients cD 2)
    (hmD : ∀ x y, F.ExpD (finiteDynkinPolynomial aD ![x, y]) = F.ExpD x * F.ExpD y)
    (rem : RemezPolynomialInput) (hdim : 1 ≤ finrank ℝ (cartanRootIdeal H))
    (pivot : Fin M.letterCount → H)
    (hcanonical : ∀ i, cartanHeightSection T H (heightProjection T.character (pivot i)) = pivot i)
    (hunit : ∀ i, ‖eW (heightProjection T.character (pivot i))‖ = 1)
    (hcontact : ∀ i, ((M.supportIn T hunimod eW).weight i).toContinuousLinearMap
      (eW (heightProjection T.character (pivot i))) =
        ‖((M.supportIn T hunimod eW).weight i).toContinuousLinearMap‖)
    (hpositive : ∀ i, 0 < M.weight i (pivot i))
    {lo hi c B : ℝ} (hc : 0 ≤ c) (hhi : 0 ≤ hi) (hB : 0 ≤ B)
    (hcost : ∀ w : M.wordList, lo ≤ M.boxCost T hunimod eW Eall w ∧
      M.boxCost T hunimod eW Eall w ≤ hi)
    (hgap : (M.bound : ℝ) * hi < c * lo)
    (σchamber : Fin M.letterCount → Bool)
    (hσchamber : (weightChamber (fun j =>
      ((M.supportIn T hunimod eW).weight j).toContinuousLinearMap) σchamber).Nonempty)
    (hnz : ∀ i, (M.supportIn T hunimod eW).weight i ≠ 0)
    (sourceInputs : ∀ (i : Fin M.letterCount)
      (s : rootOffsetConeIndex (M.supportIn T hunimod eW) i),
      M.PolarConeModelInputs F (heightConePreimage T eW
        (rootOffsetCone (M.supportIn T hunimod eW) hnz i s)))
    (sourceDynkin : ∀ (i : Fin M.letterCount)
      (s : rootOffsetConeIndex (M.supportIn T hunimod eW) i)
      (J : NilpotentLieModel (M.coneWordIdeal (heightConePreimage T eW
        (rootOffsetCone (M.supportIn T hunimod eW) hnz i s)))),
      NilpotentDynkinExpansionInput J.modelSpace J.carrier)
    (targetInputs : ∀ (i : Fin M.letterCount)
      (A : templateSymmetryGroup (M.supportIn T hunimod eW))
      (s : rootOffsetConeIndex (M.supportIn T hunimod eW) i),
      M.PolarConeModelInputs F (heightConePreimage T eW
        (transformedPolarCone (rootOffsetCone (M.supportIn T hunimod eW) hnz i s) A.val)))
    (hweightB : ∀ i, (M.supportIn T hunimod eW).weightSupport Eall i ≤ B)
    :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ (scale : ℕ → ℝ) (_hgrows : Tendsto scale atTop atTop)
        (_hmono : StrictMono scale) (_hs1 : ∀ n, 1 ≤ scale n)
        (targetScale : ℕ → ℝ) (_htmono : StrictMono targetScale),
      (∀ n, scale n ≤ targetScale n) →
      (∀ n, targetScale n ≤ (1 + δ) * scale n) →
      ∀ R : ℝ, 0 < R →
      (∀ z ∈ Metric.closedBall (0 : Fin (finrank ℝ H) → ℝ) R,
        eW (heightProjection T.character
          ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
            GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈
          (fun w => (1 - c * δ) • w) '' interior Eall) →
      ∀ (pair : ℕ → NormalizedPair G Λ) (center : ℕ → G)
        (raw raw' : ℕ → F.N.carrier → C((Fin (finrank ℝ H) → ℝ), W)),
      (∀ n k z, raw n k z = rescaledMapProfile
        (fun g => (π ((pair n).val.1 g)).toAdd) (center n) (F.inclusionN k)
        (max (Real.log (scale n)) 0)
        (F.profileChart (exponentialRescaleBasis
          (WordBasisSelections.basis X (boundedBracketWords d) βD)
          (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
          (max (Real.log (scale n)) 0))) z) →
      (∀ n k z, raw' n k z = rescaledMapProfile
        (fun g => (π ((pair n).val.1 g)).toAdd) (center n) (F.inclusionN k)
        (max (Real.log (targetScale n)) 0)
        (F.profileChart (exponentialRescaleBasis
          (WordBasisSelections.basis X (boundedBracketWords d) βD)
          (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
          (max (Real.log (targetScale n)) 0))) z) →
      let Z := Metric.closedBall (0 : Fin (finrank ℝ H) → ℝ) R
      let bD := WordBasisSelections.basis X (boundedBracketWords d) βD
      let q := ((eW.toLinearMap.comp (heightProjection T.character)).comp
        (H.subtype.comp bD.equivFun.symm.toLinearMap)).toContinuousLinearMap
      let A := fun L : templateSymmetryGroup (M.supportIn T hunimod eW) =>
        (⟨fun z => L.val (q z), L.val.toContinuousLinearEquiv.continuous.comp q.continuous⟩ :
          C((Fin (finrank ℝ H) → ℝ), W)).restrict Z
      let μ := fun n => M.translatedGroupBoxProbability T F hunimod eW
        haarN chartN hchartN bN Eall γ (scale n) 1
      let ν := fun n => M.translatedGroupBoxProbability T F hunimod eW
        haarN chartN hchartN bN Eall γ (targetScale n) 1
      let b := fun n => ∫ k, raw n k 0 ∂(μ n : Measure F.N.carrier)
      let b' := fun n => ∫ k, raw' n k 0 ∂(ν n : Measure F.N.carrier)
      let label := fun n => canonicalAffineLabel (μ n : Measure F.N.carrier)
        (fun k => (raw n k).restrict Z) (fun L => A L + ContinuousMap.const Z (b n))
      let label' := fun n => canonicalAffineLabel (ν n : Measure F.N.carrier)
        (fun k => (raw' n k).restrict Z) (fun L => A L + ContinuousMap.const Z (b' n))
      (∀ᶠ n in atTop, label n = label' n) ∧
        Tendsto (fun n => dist (b n) ((targetScale n / scale n) • b' n)) atTop (𝓝 0) := by
  classical
  obtain ⟨δ₁, hδ₁, hmean₁⟩ := M.exists_uniform_published_affine_mean_approximation T F hunimod eW
    hExp hinj realize haarN haarD dynkinN dynkinD chartN hchartN chartD hchartD m νD
    π hπExp hdec hvan hΛ hπ hpath bN γ hγ X hDnil hDletters bD₀ βD hβD
    aN hmN aD hmD rem hdim pivot hcanonical hunit hcontact hpositive
    hc hhi hB hcost hgap σchamber hσchamber hnz
    sourceInputs sourceDynkin targetInputs hweightB
  obtain ⟨δ₂, hδ₂, hmean₂⟩ := M.exists_uniform_published_affine_mean_approximation T F hunimod eW
    hExp hinj realize haarN haarD dynkinN dynkinD chartN hchartN chartD hchartD m νD
    π hπExp hdec hvan hΛ hπ hpath bN γ hγ X hDnil hDletters bD₀ βD hβD
    aN hmN aD hmD rem hdim pivot hcanonical hunit hcontact hpositive
    hc hhi hB hcost hgap σchamber hσchamber hnz
    sourceInputs sourceDynkin targetInputs hweightB
  obtain ⟨δ₃, hδ₃, hpair⟩ := M.exists_uniform_published_mixed_scale_concentration T F hunimod eW
    hExp hinj realize haarN haarD dynkinN dynkinD chartN hchartN chartD hchartD m νD
    π hπExp hdec hvan hΛ hπ hpath bN γ hγ X hDnil hDletters bD₀ βD hβD
    aN hmN aD hmD rem hdim pivot hcanonical hunit hcontact hpositive
    hc hhi hB hcost hgap σchamber hσchamber hnz
    sourceInputs sourceDynkin targetInputs hweightB
  refine ⟨min δ₁ (min δ₂ δ₃), lt_min hδ₁ (lt_min hδ₂ hδ₃), ?_⟩
  intro δ hδ hd scale hgrows hmono hs1 targetScale htmono hscaleLe hratio R hR hZheight
    pair center raw raw' hraw hraw'
  have ht1 : ∀ n, 1 ≤ targetScale n := fun n => (hs1 n).trans (hscaleLe n)
  have htgrow : Tendsto targetScale atTop atTop := tendsto_atTop_mono hscaleLe hgrows
  dsimp only
  let Z := Metric.closedBall (0 : Fin (finrank ℝ H) → ℝ) R
  let height : H →ₗ[ℝ] W := eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype)
  have hheight : Function.Surjective height := eW.surjective.comp (cartan_height_surjective T H)
  have hkill (u v : H) : height ⁅u, v⁆ = 0 := by
    change eW (heightProjection T.character (⁅u, v⁆ : H)) = 0
    rw [LieSubalgebra.coe_bracket, heightProjection_lie_eq_zero T.character T.character_lie,
      map_zero]
  let μ := fun n => M.translatedGroupBoxProbability T F hunimod eW
    haarN chartN hchartN bN Eall γ (scale n) 1
  let ν := fun n => M.translatedGroupBoxProbability T F hunimod eW
    haarN chartN hchartN bN Eall γ (targetScale n) 1
  let C := fun n => M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) Eall γ (scale n) 1
  let D := fun n => M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) Eall γ (targetScale n) 1
  have hcompact (s : ℕ → ℝ) n : IsCompact
      (M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) Eall γ (s n) 1) :=
    isCompact_exponentialCoordinateBox F.N.equiv.toLinearEquiv F.ExpN chartN hchartN
      (M.boxBasis T hunimod eW Eall γ (s n)) 1 zero_le_one
  have hfull (s : ℕ → ℝ) n : ∀ᵐ k ∂(M.translatedGroupBoxProbability T F hunimod eW
      haarN chartN hchartN bN Eall γ (s n) 1 : Measure F.N.carrier),
      k ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) Eall γ (s n) 1 := by
    have hh := M.groupBox_radius_properties T F hunimod eW haarN chartN hchartN bN
      Eall γ (s n) zero_lt_one
    simpa only [translatedGroupBoxProbability, mul_one, image_id'] using
      ae_mem_cellProbabilityMeasure
        (Measure.map ((F.ExpN ∘ F.N.equiv) ∘ bN.equivFun.symm) volume)
        _ hh.1 hh.2.1 hh.2.2.1
  have hz : (0 : Fin (finrank ℝ H) → ℝ) ∈ Z := Metric.mem_closedBall_self hR.le
  have hh := F.adjacent_scale_labels_of_approximation
    (funext hchartD ▸ chartD.continuous) height hheight hkill
    (fun L : templateSymmetryGroup (M.supportIn T hunimod eW) => L.val) Subtype.val_injective
    X (boundedBracketWords d) βD μ ν C D (hcompact scale) (hcompact targetScale)
    (hfull scale) (hfull targetScale) scale targetScale hs1 hscaleLe
    (K := 1 + δ) (by linarith) hratio
    (fun n g => (π ((pair n).val.1 g)).toAdd)
    (fun n => (hπ.comp (pair n).property.1.1).continuous) center raw raw'
    (by simpa only [bracketWordExponent_one] using hraw)
    (by simpa only [bracketWordExponent_one] using hraw') R hR
    (hmean₁ δ hδ (hd.trans (min_le_left _ _)) scale hgrows hmono hs1 Z inferInstance hZheight hz pair center raw hraw)
    (hmean₂ δ hδ (hd.trans ((min_le_right _ _).trans (min_le_left _ _)))
      targetScale htgrow htmono ht1 Z inferInstance hZheight hz pair center raw' hraw')
    (fun ε hε => by
      simpa only [μ, ν, dist_comm] using
        hpair δ hδ (hd.trans ((min_le_right _ _).trans (min_le_right _ _)))
          scale hgrows hmono hs1 Z inferInstance hZheight targetScale hscaleLe hratio pair center raw hraw hε)
  simpa only [μ, ν, height, Z, LinearMap.comp_assoc] using hh

end PolycyclicRecognition.CartanWordModel

end

end OAI

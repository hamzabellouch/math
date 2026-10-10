import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanPublishedScaleStabilization
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanCanonicalProfiles
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanOrdinaryMetricBound
import OAI.GroupTheory.PolycyclicRecognition.Analysis.ScaleLabelStabilization
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

/-! # Uniform scale stabilization and vanishing mean offsets -/

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

/-- The scale-stabilization lemma for the original Haar profiles, uniformly
over all normalized maps and centers, from the precise published inputs. -/
theorem exists_published_uniform_scale_stabilization
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
      ∀ R : ℝ, 0 < R →
      (∀ z ∈ Metric.closedBall (0 : Fin (finrank ℝ H) → ℝ) R,
        eW (heightProjection T.character
          ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
            GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈
          (fun w => (1 - c * δ) • w) '' interior Eall) →
      let Z := Metric.closedBall (0 : Fin (finrank ℝ H) → ℝ) R
      let bD := WordBasisSelections.basis X (boundedBracketWords d) βD
      let q := ((eW.toLinearMap.comp (heightProjection T.character)).comp
        (H.subtype.comp bD.equivFun.symm.toLinearMap)).toContinuousLinearMap
      let A := fun L : templateSymmetryGroup (M.supportIn T hunimod eW) =>
        (⟨fun z => L.val (q z), L.val.toContinuousLinearEquiv.continuous.comp q.continuous⟩ :
          C((Fin (finrank ℝ H) → ℝ), W)).restrict Z
      let μ := fun r => M.translatedGroupBoxProbability T F hunimod eW
        haarN chartN hchartN bN Eall γ r 1
      let raw := fun (p : NormalizedPair G Λ × G) r =>
        F.realScaleProfile (funext hchartD ▸ chartD.continuous)
          (fun g => (π (p.1.val.1 g)).toAdd) (hπ.comp p.1.property.1.1).continuous
          p.2 X (boundedBracketWords d) βD r
      let b := fun p r => ∫ k, raw p r k 0 ∂(μ r : Measure F.N.carrier)
      let label := fun p r => canonicalAffineLabel (μ r : Measure F.N.carrier)
        (fun k => (raw p r k).restrict Z) (fun L => A L + ContinuousMap.const Z (b p r))
      (∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ p r, R₀ ≤ r → label p r = label p R₀) ∧
      (∀ ε : ℝ, 0 < ε → ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ p r, R₀ ≤ r → ‖b p r‖ ≤ ε) := by
  obtain ⟨δ₀, hδ₀, hcompare⟩ := M.exists_published_adjacent_scale_labels T F hunimod eW
    hExp hinj realize haarN haarD dynkinN dynkinD chartN hchartN chartD hchartD m νD
    π hπExp hdec hvan hΛ hπ hpath bN γ hγ X hDnil hDletters bD₀ βD hβD
    aN hmN aD hmD rem hdim pivot hcanonical hunit hcontact hpositive
    hc hhi hB hcost hgap σchamber hσchamber hnz
    sourceInputs sourceDynkin targetInputs hweightB
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ hd R hR hZheight
  dsimp only
  let Z := Metric.closedBall (0 : Fin (finrank ℝ H) → ℝ) R
  let bD := WordBasisSelections.basis X (boundedBracketWords d) βD
  let q := ((eW.toLinearMap.comp (heightProjection T.character)).comp
    (H.subtype.comp bD.equivFun.symm.toLinearMap)).toContinuousLinearMap
  let A := fun L : templateSymmetryGroup (M.supportIn T hunimod eW) =>
    (⟨fun z => L.val (q z), L.val.toContinuousLinearEquiv.continuous.comp q.continuous⟩ :
      C((Fin (finrank ℝ H) → ℝ), W)).restrict Z
  let μ := fun r => M.translatedGroupBoxProbability T F hunimod eW
    haarN chartN hchartN bN Eall γ r 1
  let J := fun (p : NormalizedPair G Λ × G) g => (π (p.1.val.1 g)).toAdd
  have hJ p : LipschitzWith (Kπ * Λ) (J p) := hπ.comp p.1.property.1.1
  let raw := fun (p : NormalizedPair G Λ × G) r =>
    F.realScaleProfile (funext hchartD ▸ chartD.continuous) (J p) (hJ p).continuous
      p.2 X (boundedBracketWords d) βD r
  let b := fun p r => ∫ k, raw p r k 0 ∂(μ r : Measure F.N.carrier)
  let label := fun p r => canonicalAffineLabel (μ r : Measure F.N.carrier)
    (fun k => (raw p r k).restrict Z) (fun L => A L + ContinuousMap.const Z (b p r))
  have hE := M.isCompact_samplingPolytope T hunimod eW
  have hne : (Eall).Nonempty := ⟨0, fun i => by simp only [map_zero]; exact norm_nonneg _⟩
  obtain ⟨C, _, hmetric⟩ := M.exists_ordinary_cell_metric_bound T F hunimod eW
    hExp realize haarN dynkinN bN hE hne (M.sampling_weightSupport_pos T hunimod eW) γ hγ
  have hfull r : ∀ᵐ k ∂(μ r : Measure F.N.carrier),
      k ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) Eall γ r 1 := by
    have hh := M.groupBox_radius_properties T F hunimod eW haarN chartN hchartN bN
      Eall γ r zero_lt_one
    simpa only [μ, translatedGroupBoxProbability, mul_one, image_id'] using
      ae_mem_cellProbabilityMeasure
        (Measure.map ((F.ExpN ∘ F.N.equiv) ∘ bN.equivFun.symm) volume)
        _ hh.1 hh.2.1 hh.2.2.1
  have hb p r (hr : 1 ≤ r) : ‖b p r‖ ≤ (Kπ * Λ : ℝ≥0) * C := by
    apply F.realScaleProfile_mean_norm_le (funext hchartD ▸ chartD.continuous)
      (J p) (hJ p) p.2 X (boundedBracketWords d) βD hr (μ r)
    filter_upwards [hfull r] with k hk
    exact hmetric r hr k hk
  apply uniform_scale_stabilization_of_sequences label b (Q := 1 + δ) (by linarith) hb
  intro p r t hrg hr ht hr1 hrt htQ
  have hh := hcompare δ hδ hd r hrg hr hr1 t ht hrt htQ R hR hZheight
    (fun n => (p n).1) (fun n => (p n).2)
    (fun n => raw (p n) (r n)) (fun n => raw (p n) (t n))
    (fun _ _ _ => rfl) (fun _ _ _ => rfl)
  exact hh

end PolycyclicRecognition.CartanWordModel

end

end OAI

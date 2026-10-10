import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanPublishedChainConcentration
import OAI.GroupTheory.PolycyclicRecognition.Geometry.UniversalAllScaleCartanProfiles
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

/-! # Finite-chain concentration from the precisely published inputs -/

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

/-- The compact profile family is constructed before the enlargement threshold,
uniformly in all maps and centers. The conclusion concerns the original raw
profiles and assumes no compactness or convergence for their laws. -/
theorem exists_uniform_published_raw_chain_concentration
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
    (C : ℝ) (hC : 0 ≤ C) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ (scale : ℕ → ℝ) (_hgrows : Tendsto scale atTop atTop)
        (_hmono : StrictMono scale) (_hs1 : ∀ n, 1 ≤ scale n),
      ∀ Z : Set (Fin (finrank ℝ H) → ℝ), ∀ _ : CompactSpace Z,
      (∀ z ∈ Z, eW (heightProjection T.character
        ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
          GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈ (fun w => (1 - c * δ) • w) '' interior Eall) →
      ∀ (pair : ℕ → NormalizedPair G Λ) (center : ℕ → G)
    (radius : ℕ → ℝ) (_hr0 : ∀ n, 0 ≤ radius n)
    (_hr : HasSubexponentialUpperBoundSeq scale radius)
    {N : ℕ} (base : ℕ → Fin (N + 1) → F.N.carrier)
    (step : ℕ → Fin N → F.N.carrier)
    (_hbase : ∀ n j, base n j ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
      ((fun w => (1 + δ) • w) '' Eall) γ (scale n) (radius n))
    (_hstep : ∀ n j, step n j ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
      ((fun w => (1 + δ) • w) '' Eall) γ (scale n) (radius n))
    (_hnext : ∀ n j, base n j.succ = base n j.castSucc * step n j)
    (mode : ℕ → Fin N → Fin M.letterCount) (time : ℕ → Fin N → ℝ)
    (_htime : ∀ n j, |time n j| ≤ radius n * Real.exp
      ((M.weight (mode n j) (pivot (mode n j)) + δ * B) * scale n))
    (_hroot : ∀ n j, F.inclusionN (step n j) =
      Exp (time n j • (M.letter (mode n j) : GroupLieAlgebra (𝓘(ℝ, EG)) G)))
    (raw : ℕ → F.N.carrier → C((Fin (finrank ℝ H) → ℝ), W))
    (_hraw : ∀ n q z, raw n q z = rescaledMapProfile
      (fun g => (π ((pair n).val.1 g)).toAdd) (center n) (F.inclusionN q)
      (max (Real.log (scale n)) 0)
      (F.profileChart (exponentialRescaleBasis
        (WordBasisSelections.basis X (boundedBracketWords d) βD)
        (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
        (max (Real.log (scale n)) 0))) z)
    (_hmetric : ∀ᶠ n in atTop, ∀ j q, q ∈ (fun v => v * base n j) ''
      M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) Eall γ (scale n) 1 →
      dist 1 (F.inclusionN q) / scale n ≤ C)
    (j : Fin (N + 1)) {η : ℝ} (_hη : 0 < η),
    Tendsto (fun n => (M.translatedGroupBoxProbability T F hunimod eW
      haarN chartN hchartN bN Eall γ (scale n) 1 : Measure F.N.carrier)
      {q | η ≤ dist ((raw n (q * base n j)).restrict Z)
        ((raw n (q * base n 0)).restrict Z)}) atTop (𝓝 0) := by
  obtain ⟨S, hS, hmem⟩ := exists_universal_compact_cartan_profiles_all_scales (W := W) T F
    hExp realize haarD dynkinD X hDnil hDletters bD₀ βD hβD (Kπ * Λ) C
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  obtain ⟨δ₀, hδ₀, hconc⟩ := M.exists_uniform_published_chain_concentration T F hunimod eW
    hExp hinj realize haarN haarD dynkinN dynkinD chartN hchartN chartD hchartD m νD
    π hπExp hdec hvan hΛ hπ hpath bN γ hγ X hDnil hDletters bD₀ βD hβD
    aN hmN aD hmD rem hdim pivot hcanonical hunit hcontact hpositive
    hc hhi hB hcost hgap σchamber hσchamber S hS hnz
    sourceInputs sourceDynkin targetInputs
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ hd scale hgrows hmono hs1 Z hZ hZheight pair center radius hr0 hradius N base step
    hbase hstep hnext mode time htime hroot raw hraw hmetric j η hη
  let r := fun n => max (Real.log (scale n)) 0
  have hr n : r n = Real.log (scale n) := max_eq_left (Real.log_nonneg (hs1 n))
  have hexp n : Real.exp (r n) = scale n := by
    rw [hr, Real.exp_log (zero_lt_one.trans_le (hs1 n))]
  let := hZ
  let J := fun n g => (π ((pair n).val.1 g)).toAdd
  have hJ n : LipschitzWith (Kπ * Λ) (J n) := hπ.comp (pair n).property.1.1
  let φ := fun n => F.profileChart (exponentialRescaleBasis
    (WordBasisSelections.basis X (boundedBracketWords d) βD)
    (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)) (r n))
  have hφ n : Continuous (φ n) :=
    F.continuous_profileChart (funext hchartD ▸ chartD.continuous) _
  let cells := fun n => {q : F.N.carrier | dist 1 (F.inclusionN q) / scale n ≤ C}
  have hcells n : MeasurableSet (cells n) :=
    (isClosed_le ((continuous_const.dist F.closedN.continuous).div_const _) continuous_const).measurableSet
  have hcellne n : (cells n).Nonempty := ⟨1, by
    change dist 1 (F.inclusionN 1) / scale n ≤ C
    simpa only [map_one, dist_self, zero_div] using hC⟩
  have hm n q (hq : q ∈ cells n) :
      rescaledContinuousProfile (J n) (hJ n).continuous (center n) (F.inclusionN q)
        (r n) (φ n) (hφ n) ∈ S := by
    obtain ⟨f, hf, he⟩ := hmem (r n) (le_max_right _ _) (J n) (hJ n) (center n) (F.inclusionN q)
      (by simpa only [hexp] using (show dist 1 (F.inclusionN q) / scale n ≤ C from hq))
    have heq : rescaledContinuousProfile (J n) (hJ n).continuous (center n)
        (F.inclusionN q) (r n) (φ n) (hφ n) = f := by
      ext z
      exact (he z).symm
    exact heq ▸ hf
  have hprofiles n := exists_measurable_borel_sampled_profile (J n) (hJ n).continuous
    (center n) (r n) (φ n) (hφ n) F.inclusionN F.closedN.continuous.measurable
    (cells n) (hcells n) (hcellne n) S (hm n)
  choose profile hp ha using hprofiles
  have heq n q (hq : q ∈ cells n) : (profile n q).val = raw n q := by
    ext z
    exact (ha n q hq z).trans (hraw n q z).symm
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hmetric
  have hm' n := hn₀ (n + n₀) (Nat.le_add_left n₀ n)
  have hc' := hconc δ hδ hd Z hZ hZheight
    (fun n => scale (n + n₀)) (hgrows.comp (tendsto_add_atTop_nat n₀))
    (hmono.comp (strictMono_id.add_const n₀)) (fun n => hs1 (n + n₀))
    (fun n => pair (n + n₀)) (fun n => center (n + n₀))
    (fun n => radius (n + n₀)) (fun n => hr0 (n + n₀))
    (fun ε hε => (tendsto_add_atTop_nat n₀).eventually (hradius ε hε))
    (fun n => base (n + n₀)) (fun n => step (n + n₀))
    (fun n => hbase (n + n₀)) (fun n => hstep (n + n₀)) (fun n => hnext (n + n₀))
    (fun n => mode (n + n₀)) (fun n => time (n + n₀))
    (fun n => htime (n + n₀)) (fun n => hroot (n + n₀))
    (fun n => profile (n + n₀)) (fun n => hp (n + n₀))
    (fun n k q hq z => ha (n + n₀) q (hm' n k q hq) z) j hη
  apply (tendsto_add_atTop_iff_nat n₀).mp
  apply hc'.congr'
  filter_upwards [] with n
  apply measure_congr
  have hprops := M.translated_groupBox_cell_properties T F hunimod eW
    haarN chartN hchartN bN Eall γ (scale (n + n₀)) 1
  filter_upwards [ae_mem_cellProbabilityMeasure _ _ hprops.1 hprops.2.1 hprops.2.2] with q hq
  have hq' : q ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) Eall γ (scale (n + n₀)) 1 := by
    simpa only [mul_one, image_id'] using hq
  have hj := heq (n + n₀) (q * base (n + n₀) j) (hm' n j _ ⟨q, hq', rfl⟩)
  have hz := heq (n + n₀) (q * base (n + n₀) 0) (hm' n 0 _ ⟨q, hq', rfl⟩)
  simp only [hj, hz]

end PolycyclicRecognition.CartanWordModel

end

end OAI

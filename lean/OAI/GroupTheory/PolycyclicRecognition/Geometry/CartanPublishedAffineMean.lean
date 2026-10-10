import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanPublishedOrdinaryConcentration
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

/-! # Mean-normalized affine approximation of the original ordinary charts -/

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

/-- The original ordinary Haar profiles have deterministic affine approximants
whose offset is exactly their mean value at the identity. -/
theorem exists_uniform_published_affine_mean_approximation
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
        (_hmono : StrictMono scale) (_hs1 : ∀ n, 1 ≤ scale n),
      ∀ Z : Set (Fin (finrank ℝ H) → ℝ), ∀ _ : CompactSpace Z,
      (∀ z ∈ Z, eW (heightProjection T.character
        ((WordBasisSelections.basis X (boundedBracketWords d) βD).equivFun.symm z :
          GroupLieAlgebra (𝓘(ℝ, EG)) G)) ∈ (fun w => (1 - c * δ) • w) '' interior Eall) →
      (0 : Fin (finrank ℝ H) → ℝ) ∈ Z →
      ∀ (pair : ℕ → NormalizedPair G Λ) (center : ℕ → G)
    (raw : ℕ → F.N.carrier → C((Fin (finrank ℝ H) → ℝ), W))
    (_hraw : ∀ n q z, raw n q z = rescaledMapProfile
      (fun g => (π ((pair n).val.1 g)).toAdd) (center n) (F.inclusionN q)
      (max (Real.log (scale n)) 0)
      (F.profileChart (exponentialRescaleBasis
        (WordBasisSelections.basis X (boundedBracketWords d) βD)
        (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
        (max (Real.log (scale n)) 0))) z),
    let bD := WordBasisSelections.basis X (boundedBracketWords d) βD
    let q := ((eW.toLinearMap.comp (heightProjection T.character)).comp
      (H.subtype.comp bD.equivFun.symm.toLinearMap)).toContinuousLinearMap
    let A := fun L : templateSymmetryGroup (M.supportIn T hunimod eW) =>
      (⟨fun z => L.val (q z), L.val.toContinuousLinearEquiv.continuous.comp q.continuous⟩ :
        C((Fin (finrank ℝ H) → ℝ), W)).restrict Z
    let μ := fun n => M.translatedGroupBoxProbability T F hunimod eW
      haarN chartN hchartN bN Eall γ (scale n) 1
    ∃ label : ℕ → templateSymmetryGroup (M.supportIn T hunimod eW),
      Tendsto (fun n => ∫ v, dist ((raw n v).restrict Z)
        (A (label n) + ContinuousMap.const Z (∫ w, raw n w 0 ∂(μ n : Measure F.N.carrier)))
        ∂(μ n : Measure F.N.carrier)) atTop (𝓝 0) := by
  obtain ⟨δ₁, hδ₁, hconc⟩ := M.exists_uniform_published_ordinary_concentration T F hunimod eW
    hExp hinj realize haarN haarD dynkinN dynkinD chartN hchartN chartD hchartD m νD
    π hπExp hdec hvan hΛ hπ hpath bN γ hγ X hDnil hDletters bD₀ βD hβD
    aN hmN aD hmD rem hdim pivot hcanonical hunit hcontact hpositive
    hc hhi hB hcost hgap σchamber hσchamber hnz
    sourceInputs sourceDynkin targetInputs hweightB
  let δ₀ := min δ₁ (1 / (2 * (c + 1)))
  refine ⟨δ₀, lt_min hδ₁ (by positivity), ?_⟩
  intro δ hδ hd scale hgrows hmono hs1 Z hZ hZheight hZzero pair center raw hraw
  dsimp only
  let := hZ
  have hδbound : δ * (2 * (c + 1)) ≤ 1 :=
    (le_div_iff₀ (by positivity : 0 < 2 * (c + 1))).mp (hd.trans (min_le_right _ _))
  have ht : 0 < 1 - c * δ := by nlinarith [mul_nonneg hc hδ.le]
  let J := fun n g => (π ((pair n).val.1 g)).toAdd
  have hJ n : LipschitzWith (Kπ * Λ) (J n) := hπ.comp (pair n).property.1.1
  have hE := M.isCompact_samplingPolytope T hunimod eW
  have hne : (Eall).Nonempty := ⟨0, fun i => by simp only [map_zero]; exact norm_nonneg _⟩
  obtain ⟨n₀, S, hS, profile, hp, hactual⟩ := M.exists_compact_measurable_box_profiles
    T F hunimod eW hExp realize haarN haarD dynkinN dynkinD chartN hchartN
    X hDnil hDletters bD₀ βD hβD bN hE hne γ hγ
    (M.sampling_weightSupport_pos T hunimod eW) (δ := 0) le_rfl
    scale (fun _ => 0) hgrows hs1 (fun _ => le_rfl)
    (sequence_subexponential_upper_const hgrows 0) J hJ center
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let C n := M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) Eall γ (scale (n + n₀)) 1
  let μ n := M.translatedGroupBoxProbability T F hunimod eW
    haarN chartN hchartN bN Eall γ (scale (n + n₀)) 1
  let ν n := ProbabilityMeasure.map (μ n) (profile n)
  let bD := WordBasisSelections.basis X (boundedBracketWords d) βD
  let q := ((eW.toLinearMap.comp (heightProjection T.character)).comp
    (H.subtype.comp bD.equivFun.symm.toLinearMap)).toContinuousLinearMap
  let A := fun L : templateSymmetryGroup (M.supportIn T hunimod eW) =>
    (⟨fun z => L.val (q z), L.val.toContinuousLinearEquiv.continuous.comp q.continuous⟩ :
      C((Fin (finrank ℝ H) → ℝ), W)).restrict Z
  let obs : S → C(Z, W) := fun f => f.val.restrict Z
  have hobs : Continuous obs := (ContinuousMap.continuous_restrict Z).comp continuous_subtype_val
  have ha n v (hv : v ∈ C n) : (profile n v).val = raw (n + n₀) v := by
    ext z
    have h1 : (1 : F.N.carrier) ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
        ((fun w => (1 + (0 : ℝ)) • w) '' Eall) γ (scale (n + n₀)) 0 :=
      ⟨0, by simp [F.isExpN.map_zero], by simp⟩
    exact (hactual n 1 h1 v ⟨v, hv, mul_one v⟩ z).trans (hraw (n + n₀) v z).symm
  have hfull n : ∀ᵐ v ∂(μ n : Measure F.N.carrier), v ∈ C n := by
    have hh := M.groupBox_radius_properties T F hunimod eW haarN chartN hchartN bN
      Eall γ (scale (n + n₀)) zero_lt_one
    simpa only [μ, C, translatedGroupBoxProbability, mul_one, image_id'] using
      ae_mem_cellProbabilityMeasure
        (Measure.map ((F.ExpN ∘ F.N.equiv) ∘ bN.equivFun.symm) volume)
        (C n) hh.1 hh.2.1 hh.2.2.1
  have heq n : ∀ᵐ v ∂(μ n : Measure F.N.carrier), obs (profile n v) = (raw (n + n₀) v).restrict Z := by
    filter_upwards [hfull n] with v hv
    exact congrArg (fun f => f.restrict Z) (ha n v hv)
  have hpair : ∀ ε : ℝ, 0 < ε → Tendsto (fun n =>
      (ν n : Measure S).prod (ν n : Measure S) {p | ε ≤ dist (obs p.1) (obs p.2)})
        atTop (𝓝 0) := by
    intro ε hε
    have hh := (hconc δ hδ (hd.trans (min_le_left _ _)) scale hgrows hmono hs1 Z hZ hZheight
      pair center raw hraw hε).comp (tendsto_add_atTop_nat n₀)
    apply hh.congr'
    filter_upwards [] with n
    have hprob := probability_map_pair_distance_of_ae_eq (μ n) (profile n) (hp n)
      obs (fun v => (raw (n + n₀) v).restrict Z) (heq n) ε
      (isClosed_le continuous_const ((hobs.comp continuous_fst).dist
        (hobs.comp continuous_snd))).measurableSet
    simpa only [dist_comm, μ, ν, Function.comp_apply] using hprob.symm
  let U := q ⁻¹' ((fun w => (1 - c * δ) • w) '' interior Eall)
  have hU : IsOpen U := (isOpenMap_smul₀ ht.ne' _ isOpen_interior).preimage q.continuous
  have hUconv : Convex ℝ U :=
    ((convex_weightSamplingPolytope _).interior.smul (1 - c * δ)).linear_preimage q.toLinearMap
  have hZU : Z ⊆ U := hZheight
  have hUne : U.Nonempty := ⟨0, hZU hZzero⟩
  have haffine : ∀ ε : ℝ, 0 < ε → Tendsto (fun n => (ν n : Measure S)
      {f | ε ≤ Metric.infDist (obs f) (affineProfileClass A)}) atTop (𝓝 0) := by
    intro ε hε
    have hh := M.cartan_cell_affine_distance_tendsto_zero T F hunimod eW
      hExp realize haarN haarD dynkinN dynkinD m π hπExp hdec hvan hΛ hπ hpath
      chartN hchartN bN hE hne γ γ hγ hδ hc hhi ht.le hcost hgap
      X hDnil hDletters bD₀ βD hβD aN hmN aD hmD
      (fun n => scale (n + n₀)) (hgrows.comp (tendsto_add_atTop_nat n₀))
      (hmono.comp (strictMono_id.add_const n₀)) (fun n => hs1 (n + n₀))
      (fun _ => 0) (fun _ => le_rfl) tendsto_const_nhds (fun _ => 0)
      (Eventually.of_forall (fun n => by simp)) rem hdim
      (fun n => pair (n + n₀)) (fun n => center (n + n₀)) S hS profile hp
      (by
        intro n v hv z
        have hv' : v ∈ C n := by simpa only [map_zero, F.isExpN.map_zero, mul_one, image_id'] using hv
        exact (congrArg (fun f : C((Fin (finrank ℝ H) → ℝ), W) => f z)
          (ha n v hv')).trans (hraw (n + n₀) v z))
      U hU hUconv.isPreconnected hUne
      (by
        intro z hz
        obtain ⟨w, hw, he⟩ := hz
        exact ⟨w, interior_subset hw, he⟩)
      σchamber hσchamber Z (isCompact_iff_compactSpace.mpr hZ) hZU hε
    simpa only [ν, obs, A, q, bD, map_zero, F.isExpN.map_zero] using hh
  obtain ⟨label, hlabel⟩ := exists_mean_normalized_affine_approximation obs hobs A
    ⟨0, hZzero⟩ (fun L => by simp [A, q]) ν hpair haffine
  have hmean n : (∫ f, obs f ⟨0, hZzero⟩ ∂(ν n : Measure S)) =
      ∫ v, raw (n + n₀) v 0 ∂(μ n : Measure F.N.carrier) := by
    exact integral_profile_value_map (μ n) (profile n) (hp n)
      (fun f => obs f ⟨0, hZzero⟩) ((continuous_eval_const _).comp hobs)
      (fun v => raw (n + n₀) v 0)
      ((heq n).mono (fun v hv => congrArg (fun f => f ⟨0, hZzero⟩) hv))
  refine ⟨fun n => label (n - n₀), ?_⟩
  apply (tendsto_add_atTop_iff_nat n₀).mp
  apply hlabel.congr'
  filter_upwards [] with n
  rw [hmean]
  have he := integral_profile_distance_map (μ n) (profile n) (hp n) obs hobs
    (fun v => (raw (n + n₀) v).restrict Z) (heq n)
    (A (label n) + ContinuousMap.const Z (∫ v, raw (n + n₀) v 0 ∂(μ n : Measure F.N.carrier)))
  simpa only [Nat.add_sub_cancel, ν, μ, A, q, bD] using he

end PolycyclicRecognition.CartanWordModel

end

end OAI

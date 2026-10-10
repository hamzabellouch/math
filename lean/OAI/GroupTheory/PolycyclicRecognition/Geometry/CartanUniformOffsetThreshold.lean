import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanOneConeThreshold
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanNeighborRowOffsetsEqual
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanFixedPolarTargets
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanFixedSamplingGeometry
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanCanonicalPolarSamplers
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanContactStepBridge
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SmallFactorCell
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanOffsetThreshold

namespace OAI

/-! # One offset threshold for every original root neighbor -/

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

/-- The source and target cone models are fixed on a finite family. The
published estimates then give one threshold for all scales, maps and
supported neighboring profiles with a common affine label. -/
theorem exists_uniform_polar_offset_threshold
    (hExp : IsGroupExponential Exp)
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
    (νD : Measure F.D.carrier) [νD.IsHaarMeasure] [SFinite νD]
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
    (Profiles : Set C((Fin (finrank ℝ H) → ℝ), W))
    [MeasurableSpace Profiles] [BorelSpace Profiles] [BorelSpace (Profiles × Profiles)]
    (hnz : ∀ i, (M.supportIn T hunimod eW).weight i ≠ 0)
    (Ds : ∀ (i : Fin M.letterCount) (s : rootOffsetConeIndex (M.supportIn T hunimod eW) i),
      M.MeasuredCone F (heightConePreimage T eW
        (rootOffsetCone (M.supportIn T hunimod eW) hnz i s)))
    (dynkinI : ∀ i s, NilpotentDynkinExpansionInput (Ds i s).I.modelSpace (Ds i s).I.carrier)
    (haarI : ∀ i s, NilpotentExponentialHaarInput (Ds i s).I.modelSpace (Ds i s).I.carrier)
    (Dt : ∀ (i : Fin M.letterCount) (A : templateSymmetryGroup (M.supportIn T hunimod eW))
      (s : rootOffsetConeIndex (M.supportIn T hunimod eW) i),
      M.MeasuredCone F (heightConePreimage T eW
        (transformedPolarCone (rootOffsetCone (M.supportIn T hunimod eW) hnz i s) A.val)))
    (haarQt : ∀ i A s, NilpotentExponentialHaarInput (Dt i A s).Q.modelSpace (Dt i A s).Q.carrier)
    (haarIt : ∀ i A s, NilpotentExponentialHaarInput (Dt i A s).I.modelSpace (Dt i A s).I.carrier) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∀ row : AffineNeighborRow T M F hunimod eW π bN Eall γ X βD
        haarN chartN hchartN pivot c B δ Profiles (Λ := Λ),
      row.label₂ = row.label₁ → row.offset₁ = row.offset₂ := by
  have hE : IsCompact Eall := M.isCompact_samplingPolytope T hunimod eW
  have hne : (Eall).Nonempty := ⟨0, by
    intro j
    simpa only [map_zero] using norm_nonneg (((M.supportIn T hunimod eW).weight j).toContinuousLinearMap)⟩
  apply exists_uniform_neighbor_offset_threshold T M F hunimod eW π bN Eall γ X βD
    haarN chartN hchartN pivot c B Profiles hExp dynkinN hE hne hγ hnz
  intro i A s
  exact M.exists_one_cone_offset_threshold T F hunimod eW
    hExp realize haarN haarD dynkinN dynkinD chartN hchartN chartD hchartD m νD
    π hπExp hdec hvan hΛ hπ hpath bN γ hγ X hDnil hDletters bD₀ βD hβD
    aN hmN aD hmD rem hdim pivot i (hcanonical i) (hunit i) (hcontact i) (hpositive i)
    hc hhi hB hcost hgap σchamber hσchamber Profiles
    (rootOffsetCone (M.supportIn T hunimod eW) hnz i s)
    (rootOffsetCone_salient (M.supportIn T hunimod eW) hnz i s)
    (weight_mem_rootOffsetCone (M.supportIn T hunimod eW) hnz i s)
    A (Ds i s) (dynkinI i s) (haarI i s) (Dt i A s) (haarQt i A s) (haarIt i A s)

end PolycyclicRecognition.CartanWordModel

end

end OAI

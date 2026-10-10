import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanPublishedProfileEstimates
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanMetricBasepointComparison

namespace OAI

/-! # Published-input comparison at nearby basepoints -/

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

/-- Nearby centers have the same finite affine label, and the normalized
center-height error vanishes. All geometric and analytic bridge assumptions
are derived from the precise published inputs already used for the profiles. -/
theorem exists_uniform_published_basepoint_comparison
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
      ∃ η : ℝ, 0 < η ∧ ∀ (scale : ℕ → ℝ), Tendsto scale atTop atTop →
        StrictMono scale → (∀ n, 1 ≤ scale n) →
        (∀ n, 1 ≤ (1 - δ / 2) * scale n) →
        ∀ (pair : ℕ → NormalizedPair G Λ) (x y : ℕ → G),
        (∀ n, dist (x n) (y n) ≤ η * scale n) →
        (∀ᶠ n in atTop, label (pair n, x n) (scale n) =
          label (pair n, y n) ((1 - δ / 2) * scale n)) ∧
        Tendsto (fun n => (scale n)⁻¹ •
          ((π ((pair n).val.1 (y n))).toAdd - (π ((pair n).val.1 (x n))).toAdd -
            (label (pair n, y n) ((1 - δ / 2) * scale n)).val
              ((π ((x n)⁻¹ * y n)).toAdd))) atTop (𝓝 0) := by
  classical
  obtain ⟨δ₁, hδ₁, hestimates⟩ := M.exists_uniform_published_profile_estimates T F hunimod eW
    hExp hinj realize haarN haarD dynkinN dynkinD chartN hchartN chartD hchartD m νD
    π hπExp hdec hvan hΛ hπ hpath bN γ hγ X hDnil hDletters bD₀ βD hβD
    aN hmN aD hmD rem hdim pivot hcanonical hunit hcontact hpositive
    hc hhi hB hcost hgap σchamber hσchamber hnz sourceInputs sourceDynkin targetInputs hweightB
  let δ₀ := min (1 / 2) δ₁
  refine ⟨δ₀, lt_min (by norm_num) hδ₁, ?_⟩
  intro δ hδ hδle R hR hZheight
  have hd1 : δ ≤ δ₁ := hδle.trans (min_le_right _ _)
  have hδlt : δ < 1 := lt_of_le_of_lt (hδle.trans (min_le_left _ _)) (by norm_num)
  have estimates := hestimates δ hδ hd1 R hR hZheight
  dsimp only
  let A := fun L : templateSymmetryGroup (M.supportIn T hunimod eW) =>
    L.val.toContinuousLinearEquiv.toContinuousLinearMap
  have hA : Function.Injective A := by
    intro a a' he
    apply Subtype.ext
    ext w
    exact DFunLike.congr_fun he w
  have hE := M.isCompact_samplingPolytope T hunimod eW
  have hne : (Eall).Nonempty := ⟨0, fun i => by simp only [map_zero]; exact norm_nonneg _⟩
  have hlo : 0 < lo := by
    by_contra hn
    have hh := mul_nonpos_of_nonneg_of_nonpos hc (le_of_not_gt hn)
    have hn' := mul_nonneg (Nat.cast_nonneg M.bound) hhi
    linarith only [hgap, hh, hn']
  exact M.exists_metric_basepoint_comparison T F hunimod eW π hπExp chartN hchartN
    chartD hchartD dynkinN dynkinD hExp realize bN γ hpath Kπ.coe_nonneg
    (fun x y => by simpa only [dist_eq_norm] using hπ.dist_le_mul x y)
    X hDnil bD₀ βD hβD aD hmD haarN haarD Eall hE hne γ hγ hlo
    (fun w => (hcost w).1) hδ hδlt hR
    (fun p : NormalizedPair G Λ => fun g => (π (p.val.1 g)).toAdd)
    (fun p => (hπ.comp p.property.1.1).continuous) A hA estimates

end PolycyclicRecognition.CartanWordModel

end

end OAI

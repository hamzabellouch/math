import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanPublishedBasepointComparison
import OAI.GroupTheory.PolycyclicRecognition.Geometry.UniformBasepointHeight

namespace OAI

/-! # Uniform sublinear affine height from precisely published inputs -/

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

/-- The stabilized finite label is independent of the basepoint, and the
height error is sublinear uniformly over normalized maps and centers. -/
theorem exists_uniform_published_sublinear_height
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
      ∃ A : NormalizedPair G Λ → templateSymmetryGroup (M.supportIn T hunimod eW),
      ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ p x y,
        ‖(π (p.val.1 y)).toAdd - (π (p.val.1 x)).toAdd - (A p).val ((π (x⁻¹ * y)).toAdd)‖ ≤
          ε * dist x y + B := by
  classical
  obtain ⟨δ₁, hδ₁, hbase⟩ := M.exists_uniform_published_basepoint_comparison T F hunimod eW
    hExp hinj realize haarN haarD dynkinN dynkinD chartN hchartN chartD hchartD m νD
    π hπExp hdec hvan hΛ hπ hpath bN γ hγ X hDnil hDletters bD₀ βD hβD
    aN hmN aD hmD rem hdim pivot hcanonical hunit hcontact hpositive
    hc hhi hB hcost hgap σchamber hσchamber hnz sourceInputs sourceDynkin targetInputs hweightB
  obtain ⟨δ₂, hδ₂, hscale⟩ := M.exists_published_uniform_scale_stabilization T F hunimod eW
    hExp hinj realize haarN haarD dynkinN dynkinD chartN hchartN chartD hchartD m νD
    π hπExp hdec hvan hΛ hπ hpath bN γ hγ X hDnil hDletters bD₀ βD hβD
    aN hmN aD hmD rem hdim pivot hcanonical hunit hcontact hpositive
    hc hhi hB hcost hgap σchamber hσchamber hnz sourceInputs sourceDynkin targetInputs hweightB
  refine ⟨min (1 / 2) (min δ₁ δ₂), lt_min (by norm_num) (lt_min hδ₁ hδ₂), ?_⟩
  intro δ hδ hd R hR hZheight
  have hd1 : δ ≤ δ₁ := hd.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hd2 : δ ≤ δ₂ := hd.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨η, hη, hcompare⟩ := hbase δ hδ hd1 R hR hZheight
  obtain ⟨r₀, hr₀, hstable⟩ := (hscale δ hδ hd2 R hR hZheight).1
  let Z := Metric.closedBall (0 : Fin (finrank ℝ H) → ℝ) R
  let bD := WordBasisSelections.basis X (boundedBracketWords d) βD
  let q := ((eW.toLinearMap.comp (heightProjection T.character)).comp
    (H.subtype.comp bD.equivFun.symm.toLinearMap)).toContinuousLinearMap
  let A := fun L : templateSymmetryGroup (M.supportIn T hunimod eW) =>
    L.val.toContinuousLinearEquiv.toContinuousLinearMap
  let μ := fun r => M.translatedGroupBoxProbability T F hunimod eW
    haarN chartN hchartN bN Eall γ r 1
  let J := fun (p : NormalizedPair G Λ) g => (π (p.val.1 g)).toAdd
  let raw := fun (p : NormalizedPair G Λ × G) r =>
    F.realScaleProfile (funext hchartD ▸ chartD.continuous) (J p.1)
      (hπ.comp p.1.property.1.1).continuous p.2 X (boundedBracketWords d) βD r
  let b := fun p r => ∫ k, raw p r k 0 ∂(μ r : Measure F.N.carrier)
  let label := fun (p : NormalizedPair G Λ) x r => canonicalAffineLabel (μ r : Measure F.N.carrier)
    (fun k => (raw (p, x) r k).restrict Z)
    (fun L => linearBallProfile q (A L) R + ContinuousMap.const Z (b (p, x) r))
  have hδ1 : δ < 1 := lt_of_le_of_lt (hd.trans (min_le_left _ _)) (by norm_num)
  have ht : 0 < 1 - δ / 2 := by linarith only [hδ1]
  obtain ⟨a, _, hbound⟩ := uniform_sublinear_height_of_stable_labels label A J
    (fun g => (π g).toAdd) ht hη (fun p x r hr => hstable (p, x) r hr) hcompare
  refine ⟨a, ?_⟩
  exact uniform_sublinear_of_local_radius_bound
    (fun p x y => J p y - J p x - A (a p) ((π (x⁻¹ * y)).toAdd)) hη hbound

end PolycyclicRecognition.CartanWordModel

end

end OAI

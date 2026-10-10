import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialBoxCompact
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanMetricBasepointSampling
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBasepointConcentration
import OAI.GroupTheory.PolycyclicRecognition.Analysis.CompactProfileEstimates

namespace OAI

/-! # Metric basepoint comparison from established analytic estimates -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Metric Set Filter
open scoped Manifold Pointwise Topology ENNReal

variable {EG G I : Type*} [Fintype I] [DecidableEq I] [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsTopologicalGroup G]
  [IsIsometricSMul G G] [ProperSpace G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
  (hπExp : ∀ x, (π (ExpG x)).toAdd = eW (heightProjection T.character x))
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ x, chartN x = F.ExpN x)
  (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
  (hchartD : ∀ x, chartD x = F.ExpD x)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
  (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
  [IsTopologicalGroup F.D.carrier]

  [IsTopologicalGroup F.N.carrier] [SecondCountableTopology F.N.carrier]
  {P L : Type*} [Finite L] [Nonempty L]

include hunimod hπExp hchartN hchartD dynkinN dynkinD in
/-- The metric and Haar construction supplies all sampling premises for
basepoint comparison; the analytic estimates are a separate proved package. -/
theorem exists_metric_basepoint_comparison
    (hExp : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ₀ : M.Bases)
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {K : ℝ} (hK : 0 ≤ K)
    (hLip : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ K * dist x y)
    (X : I → H) {d : ℕ} (hDnil : lowerCentralSeries ℝ H H d = ⊥)
    (bD₀ : Basis (Fin (finrank ℝ H)) ℝ H)
    (βD : WordBasisSelections X (boundedBracketWords d))
    (hβD : IsMaximizingColumnBasis (wordListCoordinates X (boundedBracketWords d) bD₀)
      (fun w => bracketWordExponent (fun _ : I => 1) w) βD.val)
    {cD : ℕ} (aD : DynkinCoefficients cD 2)
    (hmD : ∀ x y, F.ExpD (finiteDynkinPolynomial aD ![x, y]) = F.ExpD x * F.ExpD y)
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (E : Set W) (hE : IsCompact E) (hne : E.Nonempty) (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    {lo : ℝ} (hlo : 0 < lo)
    (hcost : ∀ w : M.wordList, lo ≤ M.boxCost T hunimod eW E w)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) {R : ℝ} (hR : 0 < R)
    (J : P → G → W) (hJ : ∀ p, Continuous (J p))
    (A : L → W →L[ℝ] W) (hA : Function.Injective A) :
    let Z := Metric.closedBall (0 : Fin (finrank ℝ H) → ℝ) R
    let bD := WordBasisSelections.basis X (boundedBracketWords d) βD
    let height := eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype)
    let q := (height.comp bD.equivFun.symm.toLinearMap).toContinuousLinearMap
    let μ := fun r => M.translatedGroupBoxProbability T F hunimod eW
      haarN chartN hchartN b₀ E β r 1
    let raw := fun (p : P × G) r => F.realScaleProfile (funext hchartD ▸ chartD.continuous)
      (J p.1) (hJ p.1) p.2 X (boundedBracketWords d) βD r
    CompactProfileEstimates raw μ q A R (fun r => M.groupBox T hunimod eW
      (F.ExpN ∘ F.N.equiv) ((fun w => (1 + δ) • w) '' E) β r 1) →
    let b := fun p r => ∫ k, raw p r k 0 ∂(μ r : Measure F.N.carrier)
    let label := fun p r => canonicalAffineLabel (μ r : Measure F.N.carrier)
      (fun k => (raw p r k).restrict Z)
      (fun l => linearBallProfile q (A l) R + ContinuousMap.const Z (b p r))
    ∃ η : ℝ, 0 < η ∧ ∀ (scale : ℕ → ℝ), Tendsto scale atTop atTop → StrictMono scale →
      (∀ n, 1 ≤ scale n) → (∀ n, 1 ≤ (1 - δ / 2) * scale n) →
      ∀ (p : ℕ → P) (x y : ℕ → G), (∀ n, dist (x n) (y n) ≤ η * scale n) →
      (∀ᶠ n in atTop, label (p n, x n) (scale n) = label (p n, y n) ((1 - δ / 2) * scale n)) ∧
      Tendsto (fun n => (scale n)⁻¹ • (J (p n) (y n) - J (p n) (x n) -
        A (label (p n, y n) ((1 - δ / 2) * scale n)) ((π ((x n)⁻¹ * y n)).toAdd)))
        atTop (𝓝 0) := by
  dsimp only
  intro estimates
  let Z := Metric.closedBall (0 : Fin (finrank ℝ H) → ℝ) R
  let bD := WordBasisSelections.basis X (boundedBracketWords d) βD
  let height : H →ₗ[ℝ] W := eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype)
  let q := (height.comp bD.equivFun.symm.toLinearMap).toContinuousLinearMap
  let μ := fun r => M.translatedGroupBoxProbability T F hunimod eW
    haarN chartN hchartN b₀ E β r 1
  let raw := fun (p : P × G) r =>
    F.realScaleProfile (funext hchartD ▸ chartD.continuous) (J p.1) (hJ p.1)
      p.2 X (boundedBracketWords d) βD r
  let b := fun p r => ∫ k, raw p r k 0 ∂(μ r : Measure F.N.carrier)
  let label := fun p r => canonicalAffineLabel (μ r : Measure F.N.carrier)
    (fun k => (raw p r k).restrict Z)
    (fun L => linearBallProfile q (A L) R + ContinuousMap.const Z (b p r))
  obtain ⟨ρ₀, η, D, hρ₀, hη, hD, hgeometry⟩ := M.exists_metric_basepoint_dominated_sampling
    T F hunimod eW π hπExp chartN hchartN chartD hchartD dynkinN dynkinD hExp realize
    b₀ γ₀ hpath hK hLip
    X hDnil bD₀ βD hβD aD hmD haarN haarD E hE hne β hβ hlo hcost hδ hδ1 hR
  let ρ := min ρ₀ R
  have hρ : 0 < ρ := lt_min hρ₀ hR
  have hρR : ρ ≤ R := min_le_right _ _
  have hρ₀' : ρ ≤ ρ₀ := min_le_left _ _
  refine ⟨η, hη, ?_⟩
  have hheight : Function.Surjective height := eW.surjective.comp (cartan_height_surjective T H)
  have hkill (u v : H) : height ⁅u, v⁆ = 0 := by
    change eW (heightProjection T.character (⁅u, v⁆ : H)) = 0
    rw [LieSubalgebra.coe_bracket, heightProjection_lie_eq_zero T.character T.character_lie,
      map_zero]
  have hchartheight v : (π (F.inclusionD (chartD (F.D.equiv v)))).toAdd = height v := by
    rw [hchartD, F.compatibleD, hπExp]
    rfl
  let suffixBox := fun r => M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
    ((fun w => (1 + δ) • w) '' E) β r 1
  have hboxne r : (suffixBox r).Nonempty := by
    refine ⟨1, 0, ?_, ?_⟩
    · simp only [Function.comp_apply, map_zero, F.isExpN.map_zero]
    · simp only [map_zero, norm_zero]; exact zero_le_one
  let C := fun r => M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β r 1
  have hfull r : ∀ᵐ z ∂(μ r : Measure F.N.carrier), z ∈ C r := by
    have hh := M.groupBox_radius_properties T F hunimod eW haarN chartN hchartN b₀
      E β r zero_lt_one
    simpa only [μ, C, translatedGroupBoxProbability, mul_one, image_id'] using
      ae_mem_cellProbabilityMeasure
        (Measure.map ((F.ExpN ∘ F.N.equiv) ∘ b₀.equivFun.symm) volume)
        _ hh.1 hh.2.1 hh.2.2.1
  have hcompact r : IsCompact (C r) :=
    isCompact_exponentialCoordinateBox F.N.equiv.toLinearEquiv F.ExpN chartN hchartN
      (M.boxBasis T hunimod eW E β r) 1 zero_le_one
  have hα : 0 < 1 - δ / 2 := by linarith only [hδ1]
  apply F.nearby_labels_of_concentration (funext hchartD ▸ chartD.continuous)
    chartD hchartD π height hheight hchartheight hkill A hA J hJ
    X (boundedBracketWords d) βD hρ hR hρR hα μ suffixBox hboxne
    (D := ENNReal.ofReal D ^ finrank ℝ (cartanRootIdeal H)) (by simp) C hcompact hfull
  · intro scale hscale hscale1
    filter_upwards [hgeometry scale hscale hscale1] with n hn g hg
    obtain ⟨u, k, ν, hf, hh, hν, hdom, hchart⟩ := hn g hg
    exact ⟨u, k, ν, hf, hh, hν, hdom, fun z hz => hchart z (hz.trans hρ₀')⟩
  · exact estimates.mean
  · exact estimates.zeroMean
  · exact estimates.suffix


end PolycyclicRecognition.CartanWordModel

end

end OAI

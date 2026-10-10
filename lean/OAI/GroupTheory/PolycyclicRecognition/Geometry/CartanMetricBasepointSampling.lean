import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanMetricBasepointGeometry
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBasepointCellDomination
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanMixedScaleBoxes

namespace OAI

/-! # Actual dominated sampling at a nearby basepoint -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule MeasureTheory Metric Set Filter
open scoped Manifold Pointwise Topology ENNReal

variable {EG G I : Type*} [Fintype I] [DecidableEq I] [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
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

include hunimod hπExp hchartN hchartD dynkinN dynkinD in
/-- A nearby center admits a changed sampling law dominated by independent
ordinary-cell and allowed-suffix sampling. The domination constant is exact
and independent of the map, centers and scale. -/
theorem exists_metric_basepoint_dominated_sampling
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
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) {R : ℝ} (hR : 0 < R) :
    ∃ ρ η L : ℝ, 0 < ρ ∧ 0 < η ∧ 1 ≤ L ∧
      ∀ scale : ℕ → ℝ, Tendsto scale atTop atTop → (∀ n, 1 ≤ scale n) →
      ∀ᶠ n in atTop, ∀ g : G, dist 1 g ≤ η * scale n →
      ∃ (u : F.N.carrier) (k : F.D.carrier) (ν : ProbabilityMeasure F.N.carrier),
        F.inclusionN u * F.inclusionD k = g ∧
        (π (F.inclusionD k)).toAdd = (π g).toAdd ∧
        (∀ᵐ a ∂(ν : Measure F.N.carrier), a ∈
          M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv)
            ((fun w => (1 + δ) • w) '' E) β ((1 - δ / 2) * scale n) 1) ∧
        (∀ S : Set F.N.carrier, MeasurableSet S →
          (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN
            b₀ E β (scale n) 1 : Measure F.N.carrier)
              ((fun a => F.action k⁻¹ (u⁻¹ * a)) ⁻¹' S) ≤
          (ENNReal.ofReal L ^ finrank ℝ (cartanRootIdeal H)) *
            (M.translatedGroupBoxProbability T F hunimod eW haarN chartN hchartN
              b₀ E β ((1 - δ / 2) * scale n) 1 : Measure F.N.carrier).prod
                (ν : Measure F.N.carrier) {p | p.1 * p.2 ∈ S}) ∧
        let b := WordBasisSelections.basis X (boundedBracketWords d) βD
        let br := exponentialRescaleBasis b
          (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)) (Real.log (scale n))
        let bs := exponentialRescaleBasis b
          (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j))
            (Real.log ((1 - δ / 2) * scale n))
        ∀ z : Fin (finrank ℝ H) → ℝ, ‖z‖ ≤ ρ →
          ‖wordChartLeftShift F.D.equiv chartD br bs k z‖ ≤ R := by
  let α := 1 - δ / 2
  let t := (1 + δ) * α
  have hα : 1 / 2 ≤ α := by dsimp [α]; linarith only [hδ1]
  have hα1 : α < 1 := by dsimp [α]; linarith only [hδ]
  have ht : 1 < t := by
    have hp := mul_pos hδ (sub_pos.mpr hδ1)
    dsimp [t, α]
    nlinarith only [hp]
  obtain ⟨ρ, η, L, hρ, hη, hL, hgeometry⟩ := M.exists_metric_basepoint_sampling_geometry
    T F hunimod eW π hπExp chartN hchartN chartD hchartD dynkinN dynkinD
    hExp realize b₀ γ₀ hpath hK hLip X hDnil bD₀ βD hβD aD hmD
    E hE hne β hβ hlo hcost hα hα1 ht hR
  refine ⟨ρ, η, L, hρ, hη, hL, ?_⟩
  intro scale hs hs1
  filter_upwards [hgeometry scale hs hs1] with n hn g hg
  obtain ⟨u, k, huk, hkheight, hcover, hsupport, hchart⟩ := hn g hg
  obtain ⟨ν, hν, hdom⟩ := M.exists_basepoint_groupBox_domination T F hunimod eW
    hExp realize haarN haarD dynkinN chartN hchartN b₀ E β (scale n) (α * scale n)
    (zero_lt_one.trans_le hL) u k hcover
  refine ⟨u, k, ν, huk, hkheight, ?_, hdom, hchart⟩
  filter_upwards [hν] with z hz
  have hscale : t * scale n ≤ (1 + δ) * (α * scale n) := by
    dsimp only [t]
    rw [mul_assoc]
  exact M.groupBox_scale_le_enlargement T hunimod eW (F.ExpN ∘ F.N.equiv) hE hne
    (fun w => hlo.le.trans (hcost w)) β hδ.le hscale (hsupport hz)

end PolycyclicRecognition.CartanWordModel

end

end OAI

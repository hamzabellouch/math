import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanMetricLogChartShift
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanBasepointGeometryOfBounds
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PositiveWidthSmallLog
import OAI.GroupTheory.PolycyclicRecognition.Analysis.WordChartLogBound

namespace OAI

/-! # Actual metric factors supply the basepoint sampling geometry -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Metric Set Filter
open scoped Manifold Pointwise Topology

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

include hunimod hπExp hchartN hchartD dynkinN dynkinD in
/-- A single small ambient-distance fraction supplies the inverse-cover
and allowed-suffix inclusions, together with the actual changed chart.
All geometric conclusions are derived from the published inputs. -/
theorem exists_metric_basepoint_sampling_geometry
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
    (E : Set W) (hE : IsCompact E) (hne : E.Nonempty) (β : M.Bases)
    (hβ : IsMaximizingColumnBasis (wordListCoordinates M.letter M.wordList b₀)
      (M.boxCost T hunimod eW E) β.val)
    {lo : ℝ} (hlo : 0 < lo)
    (hcost : ∀ w : M.wordList, lo ≤ M.boxCost T hunimod eW E w)
    {α t : ℝ} (hα : 1 / 2 ≤ α) (hα1 : α < 1) (ht : 1 < t)
    {R : ℝ} (hR : 0 < R) :
    ∃ ρ η L : ℝ, 0 < ρ ∧ 0 < η ∧ 1 ≤ L ∧
      ∀ scale : ℕ → ℝ, Tendsto scale atTop atTop → (∀ n, 1 ≤ scale n) →
      ∀ᶠ n in atTop, ∀ g : G, dist 1 g ≤ η * scale n →
      ∃ (u : F.N.carrier) (k : F.D.carrier),
        F.inclusionN u * F.inclusionD k = g ∧
        (π (F.inclusionD k)).toAdd = (π g).toAdd ∧
        (∀ a₀ ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (α * scale n) 1,
          ∀ a ∈ M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) 1,
          (F.action k a₀)⁻¹ * u⁻¹ * a ∈
            M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) L) ∧
        ((F.action k) ⁻¹' M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (scale n) L ⊆
          M.groupBox T hunimod eW (F.ExpN ∘ F.N.equiv) E β (t * scale n) 1) ∧
        let b := WordBasisSelections.basis X (boundedBracketWords d) βD
        let br := exponentialRescaleBasis b
          (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)) (Real.log (scale n))
        let bs := exponentialRescaleBasis b
          (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)) (Real.log (α * scale n))
        ∀ z : Fin (finrank ℝ H) → ℝ, ‖z‖ ≤ ρ →
          ‖wordChartLeftShift F.D.equiv chartD br bs k z‖ ≤ R := by
  have hbijN : Function.Bijective F.ExpN := funext hchartN ▸ chartN.bijective
  have hbijD : Function.Bijective F.ExpD := funext hchartD ▸ chartD.bijective
  have hφ (h : H) : F.action (F.ExpD (F.D.equiv h)) =
      M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN hbijN dynkinN h := by
    rw [cartan_action_eq_adjoint_of_published_realization T M F hExp realize hbijN hbijD dynkinN,
      cartanLog_exp]
  obtain ⟨L, hL, hprod⟩ := M.exists_basepoint_box_product_cover T hunimod eW
    F.N.equiv F.ExpN F.isExpN dynkinN b₀
  obtain ⟨C, A, q, hC, hA, hmetric⟩ := M.exists_small_metric_log_chart_shift T F hunimod eW π
    hπExp chartN hchartN chartD hchartD dynkinN dynkinD hExp realize b₀ γ₀
    (WordBasisSelections.basis M.letter M.wordList β)
    hpath hK hLip X hDnil bD₀ βD hβD aD hmD
  obtain ⟨ρ, η, hρ, hη, hgeometry⟩ :=
    M.exists_basepoint_geometry_of_factor_bounds
      (T := T) (F := F) (hunimod := hunimod) (eW := eW) (π := π) (hπExp := hπExp)
      (chartN := chartN) (hchartN := hchartN) (chartD := chartD) (dynkinN := dynkinN)
      b₀ hφ hK hLip X d βD E hE hne β hβ hlo hcost hα hα1 ht hR L
      (hprod E β hβ) hL C A q hC hA hmetric
  exact ⟨ρ, η, L, hρ, hη, hL, hgeometry⟩

end PolycyclicRecognition.CartanWordModel

end

end OAI

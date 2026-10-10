import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanMetricChartShift
import OAI.GroupTheory.PolycyclicRecognition.Analysis.WordChartLogBound

namespace OAI

/-! # The same metric lift has a polynomially bounded Cartan logarithm -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Metric Set
open scoped Manifold Pointwise

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
/-- The actual small-distance chart lift also has a polynomially bounded
Cartan logarithm, uniformly in the two comparable scales. -/
theorem exists_small_metric_log_chart_shift
    (hExp : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ₀ : M.Bases) {J : Type*} [Fintype J]
    (bN : Basis J ℝ (cartanRootIdeal H))
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
    (hmD : ∀ x y, F.ExpD (finiteDynkinPolynomial aD ![x, y]) = F.ExpD x * F.ExpD y) :
    ∃ (C A : ℝ) (q : ℕ), 0 ≤ C ∧ 0 ≤ A ∧
      ∀ R : ℝ, 0 < R → ∃ (ρ η S D : ℝ) (p : ℕ),
      0 < ρ ∧ 0 < η ∧ 1 ≤ S ∧ 0 ≤ D ∧
      ∀ r s : ℝ, S ≤ r → 0 < s → r ≤ 2 * s → s ≤ r →
      ∀ g : G, dist 1 g ≤ η * r →
      ∃ (n : F.N.carrier) (k : F.D.carrier) (h : H),
        F.inclusionN n * F.inclusionD k = g ∧
        (π (F.inclusionD k)).toAdd = (π g).toAdd ∧
        (∃ v : cartanRootIdeal H, F.ExpN (F.N.equiv v) = n ∧
          ‖bN.equivFun v‖ ≤ C * (3 + dist 1 g) ^ q * Real.exp (A * (dist 1 g + 1))) ∧
        F.ExpD (F.D.equiv h) = k ∧
        ‖(finBasis ℝ H).equivFun h‖ ≤ D * (1 + r) ^ p ∧
        let b := WordBasisSelections.basis X (boundedBracketWords d) βD
        let br := exponentialRescaleBasis b
          (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)) (Real.log r)
        let bs := exponentialRescaleBasis b
          (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)) (Real.log s)
        ∀ z : Fin (finrank ℝ H) → ℝ, ‖z‖ ≤ ρ →
          ‖wordChartLeftShift F.D.equiv chartD br bs k z‖ ≤ R := by
  obtain ⟨Cₗ, p, hCₗ, hlog⟩ := exists_wordChartLeftShift_log_bound F.D.equiv F.ExpD F.isExpD
    chartD hchartD X d βD (finBasis ℝ H)
  obtain ⟨C, A, q, hC, hA, hmetric⟩ := M.exists_small_metric_chart_shift T F hunimod eW π
    hπExp chartN hchartN chartD hchartD dynkinN dynkinD hExp realize b₀ γ₀ bN
    hpath hK hLip X hDnil bD₀ βD hβD aD hmD
  refine ⟨C, A, q, hC, hA, ?_⟩
  intro R hR
  obtain ⟨ρ, η, S, hρ, hη, hS, hshift⟩ := hmetric R hR
  refine ⟨ρ, η, max 2 S, Cₗ * R, p, hρ, hη, ?_, mul_nonneg hCₗ hR.le, ?_⟩
  · exact le_trans (by norm_num) (le_max_left _ _)
  intro r s hr hs hrs hsr g hg
  have hrS : S ≤ r := (le_max_right _ _).trans hr
  have hs1 : 1 ≤ s := by have := (le_max_left 2 S).trans hr; linarith
  obtain ⟨n, k, hnk, hkheight, hn, hkshift⟩ := hshift r s hrS hs hrs g hg
  let b := WordBasisSelections.basis X (boundedBracketWords d) βD
  let br := exponentialRescaleBasis b
    (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)) (Real.log r)
  obtain ⟨h, he, hh⟩ := hlog s hs1 br k R (hkshift 0 (by simpa using hρ.le))
  refine ⟨n, k, h, hnk, hkheight, hn, he, ?_, hkshift⟩
  exact hh.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith)
    (by linarith : 1 + s ≤ 1 + r) p) (mul_nonneg hCₗ hR.le))

end PolycyclicRecognition.CartanWordModel

end

end OAI

import OAI.GroupTheory.PolycyclicRecognition.Analysis.WordChartLeftShift
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SmallDistanceRatio
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialRepresentationInput
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanSmallMetricFactors
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanPathLifts
import OAI.GroupTheory.PolycyclicRecognition.Analysis.MetricFactorComparison

namespace OAI

/-! # Actual small-distance lifts preserve a common Cartan chart domain -/

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
/-- A sufficiently small fraction of the ambient scale admits a factor
lift whose inverse Cartan translation carries one fixed coordinate ball
into the required larger ball, uniformly in both nearby scales. -/
theorem exists_small_metric_chart_shift
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
      ∀ R : ℝ, 0 < R → ∃ ρ η S : ℝ, 0 < ρ ∧ 0 < η ∧ 1 ≤ S ∧
      ∀ r s : ℝ, S ≤ r → 0 < s → r ≤ 2 * s → ∀ g : G, dist 1 g ≤ η * r →
      ∃ (n : F.N.carrier) (k : F.D.carrier),
        F.inclusionN n * F.inclusionD k = g ∧
        (π (F.inclusionD k)).toAdd = (π g).toAdd ∧
        (∃ v : cartanRootIdeal H, F.ExpN (F.N.equiv v) = n ∧
          ‖bN.equivFun v‖ ≤ C * (3 + dist 1 g) ^ q * Real.exp (A * (dist 1 g + 1))) ∧
        let b := WordBasisSelections.basis X (boundedBracketWords d) βD
        let br := exponentialRescaleBasis b
          (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)) (Real.log r)
        let bs := exponentialRescaleBasis b
          (fun j => bracketWordExponent (fun _ : I => 1) (βD.val j)) (Real.log s)
        ∀ z : Fin (finrank ℝ H) → ℝ, ‖z‖ ≤ ρ →
          ‖wordChartLeftShift F.D.equiv chartD br bs k z‖ ≤ R := by
  have hbijN : Function.Bijective F.ExpN := funext hchartN ▸ chartN.bijective
  have hbijD : Function.Bijective F.ExpD := funext hchartD ▸ chartD.bijective
  have hφ := cartan_action_eq_adjoint_of_published_realization T M F hExp realize
    hbijN hbijD dynkinN
  obtain ⟨C, A, B, D, q, hC, hA, _hB, _hD, hfactor⟩ :=
    M.exists_small_metric_cartan_factor_bound T F hunimod eW π hπExp
      chartN hchartN chartD hchartD dynkinN dynkinD b₀ γ₀ bN hφ hpath hK hLip
      X hDnil bD₀ βD hβD
  have hm x y : F.ExpD (F.D.equiv (finiteDynkinPolynomial aD ![x, y])) =
      F.ExpD (F.D.equiv x) * F.ExpD (F.D.equiv y) := by
    have he := finiteDynkinPolynomial_map F.D.equiv.toLieHom aD ![x, y]
    have hv : (fun i : Fin 2 => F.D.equiv.toLieHom (![x, y] i)) =
        ![F.D.equiv x, F.D.equiv y] := by
      funext i
      fin_cases i <;> rfl
    rw [hv] at he
    exact (congrArg F.ExpD he).trans (hmD (F.D.equiv x) (F.D.equiv y))
  refine ⟨C, A, q, hC, hA, ?_⟩
  intro R hR
  obtain ⟨ρ, ε, hρ, hε, hshift⟩ := exists_wordChartLeftShift_ball
    F.D.equiv F.ExpD F.isExpD chartD hchartD X hDnil bD₀ βD hβD aD hm hR
  obtain ⟨η, S, hη, hS, hratio⟩ := exists_small_distance_ratio B D d hε
  refine ⟨ρ, η, S, hρ, hη, hS, ?_⟩
  intro r s hr hs hrs g hg
  have hr1 : 1 ≤ r := hS.trans hr
  obtain ⟨n, k, hnk, hkheight, hn, z, hz, hzbound⟩ := hfactor r hr1 g
  refine ⟨n, k, hnk, hkheight, hn, ?_⟩
  dsimp only
  rw [← hz]
  exact hshift r s hr1 hs hrs z (hzbound.trans (hratio r hr (dist 1 g) dist_nonneg hg))

end PolycyclicRecognition.CartanWordModel

end

end OAI

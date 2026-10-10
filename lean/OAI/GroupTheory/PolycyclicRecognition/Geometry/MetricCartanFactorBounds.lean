import OAI.GroupTheory.PolycyclicRecognition.Analysis.MetricFactorBounds

namespace OAI

/-! # Polynomial Cartan logarithms for arbitrary ambient points -/

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Metric Set
open scoped Manifold Pointwise

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsIsometricSMul G G] [ProperSpace G]
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

include hunimod hπExp hchartN hchartD dynkinN dynkinD in
/-- Retain only the Cartan part of the actual metric factor theorem.
The height is exact, including when the group factors overlap. -/
theorem exists_metric_cartan_factor_bound
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ₀ : M.Bases)
    (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
      (by rw [← show chartN = F.ExpN from funext hchartN]; exact chartN.bijective) dynkinN
      (cartanLog H F.D.equiv F.ExpD
        (by rw [← show chartD = F.ExpD from funext hchartD]; exact chartD.bijective) d))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {K : ℝ} (hK : 0 ≤ K)
    (hLip : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ K * dist x y) :
    ∃ (C : ℝ) (p : ℕ), 0 ≤ C ∧ ∀ g : G,
      ∃ (u : F.N.carrier) (d : F.D.carrier),
        F.inclusionN u * F.inclusionD d = g ∧
        (π (F.inclusionD d)).toAdd = (π g).toAdd ∧
        ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD
          (by rw [← show chartD = F.ExpD from funext hchartD]; exact chartD.bijective) d)‖ ≤
          C * (3 + dist 1 g) ^ p := by
  obtain ⟨_, C, _, _, p, _, hC, _, hb⟩ := M.exists_metric_factor_thickening_bound
    T F hunimod eW π hπExp chartN hchartN chartD hchartD dynkinN dynkinD
    b₀ γ₀ b₀ (isCompact_singleton (x := (1, 1))) hφ hpath hK hLip
  refine ⟨C, p, hC, ?_⟩
  intro g
  obtain ⟨u, d, he, hh, hbound⟩ := hb g
  refine ⟨u, d, he, hh, ?_⟩
  simpa only [mul_one] using (hbound (1, 1) (mem_singleton _)).2

end PolycyclicRecognition.CartanWordModel

end

end OAI

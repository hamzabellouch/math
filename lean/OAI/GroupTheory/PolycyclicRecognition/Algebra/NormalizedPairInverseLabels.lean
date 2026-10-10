import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanInverseCoefficients
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PairCharts

namespace OAI

/-! # Inverse coefficients for the actual normalized quasi-inverse pairs -/

noncomputable section
namespace PolycyclicRecognition.CartanFactorModel

open Module
open scoped Manifold NNReal

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsIsometricSMul G G] [IsTopologicalGroup G] [ProperSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)

/-- The inverse normalization only left-translates the inverse map, which
cancels in two-point height differences. Thus the proved sublinear labels
of the normalized pairs are genuinely inverse coefficients. -/
theorem normalized_pair_inverse_coefficients
    (eW : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
    (hπExp : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
    (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
    (hchartD : ∀ x, chartD x = F.ExpD x)
    {Λ : ℝ≥0} (A : NormalizedPair G Λ → W →L[ℝ] W)
    {K : ℝ} (hK : 0 ≤ K)
    (hπ : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ K * dist x y)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ D : ℝ, 0 ≤ D ∧ ∀ p x y,
      ‖(π (p.val.1 y)).toAdd - (π (p.val.1 x)).toAdd - A p ((π (x⁻¹ * y)).toAdd)‖ ≤
        ε * dist x y + D) (p : NormalizedPair G Λ) :
    (A (pairChartTransition (1, p)).1).comp (A p) = ContinuousLinearMap.id ℝ W := by
  let q := (pairChartTransition (1, p)).1
  have hheight x y : (π (x⁻¹ * y)).toAdd = (π y).toAdd - (π x).toAdd := by
    simp only [map_mul, map_inv, toAdd_mul, toAdd_inv]
    abel
  have hs (r : NormalizedPair G Λ) (ε : ℝ) (hε : 0 < ε) : ∃ D : ℝ, 0 ≤ D ∧ ∀ x y,
      ‖(π (r.val.1 y)).toAdd - (π (r.val.1 x)).toAdd - A r ((π y).toAdd - (π x).toAdd)‖ ≤
        ε * dist x y + D := by
    obtain ⟨D, hD, hb⟩ := hsub ε hε
    exact ⟨D, hD, fun x y => by simpa only [hheight] using hb r x y⟩
  have hq x y : (π (q.val.1 y)).toAdd - (π (q.val.1 x)).toAdd =
      (π (p.val.2 y)).toAdd - (π (p.val.2 x)).toAdd := by
    dsimp only [q]
    simp only [pairChartTransition_forward, inv_one, one_mul, map_mul, map_inv,
      toAdd_mul, toAdd_inv]
    abel
  apply F.inverse_coefficients_of_sublinear_height T eW π hπExp chartD hchartD
    p.val.1 p.val.2 (A p) (A q) hK Λ.coe_nonneg (show 0 ≤ (0 : ℝ) from le_rfl)
    Λ.coe_nonneg hπ
  · intro x y
    simpa only [add_zero] using p.property.1.1.dist_le_mul x y
  · exact p.property.1.2.2.2.2.1
  · exact hs p
  · intro ε hε
    obtain ⟨D, hD, hb⟩ := hs q ε hε
    exact ⟨D, hD, fun x y => by simpa only [hq] using hb x y⟩

end PolycyclicRecognition.CartanFactorModel

end

end OAI

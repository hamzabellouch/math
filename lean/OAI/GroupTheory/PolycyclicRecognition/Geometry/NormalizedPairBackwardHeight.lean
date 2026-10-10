import OAI.GroupTheory.PolycyclicRecognition.Algebra.NormalizedPairInverseLabels

namespace OAI

/-! # Uniform height estimates for the actual backward maps -/

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

/-- The already proved inverse-coefficient identity determines the inverse
linear equivalence, including the normalization translation. -/
theorem normalized_pair_inverse_equiv
    (eW : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
    (hπExp : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
    (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
    (hchartD : ∀ x, chartD x = F.ExpD x)
    {Λ : ℝ≥0} (A : NormalizedPair G Λ → W ≃L[ℝ] W)
    {K : ℝ} (hK : 0 ≤ K)
    (hπ : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ K * dist x y)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ D : ℝ, 0 ≤ D ∧ ∀ p x y,
      ‖(π (p.val.1 y)).toAdd - (π (p.val.1 x)).toAdd - A p ((π (x⁻¹ * y)).toAdd)‖ ≤
        ε * dist x y + D) (p : NormalizedPair G Λ) :
    A (pairChartTransition (1, p)).1 = (A p).symm := by
  have h := F.normalized_pair_inverse_coefficients T eW π hπExp chartD hchartD
    (fun q => (A q).toContinuousLinearMap) hK hπ hsub p
  apply ContinuousLinearEquiv.ext
  funext w
  have he := congrArg (fun f : W →L[ℝ] W => f ((A p).symm w)) h
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] using he

/-- The backward maps inherit the same uniform two-point error, with the
inverse coefficient. Left normalization cancels exactly in their heights. -/
theorem normalized_pair_backward_sublinear_height
    (eW : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
    (hπExp : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
    (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
    (hchartD : ∀ x, chartD x = F.ExpD x)
    {Λ : ℝ≥0} (A : NormalizedPair G Λ → W ≃L[ℝ] W)
    {K : ℝ} (hK : 0 ≤ K)
    (hπ : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ K * dist x y)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ D : ℝ, 0 ≤ D ∧ ∀ p x y,
      ‖(π (p.val.1 y)).toAdd - (π (p.val.1 x)).toAdd - A p ((π (x⁻¹ * y)).toAdd)‖ ≤
        ε * dist x y + D) :
    ∀ ε : ℝ, 0 < ε → ∃ D : ℝ, 0 ≤ D ∧ ∀ p x y,
      ‖(π (p.val.2 y)).toAdd - (π (p.val.2 x)).toAdd - (A p).symm ((π (x⁻¹ * y)).toAdd)‖ ≤
        ε * dist x y + D := by
  intro ε hε
  obtain ⟨D, hD, hb⟩ := hsub ε hε
  refine ⟨D, hD, ?_⟩
  intro p x y
  let q := (pairChartTransition (1, p)).1
  have hq := F.normalized_pair_inverse_equiv T eW π hπExp chartD hchartD A hK hπ hsub p
  have he : (π (q.val.1 y)).toAdd - (π (q.val.1 x)).toAdd =
      (π (p.val.2 y)).toAdd - (π (p.val.2 x)).toAdd := by
    dsimp only [q]
    simp only [pairChartTransition_forward, inv_one, one_mul, map_mul, map_inv,
      toAdd_mul, toAdd_inv]
    abel
  have hh := hb q x y
  rw [he, show A q = (A p).symm from hq] at hh
  exact hh

end PolycyclicRecognition.CartanFactorModel

end

end OAI

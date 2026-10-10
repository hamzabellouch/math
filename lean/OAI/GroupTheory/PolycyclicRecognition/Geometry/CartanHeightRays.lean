import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanFactorModel
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanWeights
import OAI.GroupTheory.PolycyclicRecognition.Geometry.ExponentialCoarseMetric
import OAI.GroupTheory.PolycyclicRecognition.Analysis.SublinearRayIdentification

namespace OAI

/-! # Actual Cartan representatives of height rays

The height is exactly linear along these rays. Continuity on one compact
ball and the one-parameter group identity give their linear metric growth.
-/

noncomputable section
namespace PolycyclicRecognition

open Module
open scoped Manifold

namespace CartanFactorModel

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [Group G] [ChartedSpace EG G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G}
  (F : CartanFactorModel H ExpG) (eW : HeightSpace T.character ≃ₗ[ℝ] W)

/-- The Cartan one-parameter ray representing the height `t • w`. -/
def heightRay (w : W) (t : ℝ) : F.D.carrier :=
  F.ExpD (F.D.equiv (t • cartanHeightSection T H (eW.symm w)))

omit [FiniteDimensional ℝ W] in
@[simp] theorem heightRay_zero (w : W) : F.heightRay T eW w 0 = 1 := by
  simp only [heightRay, zero_smul, map_zero, F.isExpD.map_zero]

omit [FiniteDimensional ℝ W] in
/-- These are actual ambient height rays, with no coordinate approximation. -/
theorem heightRay_height (height : G →* Multiplicative W)
    (hheight : ∀ x, (height (ExpG x)).toAdd = eW (heightProjection T.character x))
    (w : W) (t : ℝ) :
    (height (F.inclusionD (F.heightRay T eW w t))).toAdd = t • w := by
  rw [heightRay, F.compatibleD, hheight]
  change eW (heightProjection T.character
    (t • (cartanHeightSection T H (eW.symm w) : GroupLieAlgebra (𝓘(ℝ, EG)) G))) = t • w
  rw [map_smul, cartanHeightSection_height, map_smul, eW.apply_symm_apply]

/-- One metric coefficient works for all directions. The cost of direction
`w` is its norm in the chosen finite-dimensional height space. -/
theorem exists_heightRay_metric_bound [IsIsometricSMul G G]
    (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
    (hchartD : ∀ x, chartD x = F.ExpD x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (w : W) (t : ℝ),
      dist 1 (F.inclusionD (F.heightRay T eW w t)) ≤ C * (1 + |t| * ‖w‖) := by
  let s := F.D.equiv.toLinearEquiv.toLinearMap.comp
    ((cartanHeightSection T H).comp eW.symm.toLinearMap)
  let E : W → G := fun w => F.inclusionD (F.ExpD (s w))
  have hE : Continuous E := by
    have he : E = F.inclusionD ∘ chartD ∘ s := by
      funext w
      exact congrArg F.inclusionD (hchartD (s w)).symm
    rw [he]
    exact F.closedD.continuous.comp (chartD.continuous.comp s.continuous_of_finiteDimensional)
  have hE0 : E 0 = 1 := by simp only [E, map_zero, F.isExpD.map_zero, map_one]
  have hadd (w : W) (x y : ℝ) : E ((x + y) • w) = E (x • w) * E (y • w) := by
    simp only [E, map_smul, F.isExpD.map_add_smul, map_mul]
  obtain ⟨C, hC, hbound⟩ := continuous_radial_exponential_metric_bound E hE hE0 hadd
  refine ⟨C, hC, ?_⟩
  intro w t
  have hb := hbound (t • w)
  simpa only [E, s, LinearMap.comp_apply, map_smul, heightRay, LinearEquiv.coe_coe, LieEquiv.coe_toLinearEquiv, norm_smul, Real.norm_eq_abs] using hb


/-- A sublinear height error restricts to the actual Cartan exponential rays.
The resulting threshold may depend on the direction and the map. -/
theorem sublinear_error_on_heightRays [IsIsometricSMul G G]
    (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
    (hchartD : ∀ x, chartD x = F.ExpD x)
    (height : G →* Multiplicative W)
    (hheight : ∀ x, (height (ExpG x)).toAdd = eW (heightProjection T.character x))
    {P : Type*} (η : P → G → W) (A : P → W →ₗ[ℝ] W)
    (hsub : ∀ p ε, 0 < ε → ∃ B : ℝ, ∀ g,
      ‖η p g - η p 1 - A p (height g).toAdd‖ ≤ ε * dist 1 g + B) :
    ∀ p w ε, 0 < ε → ∃ R : ℝ, ∀ t, R ≤ t → 0 ≤ t →
      ‖(η p (F.inclusionD (F.heightRay T eW w t)) - η p 1) - t • A p w‖ ≤ ε * t := by
  obtain ⟨C, hC, hmetric⟩ := F.exists_heightRay_metric_bound T eW chartD hchartD
  intro p w ε hε
  have hm (t : ℝ) (ht : 0 ≤ t) :
      dist 1 (F.inclusionD (F.heightRay T eW w t)) ≤ (C * ‖w‖) * t + C := by
    have h := hmetric w t
    rw [abs_of_nonneg ht] at h
    convert h using 1; ring
  obtain ⟨R, hR⟩ := sublinear_error_on_linear_ray (1 : G)
    (fun g => η p g - η p 1 - A p (height g).toAdd)
    (fun t => F.inclusionD (F.heightRay T eW w t))
    (hsub p) (mul_nonneg hC (norm_nonneg w)) hm ε hε
  refine ⟨R, ?_⟩
  intro t ht ht0
  simpa only [F.heightRay_height T eW height hheight, map_smul] using hR t ht ht0

end CartanFactorModel

end PolycyclicRecognition

end

end OAI

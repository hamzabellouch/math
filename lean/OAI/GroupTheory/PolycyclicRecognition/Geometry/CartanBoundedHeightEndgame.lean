import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanHeightRays
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanFactorHeight

namespace OAI

/-! # Bounded Cartan height from leaf and transversal estimates

Leaf bounds, averaged trace bounds and sublinear height control together give
a uniform bound on the height error.
-/

noncomputable section
namespace PolycyclicRecognition.CartanFactorModel

open Module
open scoped Manifold

variable {EG G W P I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [Group G] [ChartedSpace EG G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [Fintype I]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G}
  (F : CartanFactorModel H ExpG) (eW : HeightSpace T.character ≃ₗ[ℝ] W)

/-- The actual factorization and Cartan rays finish bounded affine height
once the leaf and boundary-trace estimates have been supplied. -/
theorem uniform_affine_bound_of_leaf_and_averaged_traces
    (height : G →* Multiplicative W)
    (hheight : ∀ x, (height (ExpG x)).toAdd = eW (heightProjection T.character x))
    (hbijN : Function.Bijective F.ExpN)
    (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
    (hchartD : ∀ x, chartD x = F.ExpD x)
    (α β : I → Module.Dual ℝ W)
    (hsep : ∀ w, (∀ i, β i w = 0) → w = 0)
    (η : P → G → W) (A : P → W →ₗ[ℝ] W)
    (hsub : ∀ p ε, 0 < ε → ∃ B : ℝ, ∀ g,
      ‖η p g - η p 1 - A p (height g).toAdd‖ ≤ ε * dist 1 g + B)
    {L B : ℝ} (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hleaf : ∀ p x n, ‖η p (x * F.inclusionN n) - η p x‖ ≤ L)
    (htrace : ∀ p d i, |β i (η p (F.inclusionD d) - η p 1) -
      α i (height (F.inclusionD d)).toAdd| ≤ B) :
    (∀ p i, α i = (β i).comp (A p)) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ p g,
        ‖η p g - (η p 1 + A p (height g).toAdd)‖ ≤ C := by
  have hsubray := F.sublinear_error_on_heightRays T eW chartD hchartD height hheight η A hsub
  obtain ⟨hcoeff, C, hC, htrans⟩ := uniform_transversal_affine_bound_of_ray_traces
    α β hsep (fun g => (height g).toAdd) η A F.inclusionD 1
    (F.heightRay T eW) (F.heightRay_height T eW height hheight) hB
    (by simpa only [map_one] using htrace)
    (by simpa only [map_one] using hsubray)
  refine ⟨hcoeff, L + C, add_nonneg hL hC, ?_⟩
  intro p g
  obtain ⟨⟨n, d⟩, rfl⟩ := F.surjective g
  have hswap : F.inclusionD d * F.inclusionN (F.action d⁻¹ n) =
      F.inclusionN n * F.inclusionD d := by
    rw [F.conjugation, map_inv, inv_inv]
    group
  have hl := hleaf p (F.inclusionD d) (F.action d⁻¹ n)
  rw [hswap] at hl
  have ht := htrans p d
  simp only [map_one] at ht
  rw [map_mul, F.inclusionN_height_eq_one T eW height hheight hbijN, one_mul]
  calc
    _ = ‖(η p (F.inclusionN n * F.inclusionD d) - η p (F.inclusionD d)) +
        (η p (F.inclusionD d) - (η p 1 + A p (height (F.inclusionD d)).toAdd))‖ := by
          congr 1
          abel
    _ ≤ _ := norm_add_le _ _
    _ ≤ L + C := add_le_add hl ht

end PolycyclicRecognition.CartanFactorModel

end

end OAI

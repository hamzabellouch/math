import OAI.GroupTheory.PolycyclicRecognition.Geometry.SublinearHeightComposition
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanHeightRays

namespace OAI

/-! # Coarse inverses have inverse linear height coefficients -/

noncomputable section
namespace PolycyclicRecognition.CartanFactorModel

open Module
open scoped Manifold

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)

/-- Comparing the composition to the identity on the actual Cartan height
rays identifies the coefficients. No inverse relation is assumed. -/
theorem inverse_coefficients_of_sublinear_height
    (eW : HeightSpace T.character ≃ₗ[ℝ] W) (π : G →* Multiplicative W)
    (hπExp : ∀ x, (π (Exp x)).toAdd = eW (heightProjection T.character x))
    (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
    (hchartD : ∀ x, chartD x = F.ExpD x)
    (f g : G → G) (A B : W →L[ℝ] W)
    {K L C D : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hπ : ∀ x y, ‖(π x).toAdd - (π y).toAdd‖ ≤ K * dist x y)
    (hfLip : ∀ x y, dist (f x) (f y) ≤ L * dist x y + C)
    (hinv : ∀ x, dist (g (f x)) x ≤ D)
    (hf : ∀ ε : ℝ, 0 < ε → ∃ E : ℝ, 0 ≤ E ∧ ∀ x y,
      ‖(π (f y)).toAdd - (π (f x)).toAdd - A ((π y).toAdd - (π x).toAdd)‖ ≤
        ε * dist x y + E)
    (hg : ∀ ε : ℝ, 0 < ε → ∃ E : ℝ, 0 ≤ E ∧ ∀ x y,
      ‖(π (g y)).toAdd - (π (g x)).toAdd - B ((π y).toAdd - (π x).toAdd)‖ ≤
        ε * dist x y + E) :
    B.comp A = ContinuousLinearMap.id ℝ W := by
  have hcomp := two_point_sublinear_height_comp (fun x => (π x).toAdd)
    f g A B hL hC hfLip hf hg
  have hid := sublinear_linear_height_error_of_close_to_id (fun x => (π x).toAdd)
    (fun x => g (f x)) (B.comp A) hK hD hπ hinv hcomp
  obtain ⟨M, hM, hm⟩ := F.exists_heightRay_metric_bound T eW chartD hchartD
  apply linear_height_coefficient_eq_id (1 : G) (fun x => (π x).toAdd) (B.comp A)
    (fun w t => F.inclusionD (F.heightRay T eW w t))
  · intro w t
    rw [F.heightRay_height T eW π hπExp, map_one]
    simp
  · intro w
    refine ⟨M * ‖w‖, M, mul_nonneg hM (norm_nonneg _), ?_⟩
    intro t ht
    have hh := hm w t
    rw [abs_of_nonneg ht] at hh
    nlinarith
  · intro ε hε
    obtain ⟨E, _, he⟩ := hid ε hε
    exact ⟨E, fun x => he 1 x⟩

end PolycyclicRecognition.CartanFactorModel

end

end OAI

import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.ClockedBounds

namespace OAI

/-! A computable modulus on each finite time slab for the detector's
clocked expressions. Spatial coordinates remain unrestricted. -/

namespace ForcedComputation.ClockedExpr
open ShearFlows Set
open scoped ContDiff BigOperators

def derivativeBound (e : ClockedExpr) (M : ℚ) : ℚ :=
  ∑ j : Fin 4, (e.diff j).bound M

theorem derivativeBound_nonneg (e : ClockedExpr) (M : ℚ) : 0 ≤ e.derivativeBound M :=
  Finset.sum_nonneg (fun j _ => (e.diff j).bound_nonneg M)

theorem fderiv_bound {e : ClockedExpr} (he : e.Valid) (M : ℚ) (y : SpaceTime)
    (hy : |y.1| ≤ |(M : ℝ)|) : ‖fderiv ℝ e.val y‖ ≤ (e.derivativeBound M : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Rat.cast_nonneg.mpr (e.derivativeBound_nonneg M))
  intro v
  conv_lhs => rw [← spaceTimeDirections_sum v]
  rw [map_sum]
  calc
    _ ≤ ∑ j : Fin 4, ‖fderiv ℝ e.val y (timeSpaceCoord j v • spaceTimeDirection j)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j : Fin 4, ‖v‖ * ((e.diff j).bound M : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      rw [map_smul, norm_smul]
      have hj : ‖fderiv ℝ e.val y (spaceTimeDirection j)‖ ≤ ((e.diff j).bound M : ℝ) := by
        rw [← e.val_diff he j y, Real.norm_eq_abs]
        exact val_bound (valid_diff he j) M y hy
      exact mul_le_mul (timeSpaceCoord_norm j v) hj (norm_nonneg _) (norm_nonneg _)
    _ = _ := by
      rw [derivativeBound, Rat.cast_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem lipschitz_bound {e : ClockedExpr} (he : e.Valid) (M : ℚ) (x y : SpaceTime)
    (hx : |x.1| ≤ |(M : ℝ)|) (hy : |y.1| ≤ |(M : ℝ)|) :
    |e.val x - e.val y| ≤ (e.derivativeBound M : ℝ) * ‖x - y‖ := by
  let S : Set SpaceTime := Icc (-|(M : ℝ)|) |(M : ℝ)| ×ˢ (univ : Set Space)
  have hc : Convex ℝ S := (convex_Icc (-|(M : ℝ)|) |(M : ℝ)|).prod convex_univ
  have hxS : x ∈ S := ⟨abs_le.mp hx, mem_univ _⟩
  have hyS : y ∈ S := ⟨abs_le.mp hy, mem_univ _⟩
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z (_ : z ∈ S) => (e.smooth he).differentiable (by simp) z)
    (fun z hz => fderiv_bound he M z (abs_le.mpr hz.1)) hc hyS hxS
  simpa only [Real.norm_eq_abs] using h

end ForcedComputation.ClockedExpr

end OAI

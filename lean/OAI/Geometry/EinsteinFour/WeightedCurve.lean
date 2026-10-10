import OAI.Geometry.EinsteinFour.ModeAverageLimit
import Mathlib.Analysis.Calculus.MeanValue

namespace OAI

/-! The regularity premise in the radial Riemann sums follows from ordinary
bounded curvature and bounded curvature derivative along the frame flow. -/

namespace PositiveEinsteinFour.Averages

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem sineWeight_abs_le_two (t : ℝ) : |sineWeight t| ≤ 2 := by
  rw [abs_of_nonneg (sineWeight_nonneg t)]
  unfold sineWeight
  linarith [Real.neg_one_le_cos (2 * Real.pi * t)]

/-- A bounded differentiable curve with bounded derivative supplies the
global Lipschitz estimate used by the sine-mode discretization. -/
theorem sineWeighted_rescale_lipschitz {f f' : ℝ → E} {B D : ℝ}
    (hderiv : ∀ s, HasDerivAt f (f' s) s)
    (hbound : ∀ s, ‖f s‖ ≤ B) (hbound' : ∀ s, ‖f' s‖ ≤ D)
    (t a b : ℝ) :
    ‖sineWeight a • f (t * a) - sineWeight b • f (t * b)‖ ≤
      (2 * Real.pi * B + 2 * D * |t|) * |a - b| := by
  have hf (x y : ℝ) : ‖f x - f y‖ ≤ D * |x - y| := by
    simpa only [Real.norm_eq_abs] using
      Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (s := Set.univ) (fun z _ => (hderiv z).hasDerivWithinAt)
        (fun z _ => hbound' z) convex_univ (Set.mem_univ y) (Set.mem_univ x)
  have hid : sineWeight a • f (t * a) - sineWeight b • f (t * b) =
      (sineWeight a - sineWeight b) • f (t * a) +
        sineWeight b • (f (t * a) - f (t * b)) := by module
  rw [hid]
  calc
    _ ≤ ‖(sineWeight a - sineWeight b) • f (t * a)‖ +
        ‖sineWeight b • (f (t * a) - f (t * b))‖ := norm_add_le _ _
    _ = |sineWeight a - sineWeight b| * ‖f (t * a)‖ +
        |sineWeight b| * ‖f (t * a) - f (t * b)‖ := by
      simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ (2 * Real.pi * |a - b|) * B + 2 * (D * |t * a - t * b|) := by
      apply add_le_add
      · exact mul_le_mul (Jacobi.sineWeight_lipschitz a b) (hbound _)
          (norm_nonneg _) (by positivity)
      · exact mul_le_mul (sineWeight_abs_le_two b) (hf _ _)
          (norm_nonneg _) (by norm_num)
    _ = _ := by rw [← mul_sub, abs_mul]; ring

end

end PositiveEinsteinFour.Averages

end OAI

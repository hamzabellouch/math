import OAI.GroupTheory.PolycyclicRecognition.Analysis.LipschitzInversePairBounds

namespace OAI

/-! # Quantitative inverse bounds for bounded Lipschitz replacements -/

namespace PolycyclicRecognition

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]

/-- Perturbing a coarse inverse pair preserves its inverse error with a
constant determined only by the original controls and perturbation radii. -/
theorem inverse_error_of_bounded_perturbations
    (f f' : X → Y) (g g' : Y → X)
    {Kg Cg Df Dg E : ℝ} (hKg : 0 ≤ Kg)
    (hg : ∀ y z, dist (g y) (g z) ≤ Kg * dist y z + Cg)
    (hfclose : ∀ x, dist (f' x) (f x) ≤ Df)
    (hgclose : ∀ y, dist (g' y) (g y) ≤ Dg)
    (hinv : ∀ x, dist (g (f x)) x ≤ E) (x : X) :
    dist (g' (f' x)) x ≤ Dg + (Kg * Df + Cg) + E := by
  calc
    dist (g' (f' x)) x ≤ dist (g' (f' x)) (g (f' x)) +
        dist (g (f' x)) (g (f x)) + dist (g (f x)) x := dist_triangle4 _ _ _ _
    _ ≤ Dg + (Kg * Df + Cg) + E := by
      exact add_le_add (add_le_add (hgclose _) ((hg _ _).trans
        (add_le_add (mul_le_mul_of_nonneg_left (hfclose x) hKg) le_rfl))) (hinv x)

end PolycyclicRecognition

end OAI

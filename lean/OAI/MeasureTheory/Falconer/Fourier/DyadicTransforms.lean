import OAI.MeasureTheory.Falconer.Estimates.DyadicTree
import OAI.MeasureTheory.Falconer.Fourier.EndpointTransform

namespace OAI

/-!
# Exact splitting into occupied dyadic cells

This is the spatial splitting in `graph:splitting`, for the original law
and the same measurable endpoint symbol on every descendant.
-/

namespace Falconer
open MeasureTheory

theorem DyadicCube.endpointTransform_split {d : ℕ} (Q : DyadicCube d)
    (μ : Measure (Space d)) [IsFiniteMeasure μ] (n : ℕ)
    (Ma Mp : ℝ) (hMp : Mp ≠ 0) (b : Space d → Sphere d → ℂ)
    (hb : Measurable (Function.uncurry b)) {C : ℝ}
    (hC : ∀ x w, ‖b x w‖ ≤ C) (r : ℝ) (w : Sphere d) :
    endpointTransform (μ.restrict Q.carrier) Ma b r w =
      (Mp / Ma) • ∑ p ∈ Q.occupiedPaths μ n,
        endpointTransform (μ.restrict (Q.descendant p).carrier) Mp b r w := by
  conv_lhs => rw [Q.restrict_occupiedPaths μ n]
  exact endpointTransform_sum (Q.occupiedPaths μ n)
    (fun p => μ.restrict (Q.descendant p).carrier) Ma Mp hMp b hb hC r w

end Falconer

end OAI

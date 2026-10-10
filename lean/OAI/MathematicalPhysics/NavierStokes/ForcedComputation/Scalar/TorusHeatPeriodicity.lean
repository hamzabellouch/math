import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Scalar.TorusHeatGaussianBound

namespace OAI

/-! The prescribed Gaussian convolution has the exact initial value and
preserves the unit spatial periods. -/

noncomputable section
namespace ForcedComputation.VelocityDetector
open ShearFlows Set MeasureTheory

theorem torusHeatKernel_periodic {t : ℝ} (ht : 0 < t) :
    PlanePeriodic (torusHeatKernel t) := by
  intro x n
  rw [torusHeatKernel_factor ht, torusHeatKernel_factor ht]
  simp only [Pi.add_apply, gaussianLattice_add_int]

theorem torusHeatEvolution_initial (g : Plane → ℝ) : torusHeatEvolution g 0 = g := by
  funext x
  simp only [torusHeatEvolution, le_refl, ↓reduceIte]

theorem torusHeatEvolution_periodic {g : Plane → ℝ} (hg : PlanePeriodic g) (t : ℝ) :
    PlanePeriodic (torusHeatEvolution g t) := by
  intro x n
  by_cases ht : t ≤ 0
  · simpa only [torusHeatEvolution, ite_eq_left ht] using hg x n
  · simp only [torusHeatEvolution, ite_eq_right ht]
    apply integral_congr_ae
    filter_upwards [] with y
    have he : (x + fun j => (n j : ℝ)) - y = (x - y) + fun j => (n j : ℝ) := by
      ext j
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    rw [he, torusHeatKernel_periodic (lt_of_not_ge ht) (x - y) n]

end ForcedComputation.VelocityDetector

end

end OAI

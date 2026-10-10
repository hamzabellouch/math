import OAI.MathematicalPhysics.DefocusingNLS.Linear.PeriodicSchwartzPairing

namespace OAI

/-! # Passing bounded physical convergence through a Schwartz test -/

open MeasureTheory Filter Topology
open scoped SchwartzMap

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem tendsto_schwartzPairing_of_bounded_pointwise (ψ : 𝓢(E, ℂ))
    (f : ℕ → C(E, ℂ)) (v : C(E, ℂ)) (B : ℝ)
    (hb : ∀ n y, ‖f n y‖ ≤ B) (hv : ∀ y, Tendsto (fun n => f n y) atTop (𝓝 (v y))) :
    Tendsto (fun n => ∫ y : E, ψ y * f n y) atTop (𝓝 (∫ y : E, ψ y * v y)) := by
  apply tendsto_integral_of_dominated_convergence (fun y => ‖ψ y‖ * B)
  · intro n
    exact (ψ.continuous.mul (f n).continuous).aestronglyMeasurable
  · exact ψ.integrable.norm.mul_const B
  · intro n
    exact ae_of_all _ (fun y => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hb n y) (norm_nonneg _))
  · exact ae_of_all _ (fun y => tendsto_const_nhds.mul (hv y))

end DefocusingNLS

end OAI

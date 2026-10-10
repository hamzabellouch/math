import OAI.Geometry.RCD.Metric.VolumeDensityLimit
import OAI.Geometry.RCD.Metric.VolumeRegime

namespace OAI

/-! # Absolute ball-volume profiles at every shrinking scale -/

open Set Metric Filter MeasureTheory
open scoped Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.rescaling_volume_density {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (p : X) :
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ euclideanUnitVolume n ∧
      ∀ s : ℕ → ℝ, (∀ k, 0 < s k) → Tendsto s atTop (𝓝 0) →
        ∀ R : ℝ, 0 < R → Tendsto
          (fun k => (hausdorff n X).real (ball p (s k*R))/(s k)^n)
          atTop (𝓝 (θ*R^n)) := by
  obtain ⟨θ,hθ,hθupper,hθlim⟩ := hX.volume_density_limit hn p
  refine ⟨θ,hθ,hθupper,?_⟩
  intro s hs hs0 R hR
  have ht := hθlim (fun k => s k*R) (fun k => mul_pos (hs k) hR)
    (by simpa only [zero_mul] using hs0.mul_const R)
  have hm := ht.mul_const (R^n)
  convert hm using 1
  funext k
  rw [mul_pow]
  field_simp

omit [ProperSpace X] in
/-- Euclidean density convergence gives absolute volume convergence at
every rescaled radius. -/
theorem rescaling_volume_convergence_of_density {n : ℕ} {p : X}
    (hdensity : ∀ s : ℕ → ℝ, (∀ k, 0 < s k) → Tendsto s atTop (𝓝 0) →
      Tendsto (fun k => (hausdorff n X).real (ball p (s k))/(s k)^n)
        atTop (𝓝 (euclideanUnitVolume n))) :
    EuclideanRescalingVolumeConvergence (hausdorff n X) n p (euclideanUnitVolume n) := by
  intro s hs hs0 _ R hR
  have ht := hdensity (fun k => s k*R) (fun k => mul_pos (hs k) hR)
    (by simpa only [zero_mul] using hs0.mul_const R)
  have hm := ht.mul_const (R^n)
  convert hm using 1
  funext k
  rw [mul_pow]
  field_simp

end RegularPointCoordinates

end

end OAI

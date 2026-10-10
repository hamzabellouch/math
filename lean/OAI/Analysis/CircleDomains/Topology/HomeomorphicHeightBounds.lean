import OAI.Analysis.CircleDomains.Topology.HomeomorphicCoordinateRange
import OAI.Analysis.CircleDomains.Selection.ScaledExteriorBounds

namespace OAI

/-! A common exterior bound gives common bounds for homeomorphic height
coordinates on each compact disk, by the proved boundary range principle. -/
open Set Function Filter Metric Asymptotics Bornology
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem homeomorphic_height_bound {φ : ℂ ≃ₜ ℂ} {R S : ℝ}
    (hR : 0 < R) (hS : 2*R ≤ S)
    (hb : ∀ z : ℂ, 2*R ≤ ‖z‖ → ‖φ z-z‖ ≤ R) :
    ∀ z ∈ closedBall (0 : ℂ) S, |(φ z).im| ≤ S+R := by
  have hSp : 0 < S := lt_of_lt_of_le (mul_pos (by norm_num) hR) hS
  have hfront (z : ℂ) (hz : z ∈ frontier (closedBall (0 : ℂ) S)) : |(φ z).im| ≤ S+R := by
    have hn : ‖z‖ = S := by
      simpa only [frontier_closedBall (0 : ℂ) hSp.ne', mem_sphere, dist_zero_right] using hz
    have hnorm : ‖φ z‖ ≤ R+S := by
      calc
        ‖φ z‖ = ‖(φ z-z)+z‖ := by rw [sub_add_cancel]
        _ ≤ ‖φ z-z‖ + ‖z‖ := norm_add_le _ _
        _ ≤ R+S := add_le_add (hb z (by rw [hn]; exact hS)) hn.le
    exact (Complex.abs_im_le_norm (φ z)).trans (by linarith)
  have hu := homeomorphic_im_le_of_boundary φ (isCompact_closedBall (0 : ℂ) S)
    (fun z hz => (abs_le.mp (hfront z hz)).2)
  have hl := homeomorphic_im_ge_of_boundary φ (isCompact_closedBall (0 : ℂ) S)
    (fun z hz => (abs_le.mp (hfront z hz)).1)
  exact fun z hz => abs_le.mpr ⟨hl z hz, hu z hz⟩

 theorem normalized_homeomorphic_height_bound
    (harea : ExteriorCoefficientAreaTheorem) {φ : ℂ ≃ₜ ℂ} {R S : ℝ}
    (hR : 0 < R) (hS : 2*R ≤ S)
    (hh : DifferentiableOn ℂ φ {z | R < ‖z‖})
    (hnorm : (fun z => φ z-z) =O[cobounded ℂ] (fun z => z⁻¹)) :
    ∀ z ∈ closedBall (0 : ℂ) S, |(φ z).im| ≤ S+R :=
  homeomorphic_height_bound hR hS
    (harea.scaled_exterior_bound hR hh φ.injective.injOn hnorm)

end CircleDomainRigidity

end

end OAI

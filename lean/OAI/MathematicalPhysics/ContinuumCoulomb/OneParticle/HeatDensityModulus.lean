import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.HeatKernelModulus
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.PlanarForcingModulus

namespace OAI

/-! Explicit moduli of the actual forcing-weighted heat density. These
are the constants used for the fixed-dimensional quadrature mesh. -/

noncomputable section
namespace ContinuumCoulomb.HeatKernelModulus

def density (r : PlanarPosition) (t : ℝ) (p : PlanarPosition) : ℝ :=
  kernel t (‖r - p‖ ^ 2) * planarForcing p

theorem squared_norm_difference {u v : PlanarPosition} {D : ℝ}
    (hu : ‖u‖ ≤ D) (hv : ‖v‖ ≤ D) :
    |‖u‖ ^ 2 - ‖v‖ ^ 2| ≤ 2 * D * ‖u - v‖ := by
  have hD : 0 ≤ D := (norm_nonneg _).trans hu
  have hid : ‖u‖ ^ 2 - ‖v‖ ^ 2 = (‖u‖ - ‖v‖) * (‖u‖ + ‖v‖) := by ring
  rw [hid, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  calc
    _ ≤ ‖u - v‖ * (‖u‖ + ‖v‖) :=
      mul_le_mul_of_nonneg_right (abs_norm_sub_norm_le u v) (by positivity)
    _ ≤ ‖u - v‖ * (2 * D) := mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
    _ = _ := by ring

theorem density_space_lipschitz {r p q : PlanarPosition} {η t D : ℝ}
    (hη : 0 < η) (ht : η ≤ t) (hp : ‖r - p‖ ≤ D) (hq : ‖r - q‖ ≤ D) :
    |density r t p - density r t q| ≤
      (2 * D / η ^ 2 + 32 * η⁻¹) * ‖p - q‖ := by
  have ht0 : 0 < t := hη.trans_le ht
  have hs : |‖r - p‖ ^ 2 - ‖r - q‖ ^ 2| ≤ 2 * D * ‖p - q‖ := by
    have h := squared_norm_difference hp hq
    simpa only [show (r - p) - (r - q) = -(p - q) by abel, norm_neg] using h
  have hk := kernel_space_lipschitz hη ht (sq_nonneg ‖r - p‖) (sq_nonneg ‖r - q‖)
  have hk' : |kernel t (‖r - p‖ ^ 2) - kernel t (‖r - q‖ ^ 2)| ≤
      (2 * D / η ^ 2) * ‖p - q‖ := by
    calc
      _ ≤ |‖r - p‖ ^ 2 - ‖r - q‖ ^ 2| / η ^ 2 := hk
      _ ≤ (2 * D * ‖p - q‖) / η ^ 2 := div_le_div_of_nonneg_right hs (sq_nonneg η)
      _ = _ := by ring
  have hkq := kernel_le_inverse hη ht (sq_nonneg ‖r - q‖)
  have hkq0 := kernel_nonnegative (A := ‖r - q‖ ^ 2) ht0
  have hf := planarForcing_norm_sub_explicit p q
  have hfp0 := planarForcing_nonnegative p
  have hfp1 := planarForcing_le_one p
  have hid : density r t p - density r t q =
      (kernel t (‖r - p‖ ^ 2) - kernel t (‖r - q‖ ^ 2)) * planarForcing p +
        kernel t (‖r - q‖ ^ 2) * (planarForcing p - planarForcing q) := by
    unfold density
    ring
  rw [hid]
  calc
    _ ≤ |(kernel t (‖r - p‖ ^ 2) - kernel t (‖r - q‖ ^ 2)) * planarForcing p| +
        |kernel t (‖r - q‖ ^ 2) * (planarForcing p - planarForcing q)| := abs_add_le _ _
    _ = |kernel t (‖r - p‖ ^ 2) - kernel t (‖r - q‖ ^ 2)| * planarForcing p +
        kernel t (‖r - q‖ ^ 2) * |planarForcing p - planarForcing q| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hfp0, abs_of_nonneg hkq0]
    _ ≤ (2 * D / η ^ 2) * ‖p - q‖ + η⁻¹ * (32 * ‖p - q‖) := by
      apply add_le_add
      · exact (mul_le_of_le_one_right (abs_nonneg _) hfp1).trans hk'
      · exact mul_le_mul hkq hf (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem density_time_lipschitz {r p : PlanarPosition} {η t s D : ℝ}
    (hη : 0 < η) (ht : η ≤ t) (hs : η ≤ s) (hp : ‖r - p‖ ≤ D) :
    |density r t p - density r s p| ≤
      (η⁻¹ ^ 2 + η⁻¹ * (1 + D ^ 2 / (4 * η ^ 2))) * |t - s| := by
  have hD : 0 ≤ D := (norm_nonneg _).trans hp
  have hsq : ‖r - p‖ ^ 2 ≤ D ^ 2 := (sq_le_sq₀ (norm_nonneg _) hD).mpr hp
  have h := kernel_time_lipschitz hη ht hs (sq_nonneg ‖r - p‖)
  rw [density, density, ← sub_mul, abs_mul, abs_of_nonneg (planarForcing_nonnegative p)]
  apply (mul_le_of_le_one_right (abs_nonneg _) (planarForcing_le_one p)).trans
  apply h.trans
  gcongr

end ContinuumCoulomb.HeatKernelModulus

end

end OAI

import OAI.Analysis.KadisonSimilarity.Tensor.TensorSlices
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Tactic

namespace OAI

/-!
# The fixed-prefix limit in propagation from a small corner

On the centered-word subspace the prefix acts isometrically. On the remaining
subspace its norm may be large, but is fixed while the tensor slice tends to
zero. The estimates below carry out that limit without a rate assumption.
-/

noncomputable section
namespace KadisonSimilarity

open Filter
open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Split a prefix into its isometric centered-word action and the exceptional
projection. The latter incurs only the fixed operator norm. -/
theorem norm_prefix_le (P : Submodule ℂ H) [P.HasOrthogonalProjection]
    (A : H →L[ℂ] H)
    (hisometry : ∀ z ∈ Pᗮ, ‖A z‖ = ‖z‖) (z : H) :
    ‖A z‖ ≤ ‖z‖ + ‖A‖ * ‖P.starProjection z‖ := by
  have hsplit : A z = A (z - P.starProjection z) + A (P.starProjection z) := by
    rw [← map_add, sub_add_cancel]
  have hcenter : ‖A (z - P.starProjection z)‖ ≤ ‖z‖ := by
    rw [hisometry _ (P.sub_starProjection_mem_orthogonal z),
      ← P.starProjection_orthogonal_val]
    exact Pᗮ.norm_starProjection_apply_le z
  calc
    _ ≤ ‖A (z - P.starProjection z)‖ + ‖A (P.starProjection z)‖ := by
      rw [hsplit]; exact norm_add_le _ _
    _ ≤ ‖z‖ + ‖A‖ * ‖P.starProjection z‖ :=
      add_le_add hcenter (A.le_opNorm _)

/-- A uniform prefix bound need not be small. It vanishes from the resulting
estimate because it multiplies a sequence converging to zero. -/
theorem propagation_bound_of_vanishing_projection
    (P : Submodule ℂ H) [P.HasOrthogonalProjection]
    (A : ℕ → H →L[ℂ] H) (z : ℕ → H)
    (hisometry : ∀ n, ∀ v ∈ Pᗮ, ‖A n v‖ = ‖v‖)
    (L : ℝ) (hL : ∀ n, ‖A n‖ ≤ L)
    (error target : ℝ) (hz : ∀ n, ‖z n‖ ≤ error)
    (hvanish : Tendsto (fun n => P.starProjection (z n)) atTop (𝓝 0))
    (htest : ∀ n, target ≤ error + ‖A n (z n)‖) :
    target ≤ 2 * error := by
  have hupper (n : ℕ) : target ≤ 2 * error + L * ‖P.starProjection (z n)‖ := by
    have hprefix := norm_prefix_le P (A n) (hisometry n) (z n)
    have hnorm := mul_le_mul_of_nonneg_right (hL n) (norm_nonneg (P.starProjection (z n)))
    linarith [htest n, hz n]
  have ht : Tendsto (fun n => 2 * error + L * ‖P.starProjection (z n)‖)
      atTop (𝓝 (2 * error)) := by
    simpa using (hvanish.norm.const_mul L).const_add (2 * error)
  exact ge_of_tendsto ht (Eventually.of_forall hupper)

/-- The scaling identity in the small corner removes its trace from the
propagation error. -/
theorem corner_scaled_error_le {a c ε v y : ℝ} (ha : 0 < a)
    (hy : y ≤ c * ε * Real.sqrt a * v) :
    (Real.sqrt a)⁻¹ * y ≤ c * ε * v := by
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.2 ha
  calc
    _ ≤ (Real.sqrt a)⁻¹ * (c * ε * Real.sqrt a * v) :=
      mul_le_mul_of_nonneg_left hy (inv_nonneg.mpr hs.le)
    _ = c * ε * v := by field_simp

end KadisonSimilarity

end

end OAI

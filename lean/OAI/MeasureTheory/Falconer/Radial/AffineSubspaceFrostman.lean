import OAI.MeasureTheory.Falconer.Radial.AffinePlaneFrostman
import OAI.MeasureTheory.Falconer.Slicing.SliceCoordinates

namespace OAI

/-! # Uniform bounds for neighborhoods of lower-dimensional affine subspaces -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {d k : ℕ}

def affineSubspaceNeighborhood (V : Submodule ℝ (Space d)) (a : Space d) (r : ℝ) :
    Set (Space d) := {x | ‖Vᗮ.starProjection (x-a)‖ ≤ r}

theorem measurableSet_affineSubspaceNeighborhood (V : Submodule ℝ (Space d))
    (a : Space d) (r : ℝ) : MeasurableSet (affineSubspaceNeighborhood V a r) := by
  exact measurableSet_le (by fun_prop) measurable_const

theorem affine_subspace_frostman_bound (μ : Measure (Space d))
    (V : Submodule ℝ (Space d)) (a : Space d) {M s C r : ℝ}
    (hM : 0 ≤ M) (ha : ‖a‖ ≤ M) (hC : 0 ≤ C)
    (hbounded : ∀ᵐ x ∂μ, ‖x‖ ≤ M) (hfrost : FrostmanBallBound μ s C)
    (hdim : Module.finrank ℝ V ≤ k) (hr : 0 < r) (hr1 : r ≤ 1) :
    μ (affineSubspaceNeighborhood V a r) ≤
      ENNReal.ofReal ((C*(3:ℝ)^s*(4*M+3)^k)*r^(s-(k:ℝ))) := by
  let F : Space (Module.finrank ℝ V) →ₗᵢ[ℝ] Space d :=
    V.subtypeₗᵢ.comp (sliceCoordinates V rfl).symm.toLinearIsometry
  have hnear : affineSubspaceNeighborhood V a r ⊆
      {x | ∃ y : Space (Module.finrank ℝ V), ‖x-(a+F y)‖ ≤ r} := by
    intro x hx
    refine ⟨sliceCoordinates V rfl (V.orthogonalProjectionOnto (x-a)),?_⟩
    have he : F (sliceCoordinates V rfl (V.orthogonalProjectionOnto (x-a))) =
        V.starProjection (x-a) := by simp [F]
    rw [he]
    have hv := V.starProjection_orthogonal_val (x-a)
    change ‖Vᗮ.starProjection (x-a)‖ ≤ r at hx
    convert hx using 2
    rw [hv]
    abel
  apply (measure_mono hnear).trans
    ((affine_plane_frostman_bound μ F a hM ha hC hbounded hfrost hr hr1).trans ?_)
  apply ENNReal.ofReal_le_ofReal
  have hp : (2*(M+M+1)+1)^(Module.finrank ℝ V) ≤ (4*M+3)^k := by
    rw [show 2*(M+M+1)+1 = 4*M+3 by ring]
    exact pow_le_pow_right₀ (by linarith only [hM]) hdim
  have hrp : r^(s-(Module.finrank ℝ V:ℝ)) ≤ r^(s-(k:ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_ge hr hr1
    exact sub_le_sub_left (Nat.cast_le.mpr hdim) s
  exact mul_le_mul (mul_le_mul_of_nonneg_left hp (by positivity)) hrp
    (by positivity) (by positivity)

end Falconer

end OAI

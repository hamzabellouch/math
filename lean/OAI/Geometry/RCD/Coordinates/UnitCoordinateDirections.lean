import OAI.Geometry.RCD.Harmonic.HomogeneousAffineImprovement

namespace OAI

/-! # The finite unit directions used to identify the coordinate Gram matrix -/

open Set Metric MeasureTheory
open scoped InnerProductSpace
noncomputable section
namespace RegularPointCoordinates

theorem coordinate_projection_norm {n : ℕ} (i : Fin n) :
    ‖(EuclideanSpace.proj i : Euclidean n →L[ℝ] ℝ)‖=1 := by
  apply le_antisymm
  · exact ContinuousLinearMap.opNorm_le_bound _ zero_le_one
      (fun z => by simpa using PiLp.norm_apply_le z i)
  · have h := (EuclideanSpace.proj i : Euclidean n →L[ℝ] ℝ).le_opNorm
      (EuclideanSpace.single i 1)
    simpa using h

theorem coordinate_pair_unit_norm {n : ℕ} (i j : Fin n) (hij : i≠j) :
    ‖(Real.sqrt 2)⁻¹ • ((EuclideanSpace.proj i : Euclidean n →L[ℝ] ℝ)+EuclideanSpace.proj j)‖=1 := by
  let ei : Euclidean n := EuclideanSpace.single i 1
  let ej : Euclidean n := EuclideanSpace.single j 1
  have heq : ((EuclideanSpace.proj i : Euclidean n →L[ℝ] ℝ)+EuclideanSpace.proj j)=
      innerSL ℝ (ei+ej) := by
    ext z
    simp [ei,ej,EuclideanSpace.inner_single_left]
  have hs : ‖ei+ej‖^2=2 := by
    rw [norm_add_sq_real]
    norm_num [ei,ej,EuclideanSpace.inner_single_left,hij]
  have hsn : ‖ei+ej‖=Real.sqrt 2 := by
    nlinarith [norm_nonneg (ei+ej),Real.sqrt_nonneg 2,Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity),heq,innerSL_apply_norm,hsn]
  exact inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (by norm_num)))

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

omit [ProperSpace X] in
theorem harmonicTargetNorm_add_le {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
    (p : X) (r : ℝ) (f g : SobolevSpace (hausdorff n X) hX.quadratic) :
    harmonicTargetNorm hX p r (f+g)≤harmonicTargetNorm hX p r f+harmonicTargetNorm hX p r g := by
  unfold harmonicTargetNorm
  rw [map_add]
  unfold normalizeLocalL2
  rw [smul_add]
  exact norm_add_le _ _

end RegularPointCoordinates

end

end OAI

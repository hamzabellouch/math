import OAI.MeasureTheory.Falconer.Angular.ProjectedDirections
import OAI.MeasureTheory.Falconer.Estimates.SphericalEnergy
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

namespace OAI

/-! # Actual orthogonal-band geometry for the angular slicing argument -/

namespace Falconer
open Set MeasureTheory NormedSpace
variable {d : ℕ}

noncomputable def pointSliceBand (V : Submodule ℝ (Space d)) (z : Space d) (δ : ℝ) :
    Set (Space d) := {x | ‖Vᗮ.starProjection x-z‖ ≤ δ}

noncomputable def directionSliceBand (V : Submodule ℝ (Space d)) (δ : ℝ) :
    Set (Sphere d) := {w | ‖Vᗮ.starProjection (w:Space d)‖ ≤ δ}

theorem pointSliceBand_measurable (V : Submodule ℝ (Space d)) (z : Space d) (δ : ℝ) :
    MeasurableSet (pointSliceBand V z δ) :=
  measurableSet_le (by fun_prop) measurable_const

theorem directionSliceBand_measurable (V : Submodule ℝ (Space d)) (δ : ℝ) :
    MeasurableSet (directionSliceBand V δ) :=
  measurableSet_le (by fun_prop) measurable_const

theorem pointSliceBand_projection_ball (V : Submodule ℝ (Space d))
    {z x a : Space d} {δ r : ℝ} (hx : x ∈ pointSliceBand V z δ)
    (ha : ‖V.starProjection x-a‖ ≤ r) : ‖x-(a+z)‖ ≤ r+δ := by
  have he : x-(a+z) = (V.starProjection x-a)+(Vᗮ.starProjection x-z) := by
    rw [Submodule.starProjection_orthogonal_val]
    abel
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add ha hx)

theorem pointSliceBand_pair_distance (V : Submodule ℝ (Space d))
    {z x y : Space d} {δ r : ℝ}
    (hx : x ∈ pointSliceBand V z δ) (hy : y ∈ pointSliceBand V z δ)
    (hxy : ‖V.starProjection x-V.starProjection y‖ ≤ r) : ‖x-y‖ ≤ r+2*δ := by
  change ‖Vᗮ.starProjection x-z‖ ≤ δ at hx
  change ‖Vᗮ.starProjection y-z‖ ≤ δ at hy
  have he : x-y = (V.starProjection x-V.starProjection y)+
      ((Vᗮ.starProjection x-z)-(Vᗮ.starProjection y-z)) := by
    simp only [Submodule.starProjection_orthogonal_val]
    abel
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add hxy
    ((norm_sub_le _ _).trans (by change _ ≤ 2*δ; linarith)))

theorem directionSliceBand_projection_lower (V : Submodule ℝ (Space d))
    {w : Sphere d} {δ : ℝ} (hw : w ∈ directionSliceBand V δ) :
    1-δ ≤ ‖V.starProjection (w:Space d)‖ := by
  have he : (w:Space d) = V.starProjection (w:Space d)+Vᗮ.starProjection (w:Space d) := by
    rw [Submodule.starProjection_orthogonal_val]
    abel
  have hh := norm_add_le (V.starProjection (w:Space d)) (Vᗮ.starProjection (w:Space d))
  rw [← he,sphere_norm] at hh
  change ‖Vᗮ.starProjection (w:Space d)‖ ≤ δ at hw
  linarith

theorem norm_sub_normalize (v : Space d) (hv : v ≠ 0) :
    ‖v-normalize v‖ = |‖v‖-1| := by
  calc
    _ = ‖(‖v‖-1) • normalize v‖ := by
      congr 1
      rw [sub_smul,norm_smul_normalize,one_smul]
    _ = _ := by rw [norm_smul,norm_normalize hv,Real.norm_eq_abs,mul_one]

theorem directionSliceBand_normalize_error (V : Submodule ℝ (Space d))
    {w : Sphere d} {δ : ℝ} (hδ : δ < 1) (hw : w ∈ directionSliceBand V δ) :
    ‖normalize (V.starProjection (w:Space d))-(w:Space d)‖ ≤ 2*δ := by
  have hp : V.starProjection (w:Space d) ≠ 0 := norm_pos_iff.mp
    ((sub_pos.mpr hδ).trans_le (directionSliceBand_projection_lower V hw))
  have herr : ‖V.starProjection (w:Space d)-(w:Space d)‖ ≤ δ := by
    change ‖Vᗮ.starProjection (w:Space d)‖ ≤ δ at hw
    simpa only [Submodule.starProjection_orthogonal_val,norm_sub_rev] using hw
  have hnorm : |‖V.starProjection (w:Space d)‖-1| ≤ δ := by
    simpa only [sphere_norm] using (abs_norm_sub_norm_le _ (w:Space d)).trans herr
  calc
    _ ≤ ‖normalize (V.starProjection (w:Space d))-V.starProjection (w:Space d)‖+
        ‖V.starProjection (w:Space d)-(w:Space d)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ δ+δ := add_le_add (by rw [norm_sub_rev,norm_sub_normalize _ hp]; exact hnorm) herr
    _ = _ := by ring

end Falconer

end OAI

import OAI.MeasureTheory.Falconer.Slicing.SliceGeometry
import OAI.MeasureTheory.Falconer.Angular.AngularTubes

namespace OAI

/-! # Original tube anchors and projected tube widths in an orthogonal slice -/

namespace Falconer
open NormedSpace
variable {d : ℕ}

theorem slice_active_anchor (V : Submodule ℝ (Space d)) {w : Sphere d}
    {x a z : Space d} {δ ε L : ℝ} (_hδ : 0 ≤ δ)
    (hw : w ∈ directionSliceBand V δ) (hx : x ∈ pointSliceBand V z δ)
    (htube : ‖perpendicularPart (w:Space d) (x-a)‖ ≤ ε)
    (hlength : |inner ℝ (w:Space d) (x-a)| ≤ L) :
    ‖Vᗮ.starProjection a-z‖ ≤ δ+L*δ+ε := by
  let t := inner ℝ (w:Space d) (x-a)
  let e := perpendicularPart (w:Space d) (x-a)
  have he : a = x-t • (w:Space d)-e := by dsimp [t,e,perpendicularPart]; module
  have he' : Vᗮ.starProjection a-z = (Vᗮ.starProjection x-z)-
      t • Vᗮ.starProjection (w:Space d)-Vᗮ.starProjection e := by
    rw [he,map_sub,map_sub,map_smul]
    abel
  have ht : ‖t • Vᗮ.starProjection (w:Space d)‖ ≤ L*δ := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul hlength hw (norm_nonneg _) ((abs_nonneg _).trans hlength)
  have heps : ‖Vᗮ.starProjection e‖ ≤ ε :=
    (Vᗮ.norm_starProjection_apply_le e).trans htube
  rw [he']
  calc
    _ ≤ (‖Vᗮ.starProjection x-z‖+‖t • Vᗮ.starProjection (w:Space d)‖)+
        ‖Vᗮ.starProjection e‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ _ := add_le_add (add_le_add hx ht) heps

theorem slice_projected_tube_width (V : Submodule ℝ (Space d)) {w : Sphere d}
    {δ : ℝ} (hδ : δ < 1) (hw : w ∈ directionSliceBand V δ) (x a : Space d) :
    ‖perpendicularPart (normalize (V.starProjection (w:Space d)))
      (V.starProjection x-V.starProjection a)‖ ≤ ‖perpendicularPart (w:Space d) (x-a)‖ := by
  let v := V.starProjection (w:Space d)
  let u := normalize v
  let t := inner ℝ (w:Space d) (x-a)
  let e := perpendicularPart (w:Space d) (x-a)
  have hv : v ≠ 0 := norm_pos_iff.mp
    ((sub_pos.mpr hδ).trans_le (directionSliceBand_projection_lower V hw))
  have hu : ‖u‖ = 1 := norm_normalize hv
  have hperp : perpendicularPart u v = 0 := by
    have hv' : v = ‖v‖ • u := (norm_smul_normalize v).symm
    rw [hv',perpendicularPart_smul]
    simp [perpendicularPart,hu]
  have hsplit : V.starProjection x-V.starProjection a = t • v+V.starProjection e := by
    dsimp [v,t,e,perpendicularPart]
    simp only [map_sub,map_smul]
    module
  change ‖perpendicularPart u (V.starProjection x-V.starProjection a)‖ ≤ ‖e‖
  rw [hsplit]
  have he : perpendicularPart u (t • v+V.starProjection e) = perpendicularPart u (V.starProjection e) := by
    calc
      _ = t • perpendicularPart u v+perpendicularPart u (V.starProjection e) := by
        simp only [perpendicularPart,inner_add_right,inner_smul_right,add_smul]
        module
      _ = _ := by rw [hperp,smul_zero,zero_add]
  rw [he]
  exact (norm_perpendicularPart_le hu _).trans (V.norm_starProjection_apply_le e)

end Falconer

end OAI

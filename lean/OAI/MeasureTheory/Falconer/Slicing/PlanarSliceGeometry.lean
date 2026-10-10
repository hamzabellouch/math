import OAI.MeasureTheory.Falconer.Slicing.SliceCoordinates
import OAI.MeasureTheory.Falconer.Slicing.TransverseFrame

namespace OAI

/-! # Oriented planar coordinates and the strip equations of sliced tubes -/

namespace Falconer
open NormedSpace

theorem exists_unit_axis_isometry {m : ℕ} (hm : 0 < m)
    {v : Space m} (hv : ‖v‖ = 1) :
    ∃ R : Space m ≃ₗᵢ[ℝ] Space m,
      R v = EuclideanSpace.basisFun (Fin m) ℝ ⟨0,hm⟩ := by
  let u := EuclideanSpace.basisFun (Fin m) ℝ ⟨0,hm⟩
  let S : Space m ≃ₗᵢ[ℝ] Space m := (ℝ ∙ (u-v))ᗮ.reflection
  have he : S u = v := Submodule.reflection_sub
    (((EuclideanSpace.basisFun (Fin m) ℝ).norm_eq_one ⟨0,hm⟩).trans hv.symm)
  exact ⟨S.symm,by rw [← he,S.symm_apply_apply]⟩

noncomputable def planarSlope (w : Space 2) : ℝ := w 1 / w 0

noncomputable def planarIntercept (w x : Space 2) : ℝ := x 1-planarSlope w*x 0

theorem planarSlope_small_of_axis_close {w : Space 2}
    (hw : dist w (EuclideanSpace.basisFun (Fin 2) ℝ 0) ≤ 1/4) :
    0 < w 0 ∧ |planarSlope w| ≤ 1/2 := by
  have hzero := (PiLp.dist_apply_le w (EuclideanSpace.basisFun (Fin 2) ℝ 0) 0).trans hw
  have hone := (PiLp.dist_apply_le w (EuclideanSpace.basisFun (Fin 2) ℝ 0) 1).trans hw
  have hz : |w 0-1| ≤ 1/4 := by simpa [Real.dist_eq] using hzero
  have ho : |w 1| ≤ 1/4 := by simpa [Real.dist_eq] using hone
  have hpos : 0 < w 0 := by have := (abs_le.mp hz).1; linarith
  refine ⟨hpos,?_⟩
  rw [planarSlope,abs_div,abs_of_pos hpos]
  apply (div_le_iff₀ hpos).mpr
  have := (abs_le.mp hz).1
  linarith

theorem planarIntercept_sub (w x a : Space 2) :
    planarIntercept w (x-a) = planarIntercept w x-planarIntercept w a := by
  simp only [planarIntercept,PiLp.sub_apply]
  ring

theorem planarIntercept_perpendicular {w : Space 2} (hw : w 0 ≠ 0) (x : Space 2) :
    planarIntercept w (perpendicularPart w x) = planarIntercept w x := by
  simp only [planarIntercept,planarSlope,perpendicularPart,PiLp.sub_apply,PiLp.smul_apply,
    smul_eq_mul]
  field_simp
  ring

theorem planarIntercept_norm_bound (w x : Space 2) :
    |planarIntercept w x| ≤ (1+|planarSlope w|)*‖x‖ := by
  calc
    _ ≤ |x 1|+|planarSlope w*x 0| := abs_sub _ _
    _ = |x 1|+|planarSlope w| * |x 0| := by rw [abs_mul]
    _ ≤ ‖x‖+|planarSlope w| * ‖x‖ :=
      add_le_add (PiLp.norm_apply_le x 1)
        (mul_le_mul_of_nonneg_left (PiLp.norm_apply_le x 0) (abs_nonneg _))
    _ = _ := by ring

theorem planar_tube_strip {w x a : Space 2} {ε : ℝ}
    (hw : w 0 ≠ 0) (hslope : |planarSlope w| ≤ 1/2)
    (htube : ‖perpendicularPart w (x-a)‖ ≤ ε) :
    |x 1-planarSlope w*x 0-planarIntercept w a| ≤ (3/2)*ε := by
  change |planarIntercept w x-planarIntercept w a| ≤ _
  rw [← planarIntercept_sub,← planarIntercept_perpendicular hw]
  exact (planarIntercept_norm_bound w _).trans
    (mul_le_mul (by linarith) htube (norm_nonneg _) (by norm_num))

end Falconer

end OAI

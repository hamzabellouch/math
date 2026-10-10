import OAI.MeasureTheory.Falconer.Graphs.GraphGeometry

namespace OAI

namespace PlanarFalconer

theorem norm_affine_remainder (v u : Plane) (hu : u ≠ 0) :
    |‖v‖-planeDot v (‖u‖⁻¹ • u)| ≤ ‖v-u‖^2/(2*‖u‖) := by
  have hupos : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hnonneg : 0 ≤ ‖v‖-planeDot v (‖u‖⁻¹ • u) := by
    have h := (le_abs_self (planeDot v (‖u‖⁻¹ • u))).trans (planeDot_abs_le _ _)
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hupos),
      inv_mul_cancel₀ hupos.ne',mul_one] at h
    linarith
  have hdot : ‖u‖*planeDot v (‖u‖⁻¹ • u) = planeDot v u := by
    simp only [planeDot,PiLp.smul_apply,smul_eq_mul]
    field_simp
  have hi : inner ℝ v u = planeDot v u := by
    simp [planeDot,EuclideanSpace.inner_eq_star_dotProduct,Fin.sum_univ_two,dotProduct,mul_comm]
  have he := norm_sub_sq_real v u
  rw [hi] at he
  rw [abs_of_nonneg hnonneg]
  apply (le_div_iff₀ (by positivity)).mpr
  nlinarith [sq_nonneg (‖v‖-‖u‖)]

end PlanarFalconer

end OAI

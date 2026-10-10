import OAI.MathematicalPhysics.DefocusingNLS.Profile.ProfileTaylorBound
import OAI.MathematicalPhysics.DefocusingNLS.Profile.ProfileCentralEnclosures

namespace OAI

/-! Uniform entrywise bounds for the actual K=34 free matching product. -/

open Matrix
namespace DefocusingNLS.ProfileCertificate

attribute [local irreducible] profileProduct

private theorem derivativeB_entry (i j : Fin 2) :
    ‖complexMatrix result.derivB i j‖ < 20*‖centralM‖ := by
  fin_cases i <;> fin_cases j <;> exact central_derivative_entries _ (by simp [Matrix2.toMatrix])

private theorem derivativeZ_entry (i j : Fin 2) :
    ‖complexMatrix result.derivZ i j‖ < 20*‖centralM‖ := by
  fin_cases i <;> fin_cases j <;> exact central_derivative_entries _ (by simp [Matrix2.toMatrix])

private theorem error_entry (i j : Fin 2) :
    rationalMatrix result.error i j < 50000*‖centralM‖ := by
  fin_cases i <;> fin_cases j <;> exact (central_error_entries _ (by simp [Matrix2.toMatrix])).2

/-- The entrywise complex Taylor remainder in `free:profile-enclosures`. -/
theorem profile_entry_remainder (b z : ℝ)
    (hb : |b| ≤ (radius : ℝ)) (hz : |z| ≤ (radius : ℝ)) (i j : Fin 2) :
    ‖profileProduct ((centerB : ℝ)+b) ((centerZ : ℝ)+z) 34 i j-
      complexMatrix result.value i j-
      (b : ℂ)*complexMatrix result.derivB i j-
      (z : ℂ)*complexMatrix result.derivZ i j‖ <
        50000*‖centralM‖*(radius : ℝ)^2 := by
  have h := profileProduct_remainder b z hb hz i j
  have he : 0 < (radius : ℝ)^2 := by norm_num [radius]
  have hs := mul_lt_mul_of_pos_left (error_entry i j) he
  have hnorm :
      ‖profileProduct ((centerB : ℝ)+b) ((centerZ : ℝ)+z) 34 i j-
        complexMatrix result.value i j-
        (b : ℂ)*complexMatrix result.derivB i j-
        (z : ℂ)*complexMatrix result.derivZ i j‖ ≤
          (radius : ℝ)^2*rationalMatrix result.error i j := by
    convert! h using 1
    simp only [linearModel, Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
      Complex.real_smul]
    congr 1
    ring
  exact hnorm.trans_lt (hs.trans_eq (by ring))

/-- The entire matrix varies by less than chi times the central denominator. -/
theorem profile_entry_variation (b z : ℝ)
    (hb : |b| ≤ (radius : ℝ)) (hz : |z| ≤ (radius : ℝ)) (i j : Fin 2) :
    ‖profileProduct ((centerB : ℝ)+b) ((centerZ : ℝ)+z) 34 i j-
      complexMatrix result.value i j‖ < (changeBound : ℝ)*‖centralM‖ := by
  let L := profileProduct ((centerB : ℝ)+b) ((centerZ : ℝ)+z) 34 i j
  let U := complexMatrix result.value i j
  let X := complexMatrix result.derivB i j
  let Y := complexMatrix result.derivZ i j
  have hδ : 0 ≤ (radius : ℝ) := by norm_num [radius]
  have hx : ‖(b : ℂ)*X‖ ≤ (radius : ℝ)*(20*‖centralM‖) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul hb (derivativeB_entry i j).le (norm_nonneg _) hδ
  have hy : ‖(z : ℂ)*Y‖ ≤ (radius : ℝ)*(20*‖centralM‖) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul hz (derivativeZ_entry i j).le (norm_nonneg _) hδ
  calc
    ‖L-U‖ = ‖(L-U-(b : ℂ)*X-(z : ℂ)*Y)+(b : ℂ)*X+(z : ℂ)*Y‖ := by
      congr 1; ring
    _ ≤ ‖L-U-(b : ℂ)*X-(z : ℂ)*Y‖+‖(b : ℂ)*X‖+‖(z : ℂ)*Y‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ < 50000*‖centralM‖*(radius : ℝ)^2+
        (radius : ℝ)*(20*‖centralM‖)+(radius : ℝ)*(20*‖centralM‖) := by
      exact add_lt_add_of_lt_of_le
        (add_lt_add_of_lt_of_le (profile_entry_remainder b z hb hz i j) hx) hy
    _ = _ := by unfold changeBound; push_cast; ring

noncomputable def normalizedProfile (b z : ℝ) (i j : Fin 2) : ℂ :=
  profileProduct ((centerB : ℝ)+b) ((centerZ : ℝ)+z) 34 i j/centralM

noncomputable def centralNormalized (i j : Fin 2) : ℂ :=
  complexMatrix result.value i j/centralM

theorem normalizedProfile_variation (b z : ℝ)
    (hb : |b| ≤ (radius : ℝ)) (hz : |z| ≤ (radius : ℝ)) (i j : Fin 2) :
    ‖normalizedProfile b z i j-centralNormalized i j‖ < (changeBound : ℝ) := by
  rw [normalizedProfile, centralNormalized, ← sub_div, norm_div]
  exact (div_lt_iff₀ (norm_pos_iff.mpr centralM_ne_zero)).mpr
    (profile_entry_variation b z hb hz i j)

@[simp] theorem centralNormalized_zero_one : centralNormalized 0 1 = 1 := by
  exact div_self centralM_ne_zero

end DefocusingNLS.ProfileCertificate

end OAI

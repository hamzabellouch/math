import OAI.MathematicalPhysics.DefocusingNLS.Profile.ProfileCertificateComparisons
import OAI.MathematicalPhysics.DefocusingNLS.Profile.ProfileMatrixProduct

namespace OAI

/-! The scalar determinant bound holds for the actual parameter-dependent product. -/

open Matrix BigOperators
namespace DefocusingNLS.ProfileCertificate

attribute [local irreducible] backwardProduct profileProduct

private theorem backward_det_normSq (b Z : ℝ) (K : ℕ) :
    Complex.normSq (backwardProduct 5 (Complex.I*Z) (-Complex.I*b) K).det =
      ∏ n ∈ Finset.range K, (((n : ℝ)^2+b^2)*(((n : ℝ)-5)^2+b^2)) := by
  induction K with
  | zero => simp [backwardProduct]
  | succ K ih =>
      rw [backwardProduct, Matrix.det_mul, Complex.normSq_mul, ih,
        det_backwardMatrix, Finset.prod_range_succ]
      congr 1
      rw [Complex.normSq_mul]
      simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
      ring

private theorem profile_det_normSq (b Z : ℝ) (K : ℕ) :
    Complex.normSq (profileProduct b Z K).det =
      (∏ n ∈ Finset.range K, (((n : ℝ)^2+b^2)*(((n : ℝ)-5)^2+b^2)))/
        (K.factorial : ℝ)^4 := by
  rw [profileProduct, Matrix.det_smul, Fintype.card_fin, Complex.normSq_mul,
    map_pow, Complex.normSq_inv, Complex.normSq_natCast, backward_det_normSq]
  simp only [div_eq_mul_inv, _root_.mul_inv_rev, mul_pow]
  ring

private theorem profile_det_bound (b Z B : ℝ) (hB : |b| ≤ B) (K : ℕ) :
    Complex.normSq (profileProduct b Z K).det ≤
      (∏ n ∈ Finset.range K, (((n : ℝ)^2+B^2)*(((n : ℝ)-5)^2+B^2)))/
        (K.factorial : ℝ)^4 := by
  rw [profile_det_normSq]
  have hBB : 0 ≤ B := (abs_nonneg b).trans hB
  have hb : b^2 ≤ B^2 := by
    have h := mul_self_le_mul_self (abs_nonneg b) hB
    nlinarith [sq_abs b]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply Finset.prod_le_prod₀
  · intro n _; positivity
  · intro n _
    apply mul_le_mul <;> nlinarith [sq_nonneg (n : ℝ), sq_nonneg ((n : ℝ)-5)]

private theorem certificate_as_real : (determinantSqBound : ℝ) =
    (∏ n ∈ Finset.range 34,
      (((n : ℝ)^2+((centerB : ℝ)+(radius : ℝ))^2)*
        (((n : ℝ)-5)^2+((centerB : ℝ)+(radius : ℝ))^2)))/(Nat.factorial 34 : ℝ)^4 := by
  unfold determinantSqBound
  simp only [bind_pure_comp, List.map_eq_map, List.map_map, Function.comp_def]
  rw [← List.prod_toFinset _ List.nodup_range]
  simp only [List.toFinset_range]
  push_cast
  rfl

/-- Uniform determinant modulus bound throughout the certificate square. -/
theorem actual_profile_determinant_bound (b z : ℝ) (hb : |b| ≤ (radius : ℝ)) :
    ‖(profileProduct ((centerB : ℝ)+b) ((centerZ : ℝ)+z) 34).det‖ <
      (62/10000000000000 : ℝ)*‖RationalComplex.toComplex result.value.b‖^2 := by
  have hcb : 0 ≤ (centerB : ℝ) := by norm_num [centerB]
  have hB : |(centerB : ℝ)+b| ≤ (centerB : ℝ)+(radius : ℝ) := by
    exact (abs_add_le _ _).trans (by
      simpa only [abs_of_nonneg hcb] using add_le_add le_rfl hb)
  have hu := profile_det_bound ((centerB : ℝ)+b) ((centerZ : ℝ)+z)
    ((centerB : ℝ)+(radius : ℝ)) hB 34
  rw [← certificate_as_real] at hu
  have hc := (Rat.cast_lt (K := ℝ)).mpr determinant_bound
  push_cast at hc
  rw [← RationalComplex.normSq_toComplex, Complex.normSq_eq_norm_sq] at hc
  have hs := hu.trans_lt hc
  rw [Complex.normSq_eq_norm_sq] at hs
  nlinarith [norm_nonneg ((profileProduct ((centerB : ℝ)+b) ((centerZ : ℝ)+z) 34).det),
    sq_nonneg ‖RationalComplex.toComplex result.value.b‖]

end DefocusingNLS.ProfileCertificate

end OAI

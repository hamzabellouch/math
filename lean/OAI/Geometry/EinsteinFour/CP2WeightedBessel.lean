import OAI.Geometry.EinsteinFour.CP2Overlap

namespace OAI

/-! Bessel's inequality for the two orthogonal directions used in the
projective midpoint construction. -/

namespace PositiveEinsteinFour

open EinsteinFour
open scoped BigOperators

noncomputable section

private def cp2Normalize (v : CP2Vector) : CP2Vector :=
  (((‖v‖⁻¹ : ℝ) : ℂ)) • v

private theorem cp2Normalize_norm (v : CP2Vector) (hv : v ≠ 0) :
    ‖cp2Normalize v‖ = 1 := by
  simp [cp2Normalize, norm_smul, Complex.norm_real, norm_ne_zero_iff.mpr hv]

private theorem cp2Normalize_inner_norm (v w : CP2Vector) :
    ‖inner ℂ (cp2Normalize v) w‖ = ‖v‖⁻¹ * ‖inner ℂ v w‖ := by
  simp only [cp2Normalize, inner_smul_left, norm_mul, RCLike.norm_conj, Complex.norm_real]
  rw [Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg v))]

theorem cp2_weighted_bessel (u v w : CP2Vector) (hu : u ≠ 0) (hv : v ≠ 0)
    (huv : inner ℂ u v = 0) :
    ‖inner ℂ u w‖ ^ 2 / ‖u‖ ^ 2 + ‖inner ℂ v w‖ ^ 2 / ‖v‖ ^ 2 ≤ ‖w‖ ^ 2 := by
  let U := cp2Normalize u
  let V := cp2Normalize v
  have hU : ‖U‖ = 1 := cp2Normalize_norm u hu
  have hV : ‖V‖ = 1 := cp2Normalize_norm v hv
  have hUV : inner ℂ U V = 0 := by simp [U, V, cp2Normalize, huv]
  have hVU : inner ℂ V U = 0 := by rw [← inner_conj_symm, hUV]; simp
  have horth : Orthonormal ℂ ![U, V] := by
    apply orthonormal_iff_ite.mpr
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [inner_self_eq_norm_sq_to_K, hU, hV, hUV, hVU]
  have h := horth.sum_inner_products_le (s := Finset.univ) w
  have hsum : ‖inner ℂ U w‖ ^ 2 + ‖inner ℂ V w‖ ^ 2 ≤ ‖w‖ ^ 2 := by
    simpa [Fin.sum_univ_two] using h
  have hU' := cp2Normalize_inner_norm u w
  have hV' := cp2Normalize_inner_norm v w
  change ‖inner ℂ U w‖ = _ at hU'
  change ‖inner ℂ V w‖ = _ at hV'
  rw [hU', hV', mul_pow, mul_pow, inv_pow, inv_pow] at hsum
  simpa only [div_eq_mul_inv, mul_comm] using hsum

end
end PositiveEinsteinFour

end OAI

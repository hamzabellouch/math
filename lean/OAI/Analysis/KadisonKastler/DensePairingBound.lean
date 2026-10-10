import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Topology.DenseEmbedding
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace OAI

/-! # Passing pairing estimates from a dense set to operator norm -/

namespace KadisonKastler

variable {A H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A homogeneous pairing estimate on a dense image controls the operator
norm. This is used after the finite randomization and clipping argument. -/
theorem opNorm_le_of_dense_pairing (J : A → H) (hJ : DenseRange J)
    (V : H →L[ℂ] H) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ a b, ‖inner ℂ (V (J a)) (J b)‖ ≤ C * ‖J a‖ * ‖J b‖) :
    ‖V‖ ≤ C := by
  have hfull (x y : H) : ‖inner ℂ (V x) y‖ ≤ C * ‖x‖ * ‖y‖ :=
    hJ.induction_on₂ (isClosed_le (by fun_prop) (by fun_prop)) hbound x y
  apply ContinuousLinearMap.opNorm_le_of_re_inner_le hC
  intro x y hx hy
  exact (Complex.re_le_norm _).trans (by simpa only [hx, hy, mul_one] using hfull x y)

variable [AddCommMonoid A] [Module ℂ A]

/-- It suffices to test the unit vectors in a dense linear image. -/
theorem opNorm_le_of_dense_unit_pairing (J : A →ₗ[ℂ] H) (hJ : DenseRange J)
    (V : H →L[ℂ] H) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ a b, ‖J a‖ ≤ 1 → ‖J b‖ ≤ 1 → ‖inner ℂ (V (J a)) (J b)‖ ≤ C) :
    ‖V‖ ≤ C := by
  apply opNorm_le_of_dense_pairing J hJ V hC
  intro a b
  by_cases ha : J a = 0
  · simp [ha]
  by_cases hb : J b = 0
  · simp [hb]
  have hna : 0 < ‖J a‖ := norm_pos_iff.mpr ha
  have hnb : 0 < ‖J b‖ := norm_pos_iff.mpr hb
  let ca : ℂ := (‖J a‖⁻¹ : ℝ)
  let cb : ℂ := (‖J b‖⁻¹ : ℝ)
  have hca : ‖ca‖ = ‖J a‖⁻¹ := by simp [ca]
  have hcb : ‖cb‖ = ‖J b‖⁻¹ := by simp [cb]
  have hja : ‖J (ca • a)‖ ≤ 1 := by
    rw [map_smul, norm_smul, hca, inv_mul_cancel₀ hna.ne']
  have hjb : ‖J (cb • b)‖ ≤ 1 := by
    rw [map_smul, norm_smul, hcb, inv_mul_cancel₀ hnb.ne']
  have hh := hbound (ca • a) (cb • b) hja hjb
  simp only [map_smul, inner_smul_left, inner_smul_right, norm_mul,
    starRingEnd_apply, norm_star, hca, hcb] at hh
  calc
    _ = (‖J a‖ * ‖J b‖) *
        (‖J b‖⁻¹ * (‖J a‖⁻¹ * ‖inner ℂ (V (J a)) (J b)‖)) := by
      field_simp [hna.ne', hnb.ne']
    _ ≤ (‖J a‖ * ‖J b‖) * C :=
      mul_le_mul_of_nonneg_left hh (mul_nonneg hna.le hnb.le)
    _ = _ := by ring

end KadisonKastler

end OAI

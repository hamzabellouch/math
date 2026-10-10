import OAI.NumberTheory.Ostmann.Characters.CharacterCompletedLogGrowth

namespace OAI

/-! # The order-one growth hypothesis for completed character L-functions -/

namespace Ostmann

/-- Concrete growth in the exact epsilon-family form needed for Hadamard
factorization. No abstract growth hypothesis on the L-function is used. -/
theorem character_completed_order_one (χ : PrimitiveComplexCharacter) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ,
      ‖χ.completed z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ (1 + ε)) := by
  obtain ⟨A, hA, hbound⟩ := character_completed_log_growth χ
  intro ε hε
  let D := 1 + Real.log 3 + ε⁻¹
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨3 * A * D, by positivity, ?_⟩
  intro z
  let N : ℕ := ⌊‖z‖⌋₊
  let x : ℝ := 1 + ‖z‖
  have hx : 1 ≤ x := by dsimp [x]; linarith [norm_nonneg z]
  have hxpos : 0 < x := by linarith
  have hN : (N : ℝ) ≤ ‖z‖ := Nat.floor_le (norm_nonneg z)
  have hzN : ‖z‖ ≤ (N : ℝ) + 1 := (Nat.lt_floor_add_one ‖z‖).le
  have ht : (N : ℝ) + 3 ≤ 3 * x := by dsimp [x]; linarith [norm_nonneg z]
  have htpos : 0 < (N : ℝ) + 3 := by positivity
  have htlog : Real.log ((N : ℝ) + 3) ≤ Real.log 3 + Real.log x := by
    have hh := Real.log_le_log htpos ht
    rwa [Real.log_mul (by norm_num) hxpos.ne'] at hh
  have hlogN : 0 ≤ Real.log ((N : ℝ) + 3) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) N])
  have hpow : 1 ≤ x ^ ε := Real.one_le_rpow hx hε.le
  have hlogx : Real.log x ≤ x ^ ε / ε := Real.log_le_rpow_div hxpos.le hε
  have hlog : 1 + Real.log ((N : ℝ) + 3) ≤ D * x ^ ε := by
    have hh := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 1 + Real.log 3)
    dsimp [D]
    rw [div_eq_mul_inv] at hlogx
    nlinarith
  have hg : Real.log ‖χ.completed z‖ ≤ (3 * A * D) * x ^ (1 + ε) := by
    apply (hbound N z hzN).trans
    have hh := mul_le_mul ht hlog (by positivity) (by positivity)
    have hh' := mul_le_mul_of_nonneg_left hh hA.le
    convert hh' using 1
    · ring
    · rw [Real.rpow_add hxpos, Real.rpow_one]
      ring
  exact (Real.le_exp_log ‖χ.completed z‖).trans (Real.exp_le_exp.mpr hg)

end Ostmann

end OAI

import OAI.NumberTheory.Ostmann.ZeroDensity.CompletedDiskZeros
import OAI.NumberTheory.Ostmann.Characters.CharacterCompletedLogGrowth

namespace OAI

/-! # Common logarithmic growth rates for the function and its disk divisor -/

namespace Ostmann

private theorem affine_log_growth_bound (a b x : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hx : 1 ≤ x) (hxab : x ≤ a * b) :
    x * (1 + Real.log x) ≤ a * (1 + Real.log a) * b * (1 + Real.log b) := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hx0 : 0 < x := by linarith
  have hla := Real.log_nonneg ha
  have hlb := Real.log_nonneg hb
  have hlx := Real.log_nonneg hx
  have hl := Real.log_le_log hx0 hxab
  rw [Real.log_mul ha0.ne' hb0.ne'] at hl
  calc
    _ ≤ (a * b) * (1 + Real.log a + Real.log b) :=
      mul_le_mul hxab (by linarith) (by positivity) (by positivity)
    _ ≤ _ := by
      nlinarith [mul_nonneg (mul_nonneg (mul_nonneg ha0.le hb0.le) hla) hlb]

theorem completed_circle_log_growth (χ : PrimitiveComplexCharacter) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (z : ℂ), ‖z‖ ≤ 3 * ((n : ℝ) + 1) →
      Real.log ‖χ.completed z‖ ≤ C * ((n : ℝ) + 9) * (1 + Real.log ((n : ℝ) + 9)) := by
  obtain ⟨A, hA, hg⟩ := character_completed_log_growth χ
  refine ⟨A * (3 * (1 + Real.log 3)), by positivity [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 3)], ?_⟩
  intro n z hz
  have hb : 1 ≤ (n : ℝ) + 9 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hh := hg (3 * n + 3) z (by push_cast; linarith)
  have hx : 1 ≤ ((3 * n + 3 : ℕ) : ℝ) + 3 := by linarith [Nat.cast_nonneg (α := ℝ) (3 * n + 3)]
  have hxab : ((3 * n + 3 : ℕ) : ℝ) + 3 ≤ 3 * ((n : ℝ) + 9) := by push_cast; linarith
  have hh' := mul_le_mul_of_nonneg_left
    (affine_log_growth_bound 3 ((n : ℝ) + 9) _ (by norm_num) hb hx hxab) hA.le
  exact hh.trans (by convert hh' using 1 <;> ring)

theorem completed_disk_mass_log_growth (χ : PrimitiveComplexCharacter) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      (∑ z ∈ completedDiskZeros χ ((n : ℝ) + 1), (analyticOrderNatAt χ.completed z : ℝ)) ≤
        C * ((n : ℝ) + 9) * (1 + Real.log ((n : ℝ) + 9)) := by
  let K : ℝ := 32 / Real.log (14 / 13)
  let a : ℝ := 2 * χ.modulus
  have hq : (1 : ℝ) ≤ χ.modulus := by exact_mod_cast χ.positive
  have hK : 0 < K := div_pos (by norm_num) (Real.log_pos (by norm_num))
  have ha : 1 ≤ a := by dsimp [a]; linarith
  have hla := Real.log_nonneg ha
  refine ⟨K * a * (1 + Real.log a), by positivity, ?_⟩
  intro n
  let x : ℝ := χ.modulus * (2 * ((n : ℝ) + 1) + 2)
  have hx : 1 ≤ x := by dsimp [x]; nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hxlog := Real.log_nonneg hx
  have hb : 1 ≤ (n : ℝ) + 9 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hxab : x ≤ a * ((n : ℝ) + 9) := by
    dsimp [x, a]
    nlinarith
  have h0 : 0 ≤ 2 * ((n : ℝ) + 1) + 1 := by positivity
  have h1 : 2 * ((n : ℝ) + 1) + 1 ≤ x := by dsimp [x]; nlinarith
  have hm := completedDiskZeros_mass_bound χ ((n : ℝ) + 1) (by positivity)
  change _ ≤ K * (2 * ((n : ℝ) + 1) + 1) * Real.log x at hm
  have hp : K * (2 * ((n : ℝ) + 1) + 1) * Real.log x ≤ K * (x * (1 + Real.log x)) := by
    nlinarith [mul_le_mul h1 (show Real.log x ≤ 1 + Real.log x by linarith)
      hxlog (by linarith : 0 ≤ x)]
  have hh := mul_le_mul_of_nonneg_left
    (affine_log_growth_bound a ((n : ℝ) + 9) x ha hb hx hxab) hK.le
  exact hm.trans (hp.trans (by convert hh using 1; ring))

end Ostmann

end OAI

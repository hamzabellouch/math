import OAI.NumberTheory.JointDickman.Counting.CoefficientWindow

namespace OAI

/-! # The floor cutoffs used by smooth minor-arc partial summation -/

namespace JointDickman
open Filter
open scoped Topology

theorem minorArc_support_window {a b : ℝ} (ha : 0 < a) :
    ∀ᶠ B : ℕ in atTop, ∀ X : ℝ, 0 < X →
      (9/10 : ℝ)*B ≤ Real.log X →
      (B : ℝ)^12 ≤ X ∧ ∀ t ∈ Set.Icc (a*X) (b*X),
        2 ≤ ⌊t⌋₊ ∧ (B : ℝ)/2 ≤ Real.log (⌊t⌋₊ : ℝ) ∧
          X ≤ (⌊t⌋₊ : ℝ)*(B : ℝ)^2 ∧ (⌊t⌋₊ : ℝ) ≤ b*X := by
  have hpoly : ∀ᶠ B : ℕ in atTop, (B : ℝ)^12 ≤ Real.exp ((9/10 : ℝ)*B) := by
    have hh := (isLittleO_pow_exp_pos_mul_atTop 12
      (by norm_num : (0 : ℝ) < 9/10)).def (by norm_num : (0 : ℝ) < 1)
    filter_upwards [tendsto_natCast_atTop_atTop.eventually hh] with B hB
    simpa only [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (Nat.cast_nonneg B : (0 : ℝ) ≤ B) 12),
      abs_of_pos (Real.exp_pos _),one_mul] using hB
  have hlog : ∀ᶠ B : ℕ in atTop, -Real.log (a/2) ≤ (2/5 : ℝ)*B :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 2/5)).eventually_ge_atTop _
  have hpow : ∀ᶠ B : ℕ in atTop, 2/a ≤ (B : ℝ)^2 :=
    ((tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  filter_upwards [hpoly,hlog,hpow,coefficient_support_window ha] with B hp hl hB hw
  intro X hX hlogX
  have hexp : Real.exp ((9/10 : ℝ)*B) ≤ X := by
    simpa only [Real.exp_log hX] using Real.exp_le_exp.mpr hlogX
  refine ⟨hp.trans hexp,?_⟩
  intro t ht
  have hlarge : 9 ≤ a*X := (hw X hX hlogX).1
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have hfloor : t/2 ≤ (⌊t⌋₊ : ℝ) := by
    have hh := Nat.lt_floor_add_one t
    linarith [ht.1]
  have hlow : a/2*X ≤ (⌊t⌋₊ : ℝ) := by linarith [ht.1]
  have hfloor0 : 0 < (⌊t⌋₊ : ℝ) := (mul_pos (half_pos ha) hX).trans_le hlow
  refine ⟨(Nat.le_floor_iff ht0).mpr (by norm_num; linarith [ht.1]),?_,?_,
    (Nat.floor_le ht0).trans ht.2⟩
  · have hh := Real.log_le_log (mul_pos (half_pos ha) hX) hlow
    rw [Real.log_mul (half_pos ha).ne' hX.ne'] at hh
    linarith
  · have hscale : 1 ≤ a/2*(B : ℝ)^2 := by
      have hh := mul_le_mul_of_nonneg_left hB (half_pos ha).le
      have he : a/2*(2/a) = 1 := by field_simp
      rwa [he] at hh
    calc
      X = X*1 := (mul_one _).symm
      _ ≤ X*(a/2*(B : ℝ)^2) := mul_le_mul_of_nonneg_left hscale hX.le
      _ = (a/2*X)*(B : ℝ)^2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hlow (sq_nonneg _)

end JointDickman

end OAI

import OAI.NumberTheory.EgyptianFractions.GeometricCharacterBound

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337.RealPhase

/-- Distance to the nearest integer. The tie convention of `round` does not
affect this distance. -/
def integerDistance (x : ℝ) : ℝ := |x - round x|

lemma integerDistance_nonneg (x : ℝ) : 0 ≤ integerDistance x := abs_nonneg _

lemma abs_sin_fract (x : ℝ) :
    |Real.sin (Real.pi * Int.fract x)| = |Real.sin (Real.pi * x)| := by
  have he : Real.pi * Int.fract x = Real.pi * x - (⌊x⌋ : ℝ) * Real.pi := by
    simp only [Int.fract]
    ring
  rw [he, Real.sin_sub_int_mul_pi, abs_mul, abs_zpow]
  simp

/-- Jordan's sine inequality in the nearest-integer convention used by
Diophantine approximation and minor-arc spacing. -/
theorem two_integerDistance_le_abs_sin (x : ℝ) :
    2 * integerDistance x ≤ |Real.sin (Real.pi * x)| := by
  have hd : integerDistance x = min (Int.fract x) (1 - Int.fract x) :=
    abs_sub_round_eq_min x
  by_cases hzero : integerDistance x = 0
  · simp [hzero]
  have hp : 0 < integerDistance x :=
    lt_of_le_of_ne (integerDistance_nonneg x) (Ne.symm hzero)
  have hl : integerDistance x ≤ Int.fract x := by rw [hd]; exact min_le_left _ _
  have hr : Int.fract x ≤ 1 - integerDistance x := by
    have h := min_le_right (Int.fract x) (1 - Int.fract x)
    rw [← hd] at h
    linarith
  calc
    2 * integerDistance x ≤ Real.sin (Real.pi * Int.fract x) :=
      sin_pi_mul_lower_on_middle hp hl hr
    _ ≤ |Real.sin (Real.pi * Int.fract x)| := le_abs_self _
    _ = _ := abs_sin_fract x

/-- Period-one complex phase, with the same normalization as the standard
cyclic character and the circle-method Fourier sum. -/
def phase (x : ℝ) : ℂ := Complex.exp (Complex.I * (2 * Real.pi * x : ℝ))

lemma norm_phase (x : ℝ) : ‖phase x‖ = 1 :=
  Complex.norm_exp_I_mul_ofReal _

lemma phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  unfold phase
  rw [show Complex.I * (2 * Real.pi * (x + y) : ℝ) =
      Complex.I * (2 * Real.pi * x : ℝ) + Complex.I * (2 * Real.pi * y : ℝ) by
    push_cast; ring]
  exact Complex.exp_add _ _

lemma phase_nat_mul (x : ℝ) (n : ℕ) : phase ((n : ℝ) * x) = phase x ^ n := by
  unfold phase
  rw [show Complex.I * (2 * Real.pi * ((n : ℝ) * x) : ℝ) =
      (n : ℂ) * (Complex.I * (2 * Real.pi * x : ℝ)) by push_cast; ring]
  exact Complex.exp_nat_mul _ _

/-- A capped geometric envelope with the integer frequencies accounted for
explicitly, rather than assigning an invalid reciprocal at distance zero. -/
def envelope (N : ℕ) (x : ℝ) : ℝ :=
  if integerDistance x = 0 then N else min (N : ℝ) (1 / (2 * integerDistance x))

theorem norm_sum_phase_le_envelope (x : ℝ) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, phase ((n : ℝ) * x)‖ ≤ envelope N x := by
  simp_rw [phase_nat_mul]
  have hcap := norm_geometric_sum_le_card (norm_phase x) N
  by_cases hx : integerDistance x = 0
  · simpa [envelope, hx] using hcap
  simp only [envelope, ite_eq_right hx]
  refine le_min hcap ?_
  have hd : 0 < integerDistance x :=
    lt_of_le_of_ne (integerDistance_nonneg x) (Ne.symm hx)
  have hs := two_integerDistance_le_abs_sin x
  have hspos : 0 < |Real.sin (Real.pi * x)| := by linarith
  calc
    _ ≤ 1 / |Real.sin (Real.pi * x)| :=
      norm_geometric_phase_sum_le (abs_pos.mp hspos) N
    _ ≤ 1 / (2 * integerDistance x) :=
      one_div_le_one_div_of_le (by positivity) hs

/-- Translating the integer interval and adding a constant phase preserve
the norm, so the same envelope handles every interval location. -/
theorem norm_sum_shift_phase_eq (x β t : ℝ) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, phase (x * (t + n) + β)‖ =
      ‖∑ n ∈ Finset.range N, phase ((n : ℝ) * x)‖ := by
  have he : ∀ n : ℕ, phase (x * (t + n) + β) =
      phase (x * t + β) * phase ((n : ℝ) * x) := by
    intro n
    rw [← phase_add]
    congr 1
    ring
  simp_rw [he]
  rw [← Finset.mul_sum, norm_mul, norm_phase, one_mul]

theorem norm_sum_shift_phase_le_envelope (x β t : ℝ) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, phase (x * (t + n) + β)‖ ≤ envelope N x := by
  rw [norm_sum_shift_phase_eq]
  exact norm_sum_phase_le_envelope x N

end Problem337.RealPhase

end

end OAI

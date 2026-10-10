import Mathlib

namespace OAI
noncomputable section
open Filter

namespace Problem337.DilationRecurrence

/-- An eventual dilation recurrence has a global affine barrier whenever its
linear drift fits the proposed slope. The finitely many initial values are
absorbed in one constant, without a positivity assumption on the sequence. -/
theorem exists_affine_upper_bound
    (f g : ℕ → ℝ) (d : ℕ) (hd : 2 ≤ d) (a b : ℝ) (hb : 0 ≤ b)
    (hmargin : a + b / (d : ℝ) ≤ b)
    (hrec : ∀ᶠ n : ℕ in atTop, f n ≤ g n + f (n / d))
    (hstep : ∀ᶠ n : ℕ in atTop, g n ≤ a * (n : ℝ)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n : ℕ, f n ≤ b * (n : ℝ) + B := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hrec.and hstep)
  let B : ℝ := ∑ k ∈ Finset.range (N + 1), |f k|
  have hB : 0 ≤ B := Finset.sum_nonneg (fun k _ => abs_nonneg (f k))
  refine ⟨B, hB, ?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n ≤ N
    · have hf : f n ≤ B := (le_abs_self (f n)).trans
        (Finset.single_le_sum (fun k _ => abs_nonneg (f k))
          (Finset.mem_range.mpr (by omega : n < N + 1)))
      exact hf.trans (le_add_of_nonneg_left (mul_nonneg hb (Nat.cast_nonneg n)))
    · have hn0 : 0 < n := by omega
      have hsmall : n / d < n := Nat.div_lt_self hn0 (by omega)
      have hprev := ih (n / d) hsmall
      have hpair := hN n (by omega)
      have hquot : ((n / d : ℕ) : ℝ) ≤ (n : ℝ) / d := Nat.cast_div_le
      have hscaled := mul_le_mul_of_nonneg_left hquot hb
      have hdrift := mul_le_mul_of_nonneg_right hmargin (Nat.cast_nonneg n)
      calc
        f n ≤ g n + f (n / d) := hpair.1
        _ ≤ a * (n : ℝ) + (b * ((n / d : ℕ) : ℝ) + B) :=
          add_le_add hpair.2 hprev
        _ ≤ a * (n : ℝ) + (b * ((n : ℝ) / d) + B) := by linarith
        _ = (a + b / (d : ℝ)) * (n : ℝ) + B := by ring
        _ ≤ b * (n : ℝ) + B := by linarith

/-- Any strict enlargement of an affine barrier is eventually a linear bound. -/
theorem eventually_linear_of_affine
    (f : ℕ → ℝ) (b B c : ℝ) (hbc : b < c)
    (hbound : ∀ n : ℕ, f n ≤ b * (n : ℝ) + B) :
    ∀ᶠ n : ℕ in atTop, f n ≤ c * (n : ℝ) := by
  have hgrowth : ∀ᶠ n : ℕ in atTop, B / (c - b) ≤ (n : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      (eventually_ge_atTop (B / (c - b)))
  filter_upwards [hgrowth] with n hn
  have hB : B ≤ (n : ℝ) * (c - b) := (div_le_iff₀ (sub_pos.mpr hbc)).mp hn
  have hf := hbound n
  nlinarith

/-- A fixed strict slack in the slope removes the initial-value constant. -/
theorem eventually_upper_bound
    (f g : ℕ → ℝ) (d : ℕ) (hd : 2 ≤ d) (a b c : ℝ) (hb : 0 ≤ b)
    (hmargin : a + b / (d : ℝ) ≤ b) (hbc : b < c)
    (hrec : ∀ᶠ n : ℕ in atTop, f n ≤ g n + f (n / d))
    (hstep : ∀ᶠ n : ℕ in atTop, g n ≤ a * (n : ℝ)) :
    ∀ᶠ n : ℕ in atTop, f n ≤ c * (n : ℝ) := by
  obtain ⟨B, _, hB⟩ := exists_affine_upper_bound f g d hd a b hb hmargin hrec hstep
  exact eventually_linear_of_affine f b B c hbc hB

/-- The asymptotic slope of the forcing term gives the geometric-series slope
for the recursively bounded sequence. This needs a limit only for `g`, not
for `f`, and handles the natural-number rounding in `n / d` exactly. -/
theorem eventually_upper_of_ratio_limit
    (f g : ℕ → ℝ) (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : 0 ≤ c)
    (hrec : ∀ᶠ n : ℕ in atTop, f n ≤ g n + f (n / d))
    (hlim : Tendsto (fun n : ℕ => g n / (n : ℝ)) atTop (nhds c))
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      f n ≤ (c / (1 - 1 / (d : ℝ)) + ε) * (n : ℝ) := by
  have hdR : (1 : ℝ) < d := by exact_mod_cast (show 1 < d by omega)
  have hd0 : (0 : ℝ) < d := by linarith
  let ρ : ℝ := 1 - 1 / (d : ℝ)
  have hρ : 0 < ρ := by
    dsimp [ρ]
    exact sub_pos.mpr ((div_lt_one hd0).mpr hdR)
  let b : ℝ := c / ρ + ε / 2
  let a : ℝ := b * ρ
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hca : c < a := by
    dsimp [a, b]
    rw [add_mul, div_mul_cancel₀ c hρ.ne']
    linarith [mul_pos (show 0 < ε / 2 by positivity) hρ]
  have hmargin : a + b / (d : ℝ) ≤ b := by
    dsimp [a, ρ]
    exact le_of_eq (by ring)
  have hbc : b < c / (1 - 1 / (d : ℝ)) + ε := by
    dsimp [b, ρ]
    linarith
  have hstep : ∀ᶠ n : ℕ in atTop, g n ≤ a * (n : ℝ) := by
    filter_upwards [hlim.eventually (gt_mem_nhds hca), eventually_ge_atTop (1 : ℕ)]
      with n hn hn1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    exact ((div_lt_iff₀ hn0).mp hn).le
  exact eventually_upper_bound f g d hd a b
    (c / (1 - 1 / (d : ℝ)) + ε) hb hmargin hbc hrec hstep

end Problem337.DilationRecurrence

end

end OAI

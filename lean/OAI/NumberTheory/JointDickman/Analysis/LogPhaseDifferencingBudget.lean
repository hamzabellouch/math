import OAI.NumberTheory.JointDickman.Amplification.IteratedDifferencing

namespace OAI
noncomputable section
open scoped BigOperators Topology
open Filter

namespace JointDickman
open Problem337

/-- The natural cutoff in van der Corput differencing preserves a power saving.
All size conditions here are scalar and hold eventually for fixed parameters. -/
theorem logarithmic_differencing_budget (r N : ℕ) (U α C : ℝ)
    (hU : 1 ≤ U) (_hα : 0 < α) (hα1 : α ≤ 1) (hC : 0 ≤ C)
    (hcut : 4 ≤ U ^ α)
    (herror : C * U ^ (-(1 : ℝ) / 5) ≤ 4 * U ^ (-α))
    (hUN : U ≤ (N : ℝ)) (hNU : (N : ℝ) ≤ 3 * U)
    (a : ℤ → ℂ)
    (hsupport : ∀ n : ℤ, n ∉ Finset.Icc (1 : ℤ) N → a n = 0)
    (hnorm : ∀ n : ℤ, ‖a n‖ ≤ 1)
    (hterminal : ∀ hs : List ℤ, hs.length = r →
      (∀ h ∈ hs, 0 < h ∧ h < (Nat.floor (U ^ α) : ℤ)) →
      ‖∑ n ∈ Finset.Icc (1 : ℤ) N, iteratedCorrelation a hs n‖ ≤
        C * U ^ ((4 : ℝ) / 5)) :
    ‖∑ n ∈ Finset.Icc (1 : ℤ) N, a n‖ ≤
      36 * U ^ (1 - α / (2 : ℝ) ^ r) := by
  let H : ℕ := Nat.floor (U ^ α)
  have hUpos : 0 < U := by linarith
  have hNpos : 0 < (N : ℝ) := hUpos.trans_le hUN
  have hp : 0 < U ^ α := Real.rpow_pos_of_pos hUpos α
  have hH : 1 ≤ H := (Nat.le_floor_iff hp.le).2 (by norm_num; linarith)
  have hHR : 0 < (H : ℝ) := by exact_mod_cast (show 0 < H by omega)
  have hHle : (H : ℝ) ≤ U ^ α := Nat.floor_le hp.le
  have hHN : H ≤ N := by
    have hpU : U ^ α ≤ U := by
      simpa using Real.rpow_le_rpow_of_exponent_le hU hα1
    exact_mod_cast hHle.trans (hpU.trans hUN)
  have hhalf : U ^ α ≤ 2 * (H : ℝ) := by
    have hfloor : U ^ α < (H : ℝ) + 1 := Nat.lt_floor_add_one _
    have hone : (1 : ℝ) ≤ H := by exact_mod_cast hH
    linarith
  have hinv : U ^ (-α) = 1 / U ^ α := by rw [Real.rpow_neg hUpos.le, one_div]
  have hHerror : 2 / (H : ℝ) ≤ 4 * U ^ (-α) := by
    rw [hinv, mul_one_div]
    apply (div_le_div_iff₀ hHR hp).2
    nlinarith
  have heps : 0 < 4 * U ^ (-α) := by positivity
  have heps1 : 4 * U ^ (-α) ≤ 1 := by
    rw [hinv, mul_one_div]
    exact (div_le_one hp).2 hcut
  have hterminal' : ∀ hs : List ℤ, hs.length = r →
      (∀ h ∈ hs, 0 < h ∧ h < H) →
      ‖∑ n ∈ Finset.Icc (1 : ℤ) N, iteratedCorrelation a hs n‖ / (N : ℝ) ≤
        4 * U ^ (-α) := by
    intro hs hlen hsteps
    calc
      ‖∑ n ∈ Finset.Icc (1 : ℤ) N, iteratedCorrelation a hs n‖ / (N : ℝ) ≤
          (C * U ^ ((4 : ℝ) / 5)) / (N : ℝ) :=
        div_le_div_of_nonneg_right (hterminal hs hlen hsteps) hNpos.le
      _ ≤ (C * U ^ ((4 : ℝ) / 5)) / U :=
        div_le_div_of_nonneg_left (by positivity) hUpos hUN
      _ = C * U ^ (-(1 : ℝ) / 5) := by
        have heq : U ^ ((4 : ℝ) / 5) / U = U ^ (-(1 : ℝ) / 5) := by
          calc
            U ^ ((4 : ℝ) / 5) / U = U ^ ((4 : ℝ) / 5) / U ^ (1 : ℝ) := by rw [Real.rpow_one]
            _ = U ^ ((4 : ℝ) / 5 - 1) := (Real.rpow_sub hUpos _ _).symm
            _ = U ^ (-(1 : ℝ) / 5) := by norm_num
        rw [mul_div_assoc, heq]
      _ ≤ 4 * U ^ (-α) := herror
  have hnormsum := iterated_differencing_power_bound r N H hH hHN
    (4 * U ^ (-α)) heps heps1 hHerror a hsupport hnorm hterminal'
  have hexp : 0 < 1 / (2 : ℝ) ^ r := by positivity
  have hexp1 : 1 / (2 : ℝ) ^ r ≤ 1 := by
    exact (div_le_one (by positivity)).2 (one_le_pow₀ (by norm_num))
  have hfour : (4 : ℝ) ^ (1 / (2 : ℝ) ^ r) ≤ 4 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4) hexp1
  have hpower : (4 * U ^ (-α)) ^ (1 / (2 : ℝ) ^ r) ≤
      4 * U ^ (-α / (2 : ℝ) ^ r) := by
    rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hUpos.le]
    have heq : -α * (1 / (2 : ℝ) ^ r) = -α / (2 : ℝ) ^ r := by ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right hfour (by positivity)
  have hraw := (div_le_iff₀ hNpos).1 hnormsum
  calc
    ‖∑ n ∈ Finset.Icc (1 : ℤ) N, a n‖ ≤
        (3 * (4 * U ^ (-α)) ^ (1 / (2 : ℝ) ^ r)) * (N : ℝ) := hraw
    _ ≤ (3 * (4 * U ^ (-α / (2 : ℝ) ^ r))) * (3 * U) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hpower (by norm_num))
        hNU hNpos.le (by positivity)
    _ = 36 * U ^ (1 - α / (2 : ℝ) ^ r) := by
      rw [sub_eq_add_neg, Real.rpow_add hUpos, Real.rpow_one]
      simp only [neg_div]
      ring

/-- For fixed parameters the scalar cutoff conditions are automatic. -/
theorem logarithmic_differencing_budget_eventually (r : ℕ) (α C : ℝ)
    (hα : 0 < α) (hαsmall : α < (1 : ℝ) / 5) (hC : 0 ≤ C) :
    ∀ᶠ (U : ℝ) in atTop, ∀ N : ℕ,
      U ≤ (N : ℝ) → (N : ℝ) ≤ 3 * U → ∀ a : ℤ → ℂ,
      (∀ n : ℤ, n ∉ Finset.Icc (1 : ℤ) N → a n = 0) →
      (∀ n : ℤ, ‖a n‖ ≤ 1) →
      (∀ hs : List ℤ, hs.length = r →
        (∀ h ∈ hs, 0 < h ∧ h < (Nat.floor (U ^ α) : ℤ)) →
        ‖∑ n ∈ Finset.Icc (1 : ℤ) N, iteratedCorrelation a hs n‖ ≤
          C * U ^ ((4 : ℝ) / 5)) →
      ‖∑ n ∈ Finset.Icc (1 : ℤ) N, a n‖ ≤
        36 * U ^ (1 - α / (2 : ℝ) ^ r) := by
  have hcut := (tendsto_rpow_atTop hα).eventually_ge_atTop (4 : ℝ)
  have hconst := (tendsto_rpow_atTop
    (show 0 < (1 : ℝ) / 5 - α by linarith)).eventually_ge_atTop C
  filter_upwards [eventually_ge_atTop (1 : ℝ), hcut, hconst] with U hU hcut hconst
  have hUpos : 0 < U := by linarith
  have herror : C * U ^ (-(1 : ℝ) / 5) ≤ 4 * U ^ (-α) := by
    calc
      C * U ^ (-(1 : ℝ) / 5) ≤
          U ^ ((1 : ℝ) / 5 - α) * U ^ (-(1 : ℝ) / 5) :=
        mul_le_mul_of_nonneg_right hconst (by positivity)
      _ = U ^ (-α) := by
        rw [← Real.rpow_add hUpos]
        congr 1
        ring
      _ ≤ 4 * U ^ (-α) := by
        have : 0 ≤ U ^ (-α) := Real.rpow_nonneg hUpos.le _
        linarith
  intro N hUN hNU a hsupport hnorm hterminal
  exact logarithmic_differencing_budget r N U α C hU hα (by linarith)
    hC hcut herror hUN hNU a hsupport hnorm hterminal

end JointDickman

end

end OAI

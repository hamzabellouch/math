import OAI.NumberTheory.TwoPointCorrelations.HalaszPrimeCounting
import OAI.NumberTheory.TwoPointCorrelations.HalaszFrequencyRows

namespace OAI

/-! Prime logarithmic windows have bounded von Mangoldt mass at frequency
resolution `1/T`, once the primes are at least `T²`. This is the precise
short-interval sieve consequence used in the Halasz mean-square argument. -/

namespace TwoPointCorrelations

open Finset
open scoped BigOperators

lemma halasz_exp_reciprocal_bound {T : ℝ} (hT : 2 ≤ T) :
    Real.exp (1 / T) ≤ 1 + 2 / T := by
  have hTp : 0 < T := by linarith
  have hinv : 0 ≤ 1 / T := by positivity
  have hi1 : 1 / T ≤ 1 := (div_le_one hTp).mpr (by linarith)
  have he := Real.abs_exp_sub_one_le (x := 1 / T) (by rwa [abs_of_nonneg hinv])
  rw [abs_of_nonneg hinv] at he
  have hh := (le_abs_self (Real.exp (1 / T) - 1)).trans he
  simp only [div_eq_mul_inv, one_mul] at hh ⊢
  linarith

lemma halasz_prime_window_log_length {T u : ℝ} (hT : 2 ≤ T)
    (hscale : T ^ 2 ≤ Real.exp u) :
    u / 2 ≤ Real.log (4 * Real.exp u / T) := by
  have hTp : 0 < T := by linarith
  have hl := Real.log_le_log (sq_pos_of_pos hTp) hscale
  rw [Real.log_pow, Real.log_exp] at hl
  norm_num at hl
  rw [Real.log_div (by positivity) hTp.ne', Real.log_mul (by norm_num) (Real.exp_pos _).ne',
    Real.log_exp]
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  linarith

/-- A bounded interval of logarithmic length `1/T` contains `O(1/T)`
weighted prime mass, uniformly over its position above `T²`. -/
theorem halasz_prime_log_window_bound : ∃ C B : ℝ, 0 < C ∧ 2 ≤ B ∧
    ∀ (T u : ℝ) (P : Finset ℕ), B ≤ T → 1 ≤ u → T ^ 2 ≤ Real.exp u →
      (∀ p ∈ P, p.Prime ∧ u ≤ Real.log (p : ℝ) ∧ Real.log (p : ℝ) ≤ u + 1 / T) →
      (∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ)) ≤ C / T := by
  obtain ⟨C, B, hC, hB, hcount⟩ := halasz_prime_interval_bound
  refine ⟨16 * C, max 2 B, by positivity, le_max_left _ _, ?_⟩
  intro T u P hBT hu hscale hP
  have hT : 2 ≤ T := (le_max_left _ _).trans hBT
  have hTB : B ≤ T := (le_max_right _ _).trans hBT
  have hTp : 0 < T := by linarith
  have hu0 : 0 < u := by linarith
  have he : 0 < Real.exp u := Real.exp_pos _
  let H := 4 * Real.exp u / T
  have hHT : T ≤ H := by
    dsimp [H]
    apply (le_div_iff₀ hTp).mpr
    nlinarith
  have hlog : u / 2 ≤ Real.log H := halasz_prime_window_log_length hT hscale
  have hlogp : 0 < Real.log H := lt_of_lt_of_le (by positivity) hlog
  have hupper : Real.exp (u + 1 / T) ≤ Real.exp u + 2 * Real.exp u / T := by
    rw [Real.exp_add]
    have hh := mul_le_mul_of_nonneg_left (halasz_exp_reciprocal_bound hT) he.le
    calc
      _ ≤ Real.exp u * (1 + 2 / T) := hh
      _ = _ := by ring
  have hp_bounds (p : ℕ) (hp : p ∈ P) :
      Real.exp u ≤ (p : ℝ) ∧ (p : ℝ) ≤ Real.exp (u + 1 / T) := by
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hP p hp).1.pos
    constructor
    · simpa only [Real.exp_log hp0] using Real.exp_le_exp.mpr (hP p hp).2.1
    · simpa only [Real.exp_log hp0] using Real.exp_le_exp.mpr (hP p hp).2.2
  have hcard : (P.card : ℝ) ≤ C * H / Real.log H := by
    apply hcount (Real.exp u - Real.exp u / T) H P (hTB.trans hHT)
    intro p hp
    have hb := hp_bounds p hp
    refine ⟨(hP p hp).1, ?_, ?_⟩
    · have hdiv : 0 < Real.exp u / T := div_pos he hTp
      linarith
    · dsimp [H]
      have hh := hb.2.trans hupper
      simp only [div_eq_mul_inv] at hh ⊢
      nlinarith [inv_pos.mpr hTp]
  have hweight : (∑ p ∈ P, Real.log (p : ℝ) / (p : ℝ)) ≤
      (P.card : ℝ) * ((u + 1 / T) / Real.exp u) := by
    calc
      _ ≤ ∑ _p ∈ P, (u + 1 / T) / Real.exp u := by
        apply sum_le_sum
        intro p hp
        have hp0 : (0 : ℝ) < p := by exact_mod_cast (hP p hp).1.pos
        calc
          _ ≤ (u + 1 / T) / (p : ℝ) :=
            div_le_div_of_nonneg_right (hP p hp).2.2 hp0.le
          _ ≤ (u + 1 / T) / Real.exp u :=
            div_le_div_of_nonneg_left (by positivity) he (hp_bounds p hp).1
      _ = _ := by simp
  have hiu : 1 / T ≤ u := by
    have hi1 : 1 / T ≤ 1 := (div_le_one hTp).mpr (by linarith)
    exact hi1.trans hu
  have hratio : (u + 1 / T) / Real.log H ≤ 4 := by
    apply (div_le_iff₀ hlogp).mpr
    linarith
  calc
    _ ≤ (P.card : ℝ) * ((u + 1 / T) / Real.exp u) := hweight
    _ ≤ (C * H / Real.log H) * ((u + 1 / T) / Real.exp u) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = (4 * C / T) * ((u + 1 / T) / Real.log H) := by dsimp [H]; field_simp
    _ ≤ (4 * C / T) * 4 := mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = 16 * C / T := by ring


/-- The same local mass bound for every window, with the lower cutoff imposed
on the prime set instead of on the window's left endpoint. -/
theorem halasz_prime_windows_above_square : ∃ C B : ℝ, 0 < C ∧ 2 ≤ B ∧
    ∀ (T : ℝ) (P : Finset ℕ), B ≤ T →
      (∀ p ∈ P, p.Prime ∧ T ^ 2 ≤ (p : ℝ)) → ∀ u : ℝ,
      (∑ p ∈ P.filter (fun (p : ℕ) =>
        u ≤ Real.log (p : ℝ) ∧ Real.log (p : ℝ) ≤ u + 1 / T),
          Real.log (p : ℝ) / (p : ℝ)) ≤ C / T := by
  classical
  obtain ⟨C, B, hC, hB, hwindow⟩ := halasz_prime_log_window_bound
  refine ⟨C, B, hC, hB, ?_⟩
  intro T P hBT hP u
  have hT : 2 ≤ T := hB.trans hBT
  have hTp : 0 < T := by linarith
  have hi : 1 / T ≤ 1 / 2 := by
    exact one_div_le_one_div_of_le (by norm_num) hT
  have hl := Real.one_sub_inv_le_log_of_pos hTp
  have hl1 : 1 ≤ 2 * Real.log T := by
    rw [← one_div] at hl
    linarith
  let v := max u (2 * Real.log T)
  have hv : 1 ≤ v := hl1.trans (le_max_right _ _)
  have hscale : T ^ 2 ≤ Real.exp v := by
    calc
      T ^ 2 = Real.exp (Real.log (T ^ 2)) := (Real.exp_log (sq_pos_of_pos hTp)).symm
      _ = Real.exp (2 * Real.log T) := by rw [Real.log_pow]; norm_num
      _ ≤ Real.exp v := Real.exp_le_exp.mpr (le_max_right _ _)
  apply hwindow T v _ hBT hv hscale
  intro p hp
  obtain ⟨hpP, hlo, hhi⟩ := mem_filter.mp hp
  have hlog := Real.log_le_log (sq_pos_of_pos hTp) (hP p hpP).2
  rw [Real.log_pow] at hlog
  refine ⟨(hP p hpP).1, max_le hlo hlog, ?_⟩
  exact hhi.trans (add_le_add (le_max_left _ _) le_rfl)

end TwoPointCorrelations

end OAI

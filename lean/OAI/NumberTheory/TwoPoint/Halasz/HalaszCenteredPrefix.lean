import OAI.NumberTheory.TwoPoint.Halasz.HalaszPhaseTranslation
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

namespace OAI

/-! Centered prefix cancellation from the proved general Halasz theorem.
The lower bound on distance stays at the original large cutoff. -/

namespace TwoPointCorrelations

open Finset Filter
open scoped ComplexConjugate

lemma halasz_distance_monotone (F : ℕ → ℂ) (hF : OneBounded F) (t : ℝ) :
    Monotone (fun N => squaredDistance F (mrtArchimedeanTwist t) N) := by
  intro n N hnN
  unfold squaredDistance
  apply sum_le_sum_of_subset_of_nonneg (halasz_prime_cutoff_subset hnN)
  intro p hp _
  have hp0 := (mem_filter.mp hp).2.pos
  have hn : ‖F p * conj (mrtArchimedeanTwist t p)‖ ≤ 1 := by
    simpa only [norm_mul, Complex.norm_conj, mrtArchimedeanTwist_norm, mul_one] using hF p hp0
  exact div_nonneg (sub_nonneg.mpr ((Complex.re_le_norm _).trans hn)) (Nat.cast_nonneg p)

lemma halasz_decay_half (M : ℝ) :
    (M + 1) * Real.exp (-M) ≤ 2 * Real.exp (-M / 2) := by
  have hh := Real.add_one_le_exp (M / 2)
  have hm := mul_le_mul_of_nonneg_right hh (Real.exp_pos (-M)).le
  have he : Real.exp (M / 2) * Real.exp (-M) = Real.exp (-M / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at hm
  nlinarith [Real.exp_pos (-M)]

/-- Uniform centered prefixes on a dyadic interval. The pretentious
lower bound is imposed only at the original cutoff X, not at smaller
scales or on a modified multiplicative function. -/
theorem halasz_centered_prefix : ∃ C : ℝ, 0 < C ∧
    ∀ᶠ N : ℕ in atTop, ∀ X : ℕ, N ≤ 2 * X → X ≤ N ^ 3 →
      ∀ (F : ℕ → ℂ), F 1 = 1 → Multiplicative F → OneBounded F →
      ∀ (t T M : ℝ), 0 ≤ M → |t| + Real.log (2 * N : ℕ) ^ 8 ≤ T →
      (∀ v : ℝ, |v| ≤ T → M ≤ squaredDistance F (mrtArchimedeanTwist v) X) →
      ∀ k ∈ Icc N (2 * N),
        ‖halaszPhaseMean (halaszTwistedFunction F t) 0 k‖ ≤
          C * (Real.exp (-M / 2) + Real.log (Real.log N) / Real.log N) * k := by
  obtain ⟨C, X₀, hC, hmean⟩ := halasz_general_twisted_mean
  obtain ⟨K, hK, hcut⟩ := halasz_distance_cutoff_loss
  let D := 2 * C * Real.exp K + C
  refine ⟨D, by dsimp [D]; positivity, ?_⟩
  have hNX : ∀ᶠ N : ℕ in atTop, X₀ ≤ (N : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop X₀)
  have hNL : ∀ᶠ N : ℕ in atTop, Real.exp 1 ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (Real.exp 1))
  filter_upwards [hNX, hNL, eventually_ge_atTop 2] with N hNX hNL hN2
  intro X _hNX₂ hXN F hF1 hFm hFb t T M hM hT hdist k hk
  have hNk : N ≤ k := (mem_Icc.mp hk).1
  have hk₂ : k ≤ 2 * N := (mem_Icc.mp hk).2
  have hk2 : 2 ≤ k := hN2.trans hNk
  have hXk : X ≤ k ^ 3 := hXN.trans (by gcongr)
  have hlogk : Real.log (N : ℝ) ≤ Real.log k := Real.log_le_log
    (by exact_mod_cast (show 0 < N by omega)) (by exact_mod_cast hNk)
  have hlog2k : Real.log (k : ℝ) ≤ Real.log (2 * N : ℕ) := Real.log_le_log
    (by exact_mod_cast (show 0 < k by omega)) (by exact_mod_cast hk₂)
  have hl0 : 0 ≤ Real.log (k : ℝ) := (Real.exp_pos 1).le.trans (hNL.trans hlogk)
  have hheight : |t| + Real.log (k : ℝ) ^ 8 ≤ T := by
    have hp := pow_le_pow_left₀ hl0 hlog2k 8
    linarith
  let M' := max 0 (M - K)
  have hd : ∀ v : ℝ, |v| ≤ T → M' ≤ squaredDistance F (mrtArchimedeanTwist v) k := by
    intro v hv
    apply max_le
    · exact halasz_distance_nonneg F hFb k v
    · have hd := hdist v hv
      by_cases hkX : k ≤ X
      · have hh := hcut F hFb k X hk2 hkX hXk v
        linarith
      · have hh := halasz_distance_monotone F hFb v (by omega : X ≤ k)
        linarith
  have hm := hmean k (hNX.trans (by exact_mod_cast hNk)) F hF1 hFm hFb
    t T M' (le_max_left _ _) hheight hd
  have he := (halasz_decay_shift hM hK).trans
    (mul_le_mul_of_nonneg_left (halasz_decay_half M) (Real.exp_pos K).le)
  have hR := Real.log_div_self_antitoneOn hNL (hNL.trans hlogk) hlogk
  have hRN : 0 ≤ Real.log (Real.log (N : ℝ)) / Real.log N := by
    apply div_nonneg
    · apply Real.log_nonneg
      exact (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1)).trans hNL
    · exact (Real.exp_pos 1).le.trans hNL
  have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hbound : ((M' + 1) * Real.exp (-M') + Real.log (Real.log k) / Real.log k) ≤
      2 * Real.exp K * Real.exp (-M / 2) + Real.log (Real.log N) / Real.log N := by
    dsimp [M']
    nlinarith
  have hp := mul_le_mul_of_nonneg_left hbound (mul_nonneg hC.le hk0)
  have hf : ‖halaszPhaseMean (halaszTwistedFunction F t) 0 k‖ =
      ‖∑ n ∈ Icc 1 k, F n * star (mrtArchimedeanTwist t n)‖ := by
    simp [halaszPhaseMean, halaszPowerPhase, halaszTwistedFunction]
  rw [hf]
  apply hm.trans
  apply hp.trans
  have hfinal : C * (2 * Real.exp K * Real.exp (-M / 2) +
      Real.log (Real.log N) / Real.log N) ≤
      D * (Real.exp (-M / 2) + Real.log (Real.log N) / Real.log N) := by
    dsimp [D]
    nlinarith [mul_nonneg hC.le (Real.exp_pos (-M / 2)).le,
      mul_nonneg (mul_nonneg hC.le (Real.exp_pos K).le) hRN]
  calc
    _ = (C * (2 * Real.exp K * Real.exp (-M / 2) +
        Real.log (Real.log N) / Real.log N)) * k := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hfinal hk0

end TwoPointCorrelations

end OAI

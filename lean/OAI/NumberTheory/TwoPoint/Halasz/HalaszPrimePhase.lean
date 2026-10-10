import OAI.NumberTheory.TwoPoint.Halasz.HalaszPrimeTheta
import OAI.NumberTheory.TwoPoint.Bounds.CosineLogIntegral

namespace OAI

/-! Prime phase sums on a finite real interval. The prime-number error
retains its exponentially small lower-endpoint factor and its explicit
frequency dependence. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

lemma halasz_prime_band_filter (a b : ℝ) :
    mrtPrimeBand a b = (Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime := by
  ext p
  simp only [mrtPrimeBand, sievePrimesUpTo, mem_sdiff, mem_filter, mem_Iic, mem_Ioc]
  by_cases hp : p.Prime <;> simp only [hp, and_true, and_false, not_false_eq_true]
  omega

lemma halasz_prime_phase_sum (a b t : ℝ) :
    (∑ p ∈ mrtPrimeBand a b, (1 - Real.cos (t * Real.log p)) / p) =
      ∑ n ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, oscillatoryReciprocalLog t n * halaszPrimeLogWeight n := by
  rw [halasz_prime_band_filter, sum_filter]
  apply sum_congr rfl
  intro n _
  by_cases hp : n.Prime
  · rw [ite_eq_left hp, halaszPrimeLogWeight, ite_eq_left hp]
    have hl : Real.log (n : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
    unfold oscillatoryReciprocalLog reciprocalLog
    field_simp
  · simp [halaszPrimeLogWeight, hp]

theorem ModFiveThetaInput.halasz_prime_phase_error (hP : ModFiveThetaInput) :
    ∃ c K : ℝ, 0 < c ∧ 0 ≤ K ∧ ∀ a b t : ℝ, Real.exp 1 ≤ a → a ≤ b →
      |(∑ p ∈ mrtPrimeBand a b, (1 - Real.cos (t * Real.log p)) / p) -
        (∫ x in a..b, oscillatoryReciprocalLog t x)| ≤
          (8 + |t|) * K * Real.exp (-c * Real.sqrt (Real.log a)) / Real.log a := by
  obtain ⟨c, K, hc, hK, htail⟩ := hP.halasz_prime_tail_error
  refine ⟨c, K, hc, hK, ?_⟩
  intro a b t ha hab
  have ha2 : 2 ≤ a := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hh := halasz_oscillatory_theta_error halaszPrimeLogWeight 1
    (K * Real.exp (-c * Real.sqrt (Real.log a))) a b t (by positivity) ha hab
    (fun x hx => by simpa only [one_mul] using htail a x ha2 hx.1)
  rw [← halasz_prime_phase_sum, one_mul] at hh
  convert hh using 1
  ring

lemma halasz_log_phase_substitution (a b t : ℝ) (ha : 1 < a) (hab : a ≤ b) :
    (∫ x in a..b, oscillatoryReciprocalLog t x) =
      ∫ y in Real.log a..Real.log b, (1 - Real.cos (t * y)) / y := by
  have hxp (x : ℝ) (hx : x ∈ Set.uIcc a b) : 0 < x := by
    rw [Set.uIcc_of_le hab] at hx
    exact (zero_lt_one.trans ha).trans_le hx.1
  have hd (x : ℝ) (hx : x ∈ Set.uIcc a b) := Real.hasDerivAt_log (hxp x hx).ne'
  have hc : ContinuousOn (fun x : ℝ => x⁻¹) (Set.uIcc a b) :=
    continuousOn_id.inv₀ (fun x hx => (hxp x hx).ne')
  have hg : ContinuousOn (fun y : ℝ => (1 - Real.cos (t * y)) / y)
      (Real.log '' Set.uIcc a b) := by
    rintro y ⟨x, hx, rfl⟩
    have hx' : a ≤ x := by rw [Set.uIcc_of_le hab] at hx; exact hx.1
    have hn : Real.log x ≠ 0 := (Real.log_pos (ha.trans_le hx')).ne'
    exact (by fun_prop (disch := assumption) :
      ContinuousAt (fun y : ℝ => (1 - Real.cos (t * y)) / y) (Real.log x)).continuousWithinAt
  rw [← intervalIntegral.integral_comp_mul_deriv' hd hc hg]
  apply intervalIntegral.integral_congr
  intro x _
  unfold oscillatoryReciprocalLog reciprocalLog
  simp only [Function.comp_def, div_eq_mul_inv]
  ring

lemma halasz_log_phase_lower (a b t : ℝ) (ha : 1 < a) (hab : a ≤ b)
    (ht : 1 ≤ |t| * Real.log a) :
    Real.log (Real.log b / Real.log a) - 3 ≤
      ∫ x in a..b, oscillatoryReciprocalLog t x := by
  have hla : 0 < Real.log a := Real.log_pos ha
  have hlab : Real.log a ≤ Real.log b := Real.log_le_log (zero_lt_one.trans ha) hab
  have hlb : 0 < Real.log b := hla.trans_le hlab
  have ht0 : 0 < |t| := by
    by_contra hn
    have hz : |t| = 0 := le_antisymm (le_of_not_gt hn) (abs_nonneg t)
    rw [hz, zero_mul] at ht
    norm_num at ht
  have hcos (y : ℝ) : Real.cos (|t| * y) = Real.cos (t * y) := by
    rcases le_or_gt 0 t with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, neg_mul, Real.cos_neg]
  have htail := (abs_le.mp (cosine_log_tail |t| (Real.log a) (Real.log b)
    ht0 hla hlab ht)).2
  simp_rw [hcos] at htail
  rw [halasz_log_phase_substitution a b t ha hab]
  have hi₁ : IntervalIntegrable (fun y : ℝ => 1 / y) volume (Real.log a) (Real.log b) := by
    apply ContinuousOn.intervalIntegrable_of_Icc hlab
    intro y hy
    exact (continuousAt_const.div continuousAt_id (hla.trans_le hy.1).ne').continuousWithinAt
  have hi₂ : IntervalIntegrable (fun y : ℝ => Real.cos (t * y) / y)
      volume (Real.log a) (Real.log b) := by
    apply ContinuousOn.intervalIntegrable_of_Icc hlab
    intro y hy
    have hn := (hla.trans_le hy.1).ne'
    exact (by fun_prop (disch := assumption) :
      ContinuousAt (fun y : ℝ => Real.cos (t * y) / y) y).continuousWithinAt
  have he : (∫ y in Real.log a..Real.log b, (1 - Real.cos (t * y)) / y) =
      Real.log (Real.log b / Real.log a) -
        ∫ y in Real.log a..Real.log b, Real.cos (t * y) / y := by
    rw [← integral_one_div_of_pos hla hlb, ← intervalIntegral.integral_sub hi₁ hi₂]
    apply intervalIntegral.integral_congr
    intro y _
    ring
  rw [he]
  linarith

lemma halasz_prime_band_tail (N : ℕ) (Y : ℝ) (hY : 0 ≤ Y) :
    mrtPrimeBand Y N = (primesUpTo N).filter (fun p : ℕ => Y < (p : ℝ)) := by
  rw [halasz_prime_band_filter]
  ext p
  simp only [mem_filter, mem_Ioc, Nat.floor_natCast, primesUpTo, mem_range]
  rw [Nat.floor_lt hY]
  rw [Nat.lt_succ_iff]
  tauto

theorem ModFiveThetaInput.halasz_prime_phase_lower (hP : ModFiveThetaInput) :
    ∃ c K : ℝ, 0 < c ∧ 0 ≤ K ∧ ∀ a b t : ℝ,
      Real.exp 1 ≤ a → a ≤ b → 1 ≤ |t| * Real.log a →
      Real.log (Real.log b / Real.log a) - 3 -
          (8 + |t|) * K * Real.exp (-c * Real.sqrt (Real.log a)) / Real.log a ≤
        ∑ p ∈ mrtPrimeBand a b, (1 - Real.cos (t * Real.log p)) / p := by
  obtain ⟨c, K, hc, hK, hh⟩ := hP.halasz_prime_phase_error
  refine ⟨c, K, hc, hK, ?_⟩
  intro a b t ha hab ht
  have ha1 : 1 < a := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans_le ha
  have hi := halasz_log_phase_lower a b t ha1 hab ht
  have he := (abs_le.mp (hh a b t ha hab)).1
  linarith

/-- A finite quantitative repulsion bound, retaining the actual PNT error. -/
theorem ModFiveThetaInput.halasz_masked_phase_lower (hP : ModFiveThetaInput) :
    ∃ c K : ℝ, 0 < c ∧ 0 ≤ K ∧ ∀ (F : ℕ → ℂ), OneBounded F →
      ∀ (Q : Finset ℕ) (N : ℕ) (Y t t₁ : ℝ),
      Real.exp 1 ≤ Y → Y ≤ N → 1 ≤ |t - t₁| * Real.log Y →
      squaredDistance F (mrtArchimedeanTwist t₁) N ≤
        squaredDistance F (mrtArchimedeanTwist t) N →
      (Real.log (Real.log N / Real.log Y) - 3 -
        (8 + |t - t₁|) * K * Real.exp (-c * Real.sqrt (Real.log Y)) / Real.log Y) / 8 ≤
          squaredDistance (mrtMissingCoefficient F Q) (mrtArchimedeanTwist t) N := by
  obtain ⟨c, K, hc, hK, hh⟩ := hP.halasz_prime_phase_lower
  refine ⟨c, K, hc, hK, ?_⟩
  intro F hF Q N Y t t₁ hY hYN ht hmin
  have hY0 : 0 ≤ Y := (Real.exp_pos 1).le.trans hY
  have hphase := hh Y N (t - t₁) hY hYN ht
  rw [halasz_prime_band_tail N Y hY0] at hphase
  have hcos := halasz_prime_cosine_defect N Y (t - t₁)
  have hdist := halasz_masked_cosine_tail_lower F hF Q N Y t t₁ hmin
  nlinarith

end TwoPointCorrelations

end OAI

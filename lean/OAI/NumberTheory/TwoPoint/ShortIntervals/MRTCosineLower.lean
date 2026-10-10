import OAI.NumberTheory.TwoPoint.Halasz.HalaszPrimePhase
import OAI.NumberTheory.TwoPoint.Fourier.ModFivePrimeNumberTheorem

namespace OAI

/-! A lower bound for the logarithmic cosine integral uniform even at
frequency zero, and the resulting one-sided prime cosine estimate. -/

namespace TwoPointCorrelations

open MeasureTheory Finset
open scoped Classical

lemma mrt_cosine_log_integrable (t a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun y : ℝ => Real.cos (t * y) / y) volume a b := by
  apply ContinuousOn.intervalIntegrable_of_Icc hab
  intro y hy
  have hn := (ha.trans_le hy.1).ne'
  exact (by fun_prop (disch := assumption) :
    ContinuousAt (fun y : ℝ => Real.cos (t * y) / y) y).continuousWithinAt

lemma mrt_cosine_log_nonneg (t a b : ℝ) (ht : 0 ≤ t) (ha : 0 < a)
    (hab : a ≤ b) (hb : t * b ≤ 1) :
    0 ≤ ∫ y in a..b, Real.cos (t * y) / y := by
  apply intervalIntegral.integral_nonneg hab
  intro y hy
  have hy0 : 0 < y := ha.trans_le hy.1
  have hty : 0 ≤ t * y := mul_nonneg ht hy0.le
  have hty1 : t * y ≤ 1 := (mul_le_mul_of_nonneg_left hy.2 ht).trans hb
  apply div_nonneg _ hy0.le
  apply Real.cos_nonneg_of_mem_Icc
  constructor <;> linarith [Real.pi_gt_three]

lemma mrt_cosine_log_lower_pos (t a b : ℝ) (ht : 0 < t) (ha : 0 < a)
    (hab : a ≤ b) : -3 ≤ ∫ y in a..b, Real.cos (t * y) / y := by
  by_cases hta : 1 ≤ t * a
  · exact (abs_le.mp (cosine_log_tail t a b ht ha hab hta)).1
  by_cases htb : t * b ≤ 1
  · exact (by norm_num : (-3 : ℝ) ≤ 0).trans (mrt_cosine_log_nonneg t a b ht.le ha hab htb)
  let c := 1 / t
  have hc : 0 < c := by dsimp [c]; positivity
  have hac : a ≤ c := by
    dsimp [c]
    apply (le_div_iff₀ ht).mpr
    nlinarith only [le_of_not_ge hta]
  have hcb : c ≤ b := by
    dsimp [c]
    apply (div_le_iff₀ ht).mpr
    nlinarith only [le_of_not_ge htb]
  have htc : t * c = 1 := by dsimp [c]; field_simp
  have hhead := mrt_cosine_log_nonneg t a c ht.le ha hac htc.le
  have htail := (abs_le.mp (cosine_log_tail t c b ht hc hcb htc.ge)).1
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (mrt_cosine_log_integrable t a c ha hac) (mrt_cosine_log_integrable t c b hc hcb)]
  linarith

lemma mrt_cosine_log_lower (t a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    -3 ≤ ∫ y in a..b, Real.cos (t * y) / y := by
  by_cases ht : t = 0
  · subst t
    exact (by norm_num : (-3 : ℝ) ≤ 0).trans
      (mrt_cosine_log_nonneg 0 a b (by norm_num) ha hab (by norm_num))
  have hcos (y : ℝ) : Real.cos (|t| * y) = Real.cos (t * y) := by
    rcases le_or_gt 0 t with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, neg_mul, Real.cos_neg]
  simpa only [hcos] using mrt_cosine_log_lower_pos |t| a b (abs_pos.mpr ht) ha hab

lemma mrt_logarithmic_phase_upper (a b t : ℝ) (ha : 1 < a) (hab : a ≤ b) :
    (∫ x in a..b, oscillatoryReciprocalLog t x) ≤
      Real.log (Real.log b) - Real.log (Real.log a) + 3 := by
  have hla : 0 < Real.log a := Real.log_pos ha
  have hlab : Real.log a ≤ Real.log b := Real.log_le_log (zero_lt_one.trans ha) hab
  have hlb : 0 < Real.log b := hla.trans_le hlab
  have h₁ : IntervalIntegrable (fun y : ℝ => 1 / y) volume (Real.log a) (Real.log b) := by
    apply ContinuousOn.intervalIntegrable_of_Icc hlab
    intro y hy
    exact (continuousAt_const.div continuousAt_id (hla.trans_le hy.1).ne').continuousWithinAt
  have h₂ := mrt_cosine_log_integrable t (Real.log a) (Real.log b) hla hlab
  have he : (∫ y in Real.log a..Real.log b, (1 - Real.cos (t * y)) / y) =
      Real.log (Real.log b / Real.log a) -
        ∫ y in Real.log a..Real.log b, Real.cos (t * y) / y := by
    rw [← integral_one_div_of_pos hla hlb, ← intervalIntegral.integral_sub h₁ h₂]
    apply intervalIntegral.integral_congr
    intro y _
    ring
  rw [halasz_log_phase_substitution a b t ha hab, he, Real.log_div hlb.ne' hla.ne']
  have hh := mrt_cosine_log_lower t (Real.log a) (Real.log b) hla hlab
  linarith

theorem mrt_prime_cosine_lower : ∃ c K C : ℝ, 0 < c ∧ 0 ≤ K ∧ 0 ≤ C ∧
    ∀ a b t : ℝ, Real.exp 1 ≤ a → a ≤ b →
      -C - (8 + |t|) * K * Real.exp (-c * Real.sqrt (Real.log a)) / Real.log a ≤
        ∑ p ∈ mrtPrimeBand a b, Real.cos (t * Real.log p) / p := by
  obtain ⟨c, K, hc, hK, herr⟩ := modFiveThetaInput.halasz_prime_phase_error
  obtain ⟨C, hC, hmass⟩ := mrt_prime_band_mertens
  refine ⟨c, K, C + 3, hc, hK, by positivity, ?_⟩
  intro a b t ha hab
  have ha1 : 1 < a := (Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans_le ha
  have ha2 : 2 ≤ a := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hE := (abs_le.mp (herr a b t ha hab)).2
  have hM := (abs_le.mp (hmass a b ha2 hab)).1
  have hI := mrt_logarithmic_phase_upper a b t ha1 hab
  have he : (∑ p ∈ mrtPrimeBand a b, (1 - Real.cos (t * Real.log p)) / p) =
      (∑ p ∈ mrtPrimeBand a b, 1 / (p : ℝ)) -
        ∑ p ∈ mrtPrimeBand a b, Real.cos (t * Real.log p) / p := by
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro p _
    ring
  rw [he] at hE
  linarith

end TwoPointCorrelations

end OAI

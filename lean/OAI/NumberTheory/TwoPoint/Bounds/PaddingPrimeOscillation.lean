import OAI.NumberTheory.TwoPoint.Bounds.CosineLogIntegral
import OAI.NumberTheory.TwoPoint.Bounds.PrimeSupplyGeometry
import OAI.NumberTheory.TwoPoint.Bounds.PowerSmallBall

namespace OAI

/-! The fixed-modulus prime input implies the padding oscillation and the
reciprocal-scale small-ball bound for the actual independent padding law. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

lemma oscillatory_log_substitution (t L : ℝ) (hL : 1 ≤ L) :
    (∫ x in Real.exp 1..Real.exp L, oscillatoryReciprocalLog t x) =
      ∫ y in (1 : ℝ)..L, (1 - Real.cos (t * y)) / y := by
  have hab : Real.exp 1 ≤ Real.exp L := Real.exp_le_exp.mpr hL
  have hxn (x : ℝ) (hx : x ∈ Set.uIcc (Real.exp 1) (Real.exp L)) : 0 < x := by
    have hx' : x ∈ Set.Icc (Real.exp 1) (Real.exp L) := by
      simpa only [Set.uIcc_of_le hab] using hx
    exact (Real.exp_pos 1).trans_le hx'.1
  have hderiv (x : ℝ) (hx : x ∈ Set.uIcc (Real.exp 1) (Real.exp L)) :
      HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log (hxn x hx).ne'
  have hdcont : ContinuousOn (fun x : ℝ => x⁻¹) (Set.uIcc (Real.exp 1) (Real.exp L)) :=
    continuousOn_id.inv₀ (fun x hx => (hxn x hx).ne')
  have hg : ContinuousOn (fun y : ℝ => (1 - Real.cos (t * y)) / y)
      (Real.log '' Set.uIcc (Real.exp 1) (Real.exp L)) := by
    rintro y ⟨x, hx, rfl⟩
    have hx' : x ∈ Set.Icc (Real.exp 1) (Real.exp L) := by
      simpa only [Set.uIcc_of_le hab] using hx
    have hl : 1 ≤ Real.log x := by
      simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hx'.1
    have hn : Real.log x ≠ 0 := (zero_lt_one.trans_le hl).ne'
    exact (by fun_prop (disch := assumption) :
      ContinuousAt (fun y : ℝ => (1 - Real.cos (t * y)) / y) (Real.log x)).continuousWithinAt
  have hh := intervalIntegral.integral_comp_mul_deriv' hderiv hdcont hg
  rw [Real.log_exp, Real.log_exp] at hh
  rw [← hh]
  apply intervalIntegral.integral_congr
  intro x _
  unfold oscillatoryReciprocalLog reciprocalLog
  simp only [Function.comp_def, div_eq_mul_inv]
  ring

lemma modFivePrimeBand_oscillation (E : Finset ℕ) (one : Bool) (a b t : ℝ) :
    (∑ p ∈ modFivePrimeBand E one a b, (1 - Real.cos (t * Real.log p)) / p) =
      ∑ p ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, oscillatoryReciprocalLog t p * deletedModFiveLogWeight E one p := by
  rw [modFivePrimeBand, sum_filter]
  apply sum_congr rfl
  intro p hp
  by_cases hs : ModFivePrime one p ∧ p ∉ E
  · rw [ite_eq_left hs]
    unfold deletedModFiveLogWeight
    rw [ite_eq_left hs]
    have hl : Real.log (p : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hs.1.1.one_lt)).ne'
    unfold oscillatoryReciprocalLog reciprocalLog
    field_simp
  · simp [deletedModFiveLogWeight, hs]

lemma padding_band_subset (E : Finset ℕ) (a L : ℝ) :
    modFivePrimeBand E false a (Real.exp L) ⊆ paddingPrimeSupply E L := by
  intro p hp
  obtain ⟨hpi, hs, he⟩ := mem_filter.mp hp
  apply mem_sdiff.mpr
  refine ⟨?_, he⟩
  apply mem_filter.mpr
  exact ⟨mem_Icc.mpr ⟨Nat.zero_le _, (mem_Ioc.mp hpi).2⟩, hs⟩

theorem ModFiveThetaInput.padding_oscillation (hP : ModFiveThetaInput) (E : Finset ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L t : ℝ), 1 ≤ L → |t| ≤ 2 →
      (3 / 4 : ℝ) * Real.log (1 + L * |t|) - C ≤
        paddingOscillation (paddingPrimeSupply E L) t := by
  obtain ⟨K, hK, herror⟩ := hP.deleted_log_error E
  refine ⟨10 * K + 15 / 4, by positivity, fun L t hL ht => ?_⟩
  have hh := oscillatory_theta_error (deletedModFiveLogWeight E false)
    (modFiveDensity false) K (Real.exp 1) (Real.exp L) t hK le_rfl
      (Real.exp_le_exp.mpr hL) ht (fun x hx => by
        rw [partialSum_deletedModFive]
        apply herror false x
        have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
        exact h2.trans hx.1)
  rw [← modFivePrimeBand_oscillation, oscillatory_log_substitution t L hL, Real.log_exp] at hh
  have hlower := (abs_le.mp hh).1
  have hmain := logarithmic_oscillation_lower t L ht hL
  have hsubset :
      (∑ p ∈ modFivePrimeBand E false (Real.exp 1) (Real.exp L),
        (1 - Real.cos (t * Real.log p)) / p) ≤ paddingOscillation (paddingPrimeSupply E L) t := by
    apply sum_le_sum_of_subset_of_nonneg (padding_band_subset E (Real.exp 1) L)
    intro p _ _
    exact div_nonneg (sub_nonneg.mpr (Real.cos_le_one _)) (Nat.cast_nonneg p)
  norm_num [modFiveDensity] at hlower
  linarith

lemma paddingPrimeSupply_prime {E : Finset ℕ} {L : ℝ} {p : ℕ}
    (hp : p ∈ paddingPrimeSupply E L) : p.Prime :=
  (mem_filter.mp (mem_sdiff.mp hp).1).2.1

/-- The precise padding difference law has `O_E(1/L)` mass in every
unit interval centered at zero. Its bound is uniform in all centered tuples. -/
theorem ModFiveThetaInput.padding_small_ball (hP : ModFiveThetaInput) (E : Finset ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 1 ≤ L →
      (paddingDifferenceLaw (paddingPrimeSupply E L)
        (fun _ hp => (paddingPrimeSupply_prime hp).two_le)).probability
          (fun x => |paddingDifferenceValue (paddingPrimeSupply E L) x| ≤ 1) ≤ C / L := by
  obtain ⟨C, _, hC⟩ := hP.padding_oscillation E
  refine ⟨20 * Real.exp ((8 / 5 : ℝ) * C + 64 / 5), by positivity, fun L hL => ?_⟩
  apply paddingDifference_small_ball _ _ L C (zero_lt_one.trans_le hL)
  intro t ht
  apply hC L t hL
  rw [abs_of_nonneg ht.1]
  linarith [ht.2]

end TwoPointCorrelations

end OAI

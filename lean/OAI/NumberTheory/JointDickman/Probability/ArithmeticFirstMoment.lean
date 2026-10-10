import OAI.NumberTheory.JointDickman.Probability.WeightedFirstMoment
import OAI.NumberTheory.JointDickman.Probability.ArithmeticSecondMoment

namespace OAI

/-! # Positive first moment for the actual arithmetic divisor weight -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem arithmeticWeighted_first_lower
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ d : ℝ, 0 < d ∧ ∀ (L : ℕ) (τ : ℝ), 0 < L → 0 < τ →
      ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T : ℕ) (w : ℕ → ℕ → ℝ), C₀ ≤ C →
        0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) →
        (∀ a c, 0 ≤ w a c ∧ w a c ≤ 1) →
        (∀ a c, (a,c) ∈ amplificationInteriorPairs B T → 1 ≤ w a c) →
        d ≤ arithmeticAmplificationMoment B L τ C w 1 := by
  obtain ⟨d,hd,hfirst⟩ := independentWeighted_first_lower hFord hSD hM hMP
  refine ⟨d/2, by positivity, ?_⟩
  intro L τ hL hτ
  obtain ⟨C₀,hC₀,hb⟩ := hfirst L τ hL hτ
  have he := amplification_quadratic_error_tendsto.eventually
    (eventually_le_nhds (by positivity : (0 : ℝ) < d/2))
  refine ⟨C₀,hC₀,?_⟩
  filter_upwards [hb,he,eventually_gt_atTop 1] with B hB hE hB1
  intro C T w hC hT hTsize hw hi
  have hpos := hB C T w hC hT hTsize (fun a c => (hw a c).1) hi
  have herr := arithmeticMoment_independent_error (L := L) (τ := τ) (C := C) hB1 w hw 1
  have hBN : (1 : ℝ) ≤ B := by exact_mod_cast (by omega : 1 ≤ B)
  have hpow : (B : ℝ) ≤ (B : ℝ)^2 := by nlinarith
  have htail : 0 ≤ ∑ p ∈ auxiliaryPrimes B, 1 / (p : ℝ)^2 := by positivity
  have hcompare : 6*(B : ℝ)^1*(∑ p ∈ auxiliaryPrimes B, 1 / (p : ℝ)^2) ≤
      6*(B : ℝ)^2*(∑ p ∈ auxiliaryPrimes B, 1 / (p : ℝ)^2) := by
    rw [pow_one]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by norm_num)) htail
  have habs := herr.trans (hcompare.trans hE)
  have hl := neg_le_abs (arithmeticAmplificationMoment B L τ C w 1 -
    independentAmplificationMoment B L τ C w 1)
  linarith

end JointDickman

end OAI

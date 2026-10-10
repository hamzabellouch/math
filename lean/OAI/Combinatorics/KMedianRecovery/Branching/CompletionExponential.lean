import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.HitsState

namespace OAI

namespace MetricKMedianRecovery.Sampling.Comparison
open Completion Categorical FiniteSampling Guided

lemma completion_exponential : ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ, 0 < m →
    Real.exp (-c*m) ≤ (1/(32*Real.exp 1))^m*(3/197:ℝ) := by
  let r : ℝ := (1/(32*Real.exp 1))*(3/197)
  have hr : 0 < r := by dsimp [r]; positivity
  refine ⟨1+|Real.log r|,by positivity,?_⟩
  intro m hm
  have he : Real.exp (-(1+|Real.log r|)*(m:ℝ)) ≤ r^m := by
    conv_rhs => rw [← Real.exp_log hr,← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hl := neg_abs_le (Real.log r)
    have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith
  apply he.trans
  dsimp only [r]
  rw [mul_pow]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hpow := pow_le_pow_of_le_one (show (0:ℝ) ≤ 3/197 by norm_num)
    (show (3/197:ℝ) ≤ 1 by norm_num) hm
  simpa only [pow_one] using hpow

variable {V : Type*} [Fintype V] [LinearOrder V] [PseudoMetricSpace V]

theorem recoveryTrial_exponential : ∃ c : ℝ, 0 < c ∧
    ∀ {D S O : Finset V} (C : Comparison D S O) (hD : D.Nonempty)
      (F : Finset V) (hSF : S ⊆ F), O ⊆ F → ∀ (hS : S.Nonempty)
      (Δ : ℝ) (hΔ : 1 ≤ Δ) (hbound : ∀ x, ∀ f ∈ F, dist x f ≤ Δ),
      (∀ w ∈ D, ∀ f ∈ F, (1:ℝ) ≤ dist w f) →
      0 < comparisonCost D C.assign → 0 < C.bad.card →
      Real.exp (-c*C.bad.card) ≤
        probability (fun seed : IntegralBits D Δ C.bad.card × (Fin (localTapeBound F C.bad.card) → Bool) =>
          realCost D (recoveryTrial D F S hD hSF hS Δ (comparisonCost D C.assign)
            (by linarith) hbound C.bad.card seed) ≤ (197/100:ℝ)*comparisonCost D C.assign) := by
  obtain ⟨c,hc,hsample⟩ := sampling_exponential
  obtain ⟨d,hd,hcompletion⟩ := completion_exponential
  refine ⟨c+d,add_pos hc hd,?_⟩
  intro D S O C hD F hSF hOF hS Δ hΔ hbound hsep hP hm
  calc
    _ = Real.exp (-c*C.bad.card)*Real.exp (-d*C.bad.card) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ ((1/2:ℝ)^(2*C.bad.card)*samplingBound C.bad.card) *
        ((1/(32*Real.exp 1))^C.bad.card*(3/197:ℝ)) :=
      mul_le_mul (hsample C.bad.card) (hcompletion C.bad.card hm)
        (Real.exp_nonneg _) ((Real.exp_nonneg _).trans (hsample C.bad.card))
    _ ≤ _ := C.recoveryTrial_success hD F hSF hOF hS Δ hΔ hbound hsep hP hm
end MetricKMedianRecovery.Sampling.Comparison

end OAI

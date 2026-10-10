import OAI.NumberTheory.JointDickman.Probability.ArithmeticFirstMoment
import OAI.NumberTheory.JointDickman.Arithmetic.AmplificationSmoothCutoff

namespace OAI

/-! # The two arithmetic moments for a concrete smooth amplification weight -/

namespace JointDickman
open Finset Filter
open scoped Topology

theorem smooth_arithmetic_first_lower
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hSD : PublishedInputs.SquarefreeSelbergDelangeInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput)
    (hMP : PublishedInputs.PrimeProductMertensInput) :
    ∃ d : ℝ, 0 < d ∧ ∀ (L : ℕ) (τ : ℝ), 0 < L → 0 < τ →
      ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ᶠ B : ℕ in atTop, ∀ (C : ℝ) (T : ℕ), C₀ ≤ C →
        0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) →
        d ≤ arithmeticAmplificationMoment B L τ C (amplificationSmoothWeight B T) 1 := by
  obtain ⟨d,hd,hl⟩ := arithmeticWeighted_first_lower hFord hSD hM hMP
  refine ⟨d,hd,?_⟩
  intro L τ hL hτ
  obtain ⟨C₀,hC₀,hb⟩ := hl L τ hL hτ
  refine ⟨C₀,hC₀,?_⟩
  filter_upwards [hb,eventually_gt_atTop 0] with B hB hB0
  intro C T hC hT hTsize
  exact hB C T (amplificationSmoothWeight B T) hC hT hTsize
    (amplificationSmoothWeight_bounds B T)
    (fun a c hac => (amplificationSmoothWeight_one_on_interior hB0 hT hac).ge)

theorem smooth_arithmetic_second_bound
    (hFord : PublishedInputs.FordUpperSieveInput)
    (hM : PublishedInputs.PrimeReciprocalMertensInput) :
    ∀ (L : ℕ) (τ C : ℝ), ∃ K : ℝ, 0 < K ∧ ∀ᶠ B : ℕ in atTop,
      ∀ T : ℕ, 0 < T → (T : ℝ) ≤ Real.exp ((1/10 : ℝ)*B) →
        arithmeticAmplificationMoment B L τ C (amplificationSmoothWeight B T) 2 ≤ K := by
  intro L τ C
  obtain ⟨K,hK,hb⟩ := arithmeticAmplification_second_bound hFord hM L τ C
  refine ⟨K,hK,?_⟩
  filter_upwards [hb,eventually_gt_atTop 0] with B hB hB0
  intro T hT hTsize
  exact hB T (amplificationSmoothWeight B T) hT hTsize
    (amplificationSmoothWeight_bounds B T)
    (amplificationSmoothWeight_support hB0 hT)

end JointDickman

end OAI

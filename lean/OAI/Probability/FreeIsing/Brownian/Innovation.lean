import OAI.Probability.FreeIsing.Brownian.Characterization
import OAI.Probability.FreeIsing.Estimates.InnovationCharacteristic

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal
open Problem367.ConditionalCharacteristic

namespace Problem367.BrownianInnovation

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem setIntegral_character_of_bounded_drift
    {F : Filtration ℝ≥0 mΩ} {B W : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hW : Martingale W F P)
    (hvariance : ∀ a b : ℝ≥0, a ≤ b →
      P[(fun ω => (B b ω - B a ω)^2) | F a] =ᵐ[P]
        fun _ => (b : ℝ) - (a : ℝ))
    {L : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ a b : ℝ≥0, a ≤ b → ∀ᵐ ω ∂P,
      |(W b ω - W a ω) - (B b ω - B a ω)| ≤ L * ((b : ℝ) - (a : ℝ)))
    {s t : ℝ≥0} (hst : s ≤ t) {A : Set Ω} (hA : MeasurableSet[F s] A) (u : ℝ) :
    (∫ ω in A, character (fun ω => W t ω - W s ω) u ω ∂P) =
      P.real A * Complex.exp (-(((t - s : ℝ≥0) : ℝ) : ℂ) * (u : ℂ)^2 / 2) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let Z : Ω → ℂ := A.indicator (fun _ => 1)
  have hZ : StronglyMeasurable[F s] Z := stronglyMeasurable_const.indicator hA
  have hZbound : ∀ᵐ ω ∂P, ‖Z ω‖ ≤ 1 := by
    apply Filter.Eventually.of_forall
    intro ω
    by_cases hω : ω ∈ A <;> simp [Z, hω]
  have h := InnovationCharacteristic.integral_characteristic_eq_gaussian_of_bounded_drift
    hB hW hvariance hL hbound s (t - s) u Z hZ hZbound
  rw [add_tsub_cancel_of_le hst] at h
  have heq : (fun ω => Z ω *
      Complex.exp (((u * (W t ω - W s ω) : ℝ) : ℂ) * Complex.I)) =
      A.indicator (character (fun ω => W t ω - W s ω) u) := by
    funext ω
    by_cases hω : ω ∈ A <;> simp [Z, character, hω, Complex.ofReal_mul]
  have hZint : (∫ ω, Z ω ∂P) = (P.real A : ℂ) := by
    simp [Z, integral_indicator ((F.le s) A hA)]
  have hexp : ((-(u ^ 2 / 2) * ((t - s : ℝ≥0) : ℝ) : ℝ) : ℂ) =
      -(((t - s : ℝ≥0) : ℝ) : ℂ) * (u : ℂ)^2 / 2 := by
    push_cast
    ring
  rw [heq, integral_indicator ((F.le s) A hA), hZint, hexp] at h
  exact h.trans (mul_comm _ _)

theorem isPreBrownianReal_of_bounded_drift
    {F : Filtration ℝ≥0 mΩ} {B W : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hW : Martingale W F P)
    (hvariance : ∀ a b : ℝ≥0, a ≤ b →
      P[(fun ω => (B b ω - B a ω)^2) | F a] =ᵐ[P]
        fun _ => (b : ℝ) - (a : ℝ))
    {L : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ a b : ℝ≥0, a ≤ b → ∀ᵐ ω ∂P,
      |(W b ω - W a ω) - (B b ω - B a ω)| ≤ L * ((b : ℝ) - (a : ℝ)))
    (hzero : ∀ᵐ ω ∂P, W 0 ω = 0) :
    IsPreBrownianReal W P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  apply BrownianCharacterization.isPreBrownianReal_of_setIntegral_character
    F hW.stronglyAdapted hzero
  intro s t hst A hA u
  exact setIntegral_character_of_bounded_drift hB hW hvariance hL hbound hst hA u

theorem isBrownianReal_of_bounded_drift
    {F : Filtration ℝ≥0 mΩ} {B W : ℝ≥0 → Ω → ℝ}
    (hB : IsPreBrownianReal B P) (hW : Martingale W F P)
    (hvariance : ∀ a b : ℝ≥0, a ≤ b →
      P[(fun ω => (B b ω - B a ω)^2) | F a] =ᵐ[P]
        fun _ => (b : ℝ) - (a : ℝ))
    {L : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ a b : ℝ≥0, a ≤ b → ∀ᵐ ω ∂P,
      |(W b ω - W a ω) - (B b ω - B a ω)| ≤ L * ((b : ℝ) - (a : ℝ)))
    (hzero : ∀ᵐ ω ∂P, W 0 ω = 0)
    (hcontinuous : ∀ᵐ ω ∂P, Continuous (fun t => W t ω)) :
    IsBrownianReal W P :=
  ⟨isPreBrownianReal_of_bounded_drift hB hW hvariance hL hbound hzero, hcontinuous⟩

end Problem367.BrownianInnovation

end

end OAI

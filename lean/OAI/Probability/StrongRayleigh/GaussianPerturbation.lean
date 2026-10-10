import OAI.Probability.StrongRayleigh.GaussianMomentBounds
import OAI.Probability.StrongRayleigh.PerturbedMoments

namespace OAI

universe u_1

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal MeasureTheory

namespace Problem336AdditiveD139.GaussianPerturbation

open GaussianMomentBounds PerturbedMoments

variable {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {mQ mH : MeasurableSpace Ω} {Q R : Ω → ℝ} {v : ℝ≥0}

theorem integrable_moments
    (hQ : HasLaw Q (gaussianReal 0 v) P)
    (hRm : AEStronglyMeasurable[mΩ] R P) (b : ℝ) (hb : 0 ≤ b)
    (hR : ∀ᵐ ω ∂P, |R ω| ≤ b) :
    Integrable (fun ω => Q ω + R ω) P ∧
    Integrable (fun ω => (Q ω + R ω) ^ 2) P ∧
    Integrable (fun ω => |Q ω + R ω| ^ 3) P := by
  let : IsProbabilityMeasure P := hQ.isProbabilityMeasure
  have hQi := integrable_of_hasLaw hQ
  have hRi : Integrable R P := (integrable_const b).mono' hRm (by
    simpa only [Real.norm_eq_abs] using hR)
  exact ⟨hQi.add hRi,
    integrable_square_add b hb hQi (integrable_sq_of_hasLaw hQ) hRm hR,
    integrable_abs_cube_add b hb hQ.aemeasurable.aestronglyMeasurable
      (integrable_abs_pow_of_hasLaw hQ 3) hRm hR⟩

theorem conditional_moment_bounds
    (hQ : HasLaw Q (gaussianReal 0 v) P)
    (hleQ : mQ ≤ mΩ) (hleH : mH ≤ mΩ)
    (hmQ : StronglyMeasurable[mQ] Q) (hind : Indep mQ mH P)
    (hRm : AEStronglyMeasurable[mΩ] R P) (b : ℝ) (hb : 0 ≤ b)
    (hR : ∀ᵐ ω ∂P, |R ω| ≤ b) :
    ∀ᵐ ω ∂P,
      |P[(fun ω => (Q ω + R ω) ^ 2) | mH] ω - (v : ℝ)| ≤
        2 * b * Real.sqrt v + b ^ 2 ∧
      P[(fun ω => |Q ω + R ω| ^ 3) | mH] ω ≤
        4 * (standardThirdAbsMoment * (v : ℝ) * Real.sqrt v + b ^ 3) := by
  let : IsProbabilityMeasure P := hQ.isProbabilityMeasure
  obtain ⟨_, hQ₂, hQ₁, hQ₃⟩ := conditional_gaussian_moments hQ hleQ hleH hmQ hind
  obtain ⟨_, hD₂, hD₃⟩ := integrable_moments hQ hRm b hb hR
  have hs := condExp_square_perturbation hleH b hb
    (integrable_of_hasLaw hQ) (integrable_sq_of_hasLaw hQ) hD₂ hR
  have hc := condExp_abs_cube_perturbation hleH b hb
    (integrable_abs_pow_of_hasLaw hQ 3) hD₃ hR
  filter_upwards [hQ₂, hQ₁, hQ₃, hs, hc] with ω h₂ h₁ h₃ hsω hcω
  constructor
  · rw [h₂] at hsω
    have hmul := mul_le_mul_of_nonneg_left h₁ (by positivity : 0 ≤ 2 * b)
    linarith
  · simpa only [h₃] using hcω

theorem integral_moment_bounds
    (hQ : HasLaw Q (gaussianReal 0 v) P)
    (hRm : AEStronglyMeasurable[mΩ] R P) (b : ℝ) (hb : 0 ≤ b)
    (hR : ∀ᵐ ω ∂P, |R ω| ≤ b) :
    |(∫ ω, (Q ω + R ω) ^ 2 ∂P) - (v : ℝ)| ≤
      2 * b * Real.sqrt v + b ^ 2 ∧
    (∫ ω, |Q ω + R ω| ^ 3 ∂P) ≤
      4 * (standardThirdAbsMoment * (v : ℝ) * Real.sqrt v + b ^ 3) := by
  let : IsProbabilityMeasure P := hQ.isProbabilityMeasure
  constructor
  · have h := integral_square_perturbation b hb
      (integrable_of_hasLaw hQ) (integrable_sq_of_hasLaw hQ) hRm hR
    rw [integral_sq_of_hasLaw hQ] at h
    have hmul := mul_le_mul_of_nonneg_left (integral_abs_le_of_hasLaw hQ)
      (by positivity : 0 ≤ 2 * b)
    linarith
  · have h := integral_abs_cube_perturbation b hb hQ.aemeasurable.aestronglyMeasurable
      (integrable_abs_pow_of_hasLaw hQ 3) hRm hR
    simpa only [integral_abs_cube_of_hasLaw hQ] using h

end Problem336AdditiveD139.GaussianPerturbation

end

end OAI

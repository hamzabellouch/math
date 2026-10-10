import OAI.Probability.StrongRayleigh.ConditionalTaylor
import OAI.Probability.StrongRayleigh.InnovationErrorScale
import OAI.Probability.StrongRayleigh.GaussianPerturbation

namespace OAI

universe u_1

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace Problem336AdditiveD139.LocalInnovation

variable {Ω : Type u_1} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [IsProbabilityMeasure μ] {m : MeasurableSpace Ω}

theorem conditional_characteristic_error_le_scale
    (hm : m ≤ mΩ) {D : Ω → ℝ} {L σ c₃ h : ℝ}
    (hL : 0 ≤ L) (hσ : 0 ≤ σ) (hc : 0 ≤ c₃) (h0 : 0 ≤ h) (h1 : h ≤ 1)
    (hD : Integrable D μ)
    (hD2 : Integrable (fun ω => D ω ^ 2) μ)
    (hD3 : Integrable (fun ω => |D ω| ^ 3) μ)
    (hmean : μ[D | m] =ᵐ[μ] fun _ => 0)
    (hsecond : ∀ᵐ ω ∂μ,
      |μ[fun a => D a ^ 2 | m] ω - h * σ ^ 2|
        ≤ 2 * (L * h) * (σ * Real.sqrt h) + (L * h) ^ 2)
    (hthird : ∀ᵐ ω ∂μ,
      μ[fun a => |D a| ^ 3 | m] ω
        ≤ 4 * (c₃ * σ ^ 3 * h * Real.sqrt h + (L * h) ^ 3)) :
    ∀ᵐ ω ∂μ,
      ‖μ[fun a => Complex.exp (Complex.I * (D a : ℂ)) | m] ω -
          (Real.exp (-(h * σ ^ 2) / 2) : ℂ)‖ ≤
        InnovationErrorScale.errorConstant L σ c₃ * h * Real.sqrt h := by
  have hTaylor := CharacteristicTaylor.conditional_characteristic_bound
    hm hD hD2 hD3 hmean (mul_nonneg h0 (sq_nonneg σ))
  filter_upwards [hTaylor, hsecond, hthird] with ω ht hs hcub
  apply InnovationErrorScale.local_error_le_scale hL hσ hc h0 h1 _ hs hcub
  linarith

theorem conditional_characteristic_error_le_variance_scale
    (hm : m ≤ mΩ) {D : Ω → ℝ} {L V c₃ h : ℝ}
    (hL : 0 ≤ L) (hV : 0 ≤ V) (hc : 0 ≤ c₃) (h0 : 0 ≤ h) (h1 : h ≤ 1)
    (hD : Integrable D μ)
    (hD2 : Integrable (fun ω => D ω ^ 2) μ)
    (hD3 : Integrable (fun ω => |D ω| ^ 3) μ)
    (hmean : μ[D | m] =ᵐ[μ] fun _ => 0)
    (hsecond : ∀ᵐ ω ∂μ,
      |μ[fun a => D a ^ 2 | m] ω - h * V|
        ≤ 2 * (L * h) * Real.sqrt (h * V) + (L * h) ^ 2)
    (hthird : ∀ᵐ ω ∂μ,
      μ[fun a => |D a| ^ 3 | m] ω
        ≤ 4 * (c₃ * (h * V) * Real.sqrt (h * V) + (L * h) ^ 3)) :
    ∀ᵐ ω ∂μ,
      ‖μ[fun a => Complex.exp (Complex.I * (D a : ℂ)) | m] ω -
          (Real.exp (-(h * V) / 2) : ℂ)‖ ≤
        InnovationErrorScale.errorConstant L (Real.sqrt V) c₃ * h * Real.sqrt h := by
  have hsqrt : Real.sqrt (h * V) = Real.sqrt V * Real.sqrt h := by
    rw [Real.sqrt_mul h0]
    ring
  have hcube : c₃ * Real.sqrt V ^ 3 * h * Real.sqrt h =
      c₃ * (h * V) * Real.sqrt (h * V) := by
    rw [hsqrt, pow_succ, Real.sq_sqrt hV]
    ring
  have hs : ∀ᵐ ω ∂μ,
      |μ[fun a => D a ^ 2 | m] ω - h * Real.sqrt V ^ 2|
        ≤ 2 * (L * h) * (Real.sqrt V * Real.sqrt h) + (L * h) ^ 2 := by
    simpa only [Real.sq_sqrt hV, hsqrt] using hsecond
  have ht : ∀ᵐ ω ∂μ,
      μ[fun a => |D a| ^ 3 | m] ω
        ≤ 4 * (c₃ * Real.sqrt V ^ 3 * h * Real.sqrt h + (L * h) ^ 3) := by
    simpa only [hcube] using hthird
  simpa only [Real.sq_sqrt hV] using
    conditional_characteristic_error_le_scale hm hL (Real.sqrt_nonneg V) hc h0 h1
      hD hD2 hD3 hmean hs ht

theorem gaussian_perturbation_characteristic_error
    {mQ : MeasurableSpace Ω} {Q R : Ω → ℝ} {h V : ℝ≥0} {L : ℝ}
    (hleQ : mQ ≤ mΩ) (hm : m ≤ mΩ)
    (hQ : HasLaw Q (gaussianReal 0 (h * V)) μ)
    (hmQ : StronglyMeasurable[mQ] Q) (hind : Indep mQ m μ)
    (hRm : AEStronglyMeasurable[mΩ] R μ)
    (hL : 0 ≤ L) (h1 : (h : ℝ) ≤ 1)
    (hR : ∀ᵐ ω ∂μ, |R ω| ≤ L * (h : ℝ))
    (hmean : μ[(fun ω => Q ω + R ω) | m] =ᵐ[μ] fun _ => 0) :
    ∀ᵐ ω ∂μ,
      ‖μ[fun a => Complex.exp (Complex.I * ((Q a + R a : ℝ) : ℂ)) | m] ω -
          (Real.exp (-((h : ℝ) * (V : ℝ)) / 2) : ℂ)‖ ≤
        InnovationErrorScale.errorConstant L (Real.sqrt V)
          GaussianMomentBounds.standardThirdAbsMoment * (h : ℝ) * Real.sqrt h := by
  have hb : 0 ≤ L * (h : ℝ) := mul_nonneg hL h.coe_nonneg
  obtain ⟨hD, hD2, hD3⟩ := GaussianPerturbation.integrable_moments hQ hRm _ hb hR
  have hbounds := GaussianPerturbation.conditional_moment_bounds
    hQ hleQ hm hmQ hind hRm _ hb hR
  apply conditional_characteristic_error_le_variance_scale hm hL V.coe_nonneg
    GaussianMomentBounds.standardThirdAbsMoment_nonneg h.coe_nonneg h1
    hD hD2 hD3 hmean
  · filter_upwards [hbounds] with ω hω
    simpa only [NNReal.coe_mul] using hω.1
  · filter_upwards [hbounds] with ω hω
    simpa only [NNReal.coe_mul] using hω.2

end Problem336AdditiveD139.LocalInnovation

end

end OAI

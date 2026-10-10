import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OAI

namespace FiniteFactor
open MeasureTheory
open scoped ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- A conditional probability bound controls any nonnegative integrable weight
measurable with respect to the conditioning sigma algebra. -/
theorem conditional_mask_integral_le [IsFiniteMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {f : Ω → ℝ} {H : Set Ω} {δ : ℝ}
    (hf : Integrable f μ) (hfm : StronglyMeasurable[m] f)
    (hf0 : 0 ≤ᵐ[μ] f) (hH : @MeasurableSet Ω mΩ H)
    (hcond : ∀ᵐ ω ∂μ, μ[H.indicator (fun _ => (1 : ℝ)) | m] ω ≤ δ) :
    ∫ ω in H, f ω ∂μ ≤ δ * ∫ ω, f ω ∂μ := by
  let g : Ω → ℝ := H.indicator (fun _ => 1)
  have hg : Integrable g μ := (integrable_const (1 : ℝ)).indicator hH
  have heq : f * g = H.indicator f := by
    ext ω
    by_cases h : ω ∈ H <;> simp [g, h]
  have hfg : Integrable (f * g) μ := heq.symm ▸ hf.indicator hH
  have hout : μ[f * g | m] =ᵐ[μ] f * μ[g | m] :=
    condExp_mul_of_stronglyMeasurable_left hfm hfg hg
  have hi : Integrable (f * μ[g | m]) μ := integrable_condExp.congr hout
  calc
    ∫ ω in H, f ω ∂μ = ∫ ω, (f * g) ω ∂μ := by
      rw [heq, integral_indicator hH]
    _ = ∫ ω, μ[f * g | m] ω ∂μ := (integral_condExp hm).symm
    _ = ∫ ω, f ω * μ[g | m] ω ∂μ := integral_congr_ae hout
    _ ≤ ∫ ω, f ω * δ ∂μ := by
      apply integral_mono_ae hi (hf.mul_const δ)
      filter_upwards [hf0, hcond] with ω hfω hcω
      exact mul_le_mul_of_nonneg_left hcω hfω
    _ = δ * ∫ ω, f ω ∂μ := by rw [integral_mul_const]; exact mul_comm _ _

/-- Cauchy–Schwarz in the integral form used on Ω × ℤ. -/
theorem integral_mul_le_sqrt_squares {f g : Ω → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hf0 : 0 ≤ᵐ[μ] f) (hg0 : 0 ≤ᵐ[μ] g) :
    ∫ ω, f ω * g ω ∂μ ≤
      Real.sqrt (∫ ω, f ω ^ 2 ∂μ) * Real.sqrt (∫ ω, g ω ^ 2 ∂μ) := by
  have hh : Real.HolderConjugate 2 2 := by norm_num [Real.holderConjugate_iff]
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hh hf0 hg0
    (by simpa using hf) (by simpa using hg)
  simpa [Real.sqrt_eq_rpow] using h

/-- A masked L² mass at most δ and an unmasked mass at most one yield √δ.
The ambient measure can be probability times counting measure, so this is
not restricted to a finite coefficient set. -/
theorem integral_mul_le_sqrt_of_square_bounds {f g : Ω → ℝ} {δ : ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hf0 : 0 ≤ᵐ[μ] f) (hg0 : 0 ≤ᵐ[μ] g)
    (hδ : ∫ ω, f ω ^ 2 ∂μ ≤ δ) (hg1 : ∫ ω, g ω ^ 2 ∂μ ≤ 1) :
    ∫ ω, f ω * g ω ∂μ ≤ Real.sqrt δ := by
  calc
    ∫ ω, f ω * g ω ∂μ ≤
        Real.sqrt (∫ ω, f ω ^ 2 ∂μ) * Real.sqrt (∫ ω, g ω ^ 2 ∂μ) :=
      integral_mul_le_sqrt_squares hf hg hf0 hg0
    _ ≤ Real.sqrt δ * Real.sqrt 1 :=
      mul_le_mul (Real.sqrt_le_sqrt hδ) (Real.sqrt_le_sqrt hg1)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = Real.sqrt δ := by simp

/-- Countably many masks, each with a conditional probability bound.
The sum is genuinely infinite; no bound on the union of the events is used.
Apply to f_v=|ξ_v(x)|² or f_v=|γ_{n+v}(y)|² in the two orientations. -/
theorem conditional_mask_tsum_integral_le [IsFiniteMeasure μ]
    {ι : Type*} [Countable ι] {m : MeasurableSpace Ω} (hm : m ≤ mΩ)
    {f : ι → Ω → ℝ} {H : ι → Set Ω} {δ : ℝ}
    (hf : ∀ i, Integrable (f i) μ)
    (hfm : ∀ i, StronglyMeasurable[m] (f i))
    (hf0 : ∀ i ω, 0 ≤ f i ω) (hH : ∀ i, @MeasurableSet Ω mΩ (H i))
    (hsum : ∀ᵐ ω ∂μ, Summable (fun i => f i ω))
    (hint : Integrable (fun ω => ∑' i, f i ω) μ)
    (hcond : ∀ i, ∀ᵐ ω ∂μ,
      μ[(H i).indicator (fun _ => (1 : ℝ)) | m] ω ≤ δ) :
    ∫ ω, (∑' i, (H i).indicator (f i) ω) ∂μ ≤
      δ * ∫ ω, (∑' i, f i ω) ∂μ := by
  classical
  have hmask0 : ∀ i ω, 0 ≤ (H i).indicator (f i) ω := by
    intro i ω
    by_cases h : ω ∈ H i <;> simp [h, hf0]
  have hmaskle : ∀ i ω, (H i).indicator (f i) ω ≤ f i ω := by
    intro i ω
    by_cases h : ω ∈ H i <;> simp [h, hf0]
  have hmaskSum : ∀ᵐ ω ∂μ, Summable (fun i => (H i).indicator (f i) ω) := by
    filter_upwards [hsum] with ω hω
    exact hω.of_nonneg_of_le (fun i => hmask0 i ω) (fun i => hmaskle i ω)
  have horig := hasSum_integral_of_dominated_convergence f
    (fun i => (hf i).aestronglyMeasurable)
    (fun i => Filter.Eventually.of_forall fun ω => (Real.norm_of_nonneg (hf0 i ω)).le)
    hsum hint (hsum.mono fun _ h => h.hasSum)
  have hmasked := hasSum_integral_of_dominated_convergence f
    (fun i => ((hf i).indicator (hH i)).aestronglyMeasurable)
    (fun i => Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_of_nonneg (hmask0 i ω)]
      exact hmaskle i ω)
    hsum hint (hmaskSum.mono fun _ h => h.hasSum)
  calc
    ∫ ω, (∑' i, (H i).indicator (f i) ω) ∂μ =
        ∑' i, ∫ ω, (H i).indicator (f i) ω ∂μ := hmasked.tsum_eq.symm
    _ ≤ ∑' i, δ * ∫ ω, f i ω ∂μ := by
      apply Summable.tsum_le_tsum _ hmasked.summable (horig.summable.mul_left δ)
      intro i
      rw [integral_indicator (hH i)]
      exact conditional_mask_integral_le hm (hf i) (hfm i)
        (Filter.Eventually.of_forall (hf0 i)) (hH i) (hcond i)
    _ = δ * ∫ ω, (∑' i, f i ω) ∂μ := by rw [tsum_mul_left, horig.tsum_eq]

theorem attenuated_two_mask_integral_le
    {f g R : Ω → ℝ} {H₁ H₂ : Set Ω} {ε δ : ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hf0 : 0 ≤ᵐ[μ] f) (hg0 : 0 ≤ᵐ[μ] g)
    (hf1 : ∫ ω, f ω ^ 2 ∂μ ≤ 1) (hg1 : ∫ ω, g ω ^ 2 ∂μ ≤ 1)
    (hH₁ : MeasurableSet H₁) (hH₂ : MeasurableSet H₂)
    (hmask₁ : ∫ ω, (H₁.indicator f ω) ^ 2 ∂μ ≤ δ)
    (hmask₂ : ∫ ω, (H₂.indicator g ω) ^ 2 ∂μ ≤ δ)
    (hε : 0 ≤ ε) (hRm : AEStronglyMeasurable R μ)
    (hR0 : 0 ≤ᵐ[μ] R) (hR1 : ∀ᵐ ω ∂μ, R ω ≤ 1)
    (hR : ∀ᵐ ω ∂μ, R ω ≤ ε + H₁.indicator (fun _ => 1) ω +
      H₂.indicator (fun _ => 1) ω) :
    ∫ ω, R ω * f ω * g ω ∂μ ≤ ε + 2 * Real.sqrt δ := by
  have hm₁ : MemLp (H₁.indicator f) 2 μ := hf.indicator hH₁
  have hm₂ : MemLp (H₂.indicator g) 2 μ := hg.indicator hH₂
  have hm₁0 : 0 ≤ᵐ[μ] H₁.indicator f := hf0.mono fun ω h => by
    change 0 ≤ f ω at h
    by_cases hω : ω ∈ H₁ <;> simp [hω, h]
  have hm₂0 : 0 ≤ᵐ[μ] H₂.indicator g := hg0.mono fun ω h => by
    change 0 ≤ g ω at h
    by_cases hω : ω ∈ H₂ <;> simp [hω, h]
  have herr₁ := integral_mul_le_sqrt_of_square_bounds hm₁ hg hm₁0 hg0 hmask₁ hg1
  have herr₂ : ∫ ω, f ω * H₂.indicator g ω ∂μ ≤ Real.sqrt δ := by
    simpa only [mul_comm] using
      integral_mul_le_sqrt_of_square_bounds hm₂ hf hm₂0 hf0 hmask₂ hf1
  have hgood : ∫ ω, f ω * g ω ∂μ ≤ 1 := by
    simpa using integral_mul_le_sqrt_of_square_bounds hf hg hf0 hg0 hf1 hg1
  have hfg : Integrable (fun ω => f ω * g ω) μ := hf.integrable_mul hg
  have hi₁ : Integrable (fun ω => H₁.indicator f ω * g ω) μ := hm₁.integrable_mul hg
  have hi₂ : Integrable (fun ω => f ω * H₂.indicator g ω) μ := hf.integrable_mul hm₂
  have hprod : Integrable (fun ω => R ω * f ω * g ω) μ := by
    apply hfg.mono' ((hRm.mul hf.aestronglyMeasurable).mul hg.aestronglyMeasurable)
    filter_upwards [hf0, hg0, hR0, hR1] with ω hfω hgω hRω hRω1
    change ‖R ω * f ω * g ω‖ ≤ f ω * g ω
    rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg hRω hfω) hgω)]
    calc
      R ω * f ω * g ω = R ω * (f ω * g ω) := mul_assoc _ _ _
      _ ≤ 1 * (f ω * g ω) := mul_le_mul_of_nonneg_right hRω1 (mul_nonneg hfω hgω)
      _ = f ω * g ω := one_mul _
  have hmajor : ∀ᵐ ω ∂μ, R ω * f ω * g ω ≤
      ε * (f ω * g ω) + H₁.indicator f ω * g ω + f ω * H₂.indicator g ω := by
    filter_upwards [hf0, hg0, hR] with ω hfω hgω hRω
    calc
      R ω * f ω * g ω = R ω * (f ω * g ω) := mul_assoc _ _ _
      _ ≤ (ε + H₁.indicator (fun _ => 1) ω + H₂.indicator (fun _ => 1) ω) *
          (f ω * g ω) := mul_le_mul_of_nonneg_right hRω (mul_nonneg hfω hgω)
      _ = ε * (f ω * g ω) + H₁.indicator f ω * g ω + f ω * H₂.indicator g ω := by
        by_cases h₁ : ω ∈ H₁ <;> by_cases h₂ : ω ∈ H₂ <;>
          simp [h₁, h₂] <;> ring
  calc
    ∫ ω, R ω * f ω * g ω ∂μ ≤
        ∫ ω, ε * (f ω * g ω) + H₁.indicator f ω * g ω +
          f ω * H₂.indicator g ω ∂μ :=
      integral_mono_ae hprod (((hfg.const_mul ε).add hi₁).add hi₂) hmajor
    _ = ε * (∫ ω, f ω * g ω ∂μ) +
        (∫ ω, H₁.indicator f ω * g ω ∂μ) +
        (∫ ω, f ω * H₂.indicator g ω ∂μ) := by
      have h₁ := integral_add (hfg.const_mul ε) hi₁
      have h₂ := integral_add ((hfg.const_mul ε).add hi₁) hi₂
      dsimp only [Pi.add_apply] at h₁ h₂
      rw [h₂, h₁, integral_const_mul]
    _ ≤ ε + 2 * Real.sqrt δ := by
      have := mul_le_mul_of_nonneg_left hgood hε
      linarith

end FiniteFactor

end OAI

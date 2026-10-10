import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.Twist
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.MovingParameters
import OAI.NumberTheory.OrdinaryCorrelations.Elliott.CesaroNormFunctionEq

namespace OAI

noncomputable section
open scoped BigOperators
open Finset
open Finset Classical
open Filter
open Finset Classical Filter
open scoped Topology
open MeasureTheory intervalIntegral
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set
open Finset Filter
open ArithmeticFunction
open MeasureTheory Finset
open Classical
open Classical Finset
open Classical Finset Real MeasureTheory
open scoped ContDiff
open Filter Finset

namespace OrdinaryCorrelations.ElliottReductions

lemma mean_zero_of_nonpretentious {f : ℕ → ℂ} (hf : OneBounded f)
    (hm : Multiplicative f) (hNP : UniformlyNonpretentious f) :
    Tendsto (cesaro f) atTop (nhds 0) := by
  let p : ℕ → PretentiousEuler.MovingParameters := fun N =>
    ⟨(N, 0), by simp only [abs_zero]; positivity⟩
  have hp : Tendsto p atTop PretentiousEuler.movingFilter := by
    change Tendsto p atTop (comap (fun p : PretentiousEuler.MovingParameters => p.1.1) atTop)
    apply tendsto_comap_iff.mpr
    exact tendsto_id
  have ht := (PretentiousEuler.moving_multiplicative_mean_tendsto_zero hf hm hNP).comp hp
  change Tendsto (fun N : ℕ => (N : ℂ)⁻¹ *
    ∑ n ∈ Icc 1 N, OrdinaryArchimedeanTwist.twist f 0 n) atTop (nhds 0) at ht
  change Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ Icc 1 N, f n) atTop (nhds 0)
  simpa only [OrdinaryArchimedeanTwist.twist, Complex.ofReal_zero, zero_mul,
    mul_zero, Complex.exp_zero, mul_one] using ht

theorem absolute_mean_zero_of_divergent_defect {f : ℕ → ℂ}
    (hf : OneBounded f) (hm : Multiplicative f)
    (hdiv : ¬ Summable (primeDefect f)) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Icc 1 N, ‖f n‖)
      atTop (nhds 0) := by
  have ht := mean_zero_of_nonpretentious (normFunction_oneBounded hf)
    (normFunction_multiplicative hm) (normFunction_nonpretentious_of_divergent_defect hf hdiv)
  have he := (Complex.continuous_re.tendsto (0 : ℂ)).comp ht
  simpa only [Function.comp_def, cesaro_normFunction_eq, Complex.ofReal_re,
    Complex.zero_re] using he

theorem cancellation_of_divergent_defect (f g : ℕ → ℂ)
    (hf : OneBounded f) (hg : OneBounded g)
    (hmf : Multiplicative f) (hmg : Multiplicative g)
    (hdiv : ¬ Summable (primeDefect f) ∨ ¬ Summable (primeDefect g)) (h₁ h₂ : ℕ) :
    Tendsto (shiftAverage f g h₁ h₂) atTop (nhds 0) := by
  have hleft (f g : ℕ → ℂ) (hf : OneBounded f) (hg : OneBounded g)
      (hm : Multiplicative f) (hdiv : ¬ Summable (primeDefect f)) (h₁ h₂ : ℕ) :
      Tendsto (shiftAverage f g h₁ h₂) atTop (nhds 0) := by
    apply cancellation_of_absolute_mean_zero f g hf hg _ h₁ h₂
    exact mean_zero_of_nonpretentious (normFunction_oneBounded hf)
      (normFunction_multiplicative hm) (normFunction_nonpretentious_of_divergent_defect hf hdiv)
  rcases hdiv with hdiv | hdiv
  · exact hleft f g hf hg hmf hdiv h₁ h₂
  · have he : shiftAverage g f h₂ h₁ = shiftAverage f g h₁ h₂ :=
      funext (fun N => shiftAverage_swap _ _ _ _ N)
    rw [← he]
    exact hleft g f hg hf hmg hdiv h₂ h₁

theorem finite_defects_of_correlation_failure (f g : ℕ → ℂ)
    (hf : OneBounded f) (hg : OneBounded g)
    (hmf : Multiplicative f) (hmg : Multiplicative g) (h₁ h₂ : ℕ)
    (hfail : ¬ Tendsto (shiftAverage f g h₁ h₂) atTop (nhds 0)) :
    f 1 = 1 ∧ g 1 = 1 ∧ Summable (primeDefect f) ∧ Summable (primeDefect g) := by
  have h1f : f 1 = 1 := by
    rcases Completion.one_or_zero hmf with h1 | hz
    · exact h1
    · exact False.elim (hfail (cancellation_of_value_one_zero f g hmf hmg
        (Or.inl (hz 1 Nat.zero_lt_one)) h₁ h₂))
  have h1g : g 1 = 1 := by
    rcases Completion.one_or_zero hmg with h1 | hz
    · exact h1
    · exact False.elim (hfail (cancellation_of_value_one_zero f g hmf hmg
        (Or.inr (hz 1 Nat.zero_lt_one)) h₁ h₂))
  refine ⟨h1f, h1g, ?_, ?_⟩
  · by_contra hdiv
    exact hfail (cancellation_of_divergent_defect f g hf hg hmf hmg (Or.inl hdiv) h₁ h₂)
  · by_contra hdiv
    exact hfail (cancellation_of_divergent_defect f g hf hg hmf hmg (Or.inr hdiv) h₁ h₂)

end OrdinaryCorrelations.ElliottReductions

end

end OAI

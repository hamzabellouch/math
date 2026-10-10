import OAI.NumberTheory.OrdinaryCorrelations.Elliott.Cesaro
import OAI.NumberTheory.OrdinaryCorrelations.Elliott.PrimeDefect

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

lemma cesaro_normFunction_eq (f : ℕ → ℂ) (N : ℕ) :
    cesaro (normFunction f) N =
      (((N : ℝ)⁻¹ * ∑ n ∈ Icc 1 N, ‖f n‖ : ℝ) : ℂ) := by
  simp only [cesaro, normFunction, Complex.ofReal_mul, Complex.ofReal_inv,
    Complex.ofReal_natCast, Complex.ofReal_sum]

lemma norm_shiftAverage_le_absolute_mean (f g : ℕ → ℂ)
    (hg : OneBounded g) (h₁ h₂ N : ℕ) :
    ‖shiftAverage f g h₁ h₂ N‖ ≤
      (cesaro (normFunction (fun n => f (n + h₁))) N).re := by
  rw [cesaro_normFunction_eq, Complex.ofReal_re]
  unfold shiftAverage
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro n hn
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (hg _)

theorem cancellation_of_absolute_mean_zero (f g : ℕ → ℂ)
    (hf : OneBounded f) (hg : OneBounded g)
    (ht : Tendsto (cesaro (normFunction f)) atTop (nhds 0)) (h₁ h₂ : ℕ) :
    Tendsto (shiftAverage f g h₁ h₂) atTop (nhds 0) := by
  have hs := (Complex.continuous_re.tendsto (0 : ℂ)).comp
    (cesaro_translation_tendsto (normFunction f) (normFunction_oneBounded hf) h₁ ht)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun N => norm_shiftAverage_le_absolute_mean f g hg h₁ h₂ N) hs

end OrdinaryCorrelations.ElliottReductions

end

end OAI

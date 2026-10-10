import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.OneBounded
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.OneOrZero
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.MeanC

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

def cesaro (a : ℕ → ℂ) (N : ℕ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ n ∈ Icc 1 N, a n

lemma cesaro_translation_bound (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (h N : ℕ) :
    ‖cesaro (fun n => a (n + h)) N - cesaro a N‖ ≤
      (N : ℝ)⁻¹ * (2 * h) := by
  unfold cesaro
  rw [← mul_sub, norm_mul, norm_inv, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left
    (by simpa using SourceRoughFourier.prefix_translation_bound a N h 1 ha)
    (by positivity)

theorem cesaro_translation_error (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (h : ℕ) :
    Tendsto (fun N => cesaro (fun n => a (n + h)) N - cesaro a N)
      atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have ht : Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * (2 * h)) atTop (nhds 0) := by
    simpa using
      (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).mul_const (2 * (h : ℝ))
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun N => cesaro_translation_bound a ha h N) ht

lemma cesaro_translation_tendsto (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (h : ℕ)
    {z : ℂ} (hz : Tendsto (cesaro a) atTop (nhds z)) :
    Tendsto (cesaro (fun n => a (n + h))) atTop (nhds z) := by
  simpa only [sub_add_cancel, zero_add] using (cesaro_translation_error a ha h).add hz

lemma shiftAverage_swap (f g : ℕ → ℂ) (h₁ h₂ N : ℕ) :
    shiftAverage f g h₁ h₂ N = shiftAverage g f h₂ h₁ N := by
  unfold shiftAverage
  congr 1
  apply sum_congr rfl
  intro n hn
  exact mul_comm _ _

lemma shiftAverage_translate (f g : ℕ → ℂ) (hf : OneBounded f) (hg : OneBounded g)
    (h₁ h₂ k : ℕ) {z : ℂ}
    (hz : Tendsto (shiftAverage f g h₁ h₂) atTop (nhds z)) :
    Tendsto (shiftAverage f g (h₁ + k) (h₂ + k)) atTop (nhds z) := by
  have ha : ∀ n, ‖f (n + h₁) * g (n + h₂)‖ ≤ 1 := by
    intro n
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (hf _) (norm_nonneg _)).trans
      (by simpa only [one_mul] using hg _)
  have hz' : Tendsto (cesaro (fun n => f (n + h₁) * g (n + h₂))) atTop (nhds z) := hz
  have hlim := cesaro_translation_tendsto _ ha k hz'
  change Tendsto (fun N : ℕ => (N : ℂ)⁻¹ *
    ∑ n ∈ Icc 1 N, f (n + k + h₁) * g (n + k + h₂)) atTop (nhds z) at hlim
  change Tendsto (fun N : ℕ => (N : ℂ)⁻¹ *
    ∑ n ∈ Icc 1 N, f (n + (h₁ + k)) * g (n + (h₂ + k))) atTop (nhds z)
  simpa only [Nat.add_right_comm _ k, Nat.add_assoc] using hlim

lemma shiftAverage_of_anchored (f g : ℕ → ℂ) (hf : OneBounded f) (hg : OneBounded g)
    (h₁ h₂ : ℕ) (hh : h₁ ≤ h₂)
    (hlim : Tendsto (shiftAverage f g 0 (h₂ - h₁)) atTop (nhds 0)) :
    Tendsto (shiftAverage f g h₁ h₂) atTop (nhds 0) := by
  simpa only [zero_add, Nat.sub_add_cancel hh] using
    shiftAverage_translate f g hf hg 0 (h₂ - h₁) h₁ hlim

lemma shiftAverage_zero_left (f g : ℕ → ℂ) (hz : ∀ n, 0 < n → f n = 0)
    (h₁ h₂ N : ℕ) : shiftAverage f g h₁ h₂ N = 0 := by
  unfold shiftAverage
  have he : (∑ n ∈ Icc 1 N, f (n + h₁) * g (n + h₂)) = 0 := by
    apply sum_eq_zero
    intro n hn
    rw [hz (n + h₁) (by have := (mem_Icc.mp hn).1; omega), zero_mul]
  rw [he, mul_zero]

lemma shiftAverage_zero_right (f g : ℕ → ℂ) (hz : ∀ n, 0 < n → g n = 0)
    (h₁ h₂ N : ℕ) : shiftAverage f g h₁ h₂ N = 0 := by
  rw [shiftAverage_swap]
  exact shiftAverage_zero_left g f hz _ _ _

theorem cancellation_of_value_one_zero (f g : ℕ → ℂ)
    (hmf : Multiplicative f) (hmg : Multiplicative g)
    (hz : f 1 = 0 ∨ g 1 = 0) (h₁ h₂ : ℕ) :
    Tendsto (shiftAverage f g h₁ h₂) atTop (nhds 0) := by
  rcases hz with hf | hg
  · have hz' : ∀ n, 0 < n → f n = 0 :=
      (Completion.one_or_zero hmf).resolve_left (by rw [hf]; exact zero_ne_one)
    have he : shiftAverage f g h₁ h₂ = fun _ => 0 := by
      funext N
      exact shiftAverage_zero_left f g hz' _ _ _
    rw [he]
    exact tendsto_const_nhds
  · have hz' : ∀ n, 0 < n → g n = 0 :=
      (Completion.one_or_zero hmg).resolve_left (by rw [hg]; exact zero_ne_one)
    have he : shiftAverage f g h₁ h₂ = fun _ => 0 := by
      funext N
      exact shiftAverage_zero_right f g hz' _ _ _
    rw [he]
    exact tendsto_const_nhds

end OrdinaryCorrelations.ElliottReductions

end

end OAI

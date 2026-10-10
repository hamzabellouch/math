import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.CutoffSmall
import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.PartialSmallOfTriangleSmall

namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Finset
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius
open Filter
open MeasureTheory Filter
open MeasureTheory
open MeasureTheory Set
open Set MeasureTheory Complex
open Set

namespace OrdinaryCorrelations.PretentiousEuler
open OrdinaryRieszPerron OrdinaryTriangular Completion Filter

lemma triangle_eq_cutoff (a : ℕ → ℂ) {N : ℕ} (hN : 0<N) :
    triangle a N=(N:ℂ)*cutoffSeries a (N:ℝ) := by
  rw [cutoffSeries_eq_sum a (by exact_mod_cast hN),Nat.floor_natCast,Finset.mul_sum]
  unfold triangle
  apply Finset.sum_congr rfl
  intro n hn
  have hnc : (N:ℂ)≠0 := by exact_mod_cast hN.ne'
  push_cast
  field_simp

theorem complete_partial_small {f : ℕ → ℂ} (hf : OneBounded f)
    (hNP : UniformlyNonpretentious f) (ε : ℝ) (hε : 0<ε) :
    ∃M : ℝ, ∀N : ℕ, M≤(N:ℝ) →
      ‖∑n∈Finset.Icc 1 N, complete f n‖≤ε*(N:ℝ) := by
  apply partial_small_of_triangle_small (complete f) (complete_oneBounded hf) _ ε hε
  intro e he
  obtain ⟨M,hM,hsmall⟩ := cutoff_small hf hNP e he
  refine ⟨M,?_⟩
  intro N hNM
  have hN : 0<N := by have hh := lt_of_lt_of_le (lt_trans zero_lt_one hM) hNM; exact_mod_cast hh
  rw [triangle_eq_cutoff (complete f) hN,norm_mul,Complex.norm_natCast]
  have hh := mul_le_mul_of_nonneg_left (hsmall (N:ℝ) hNM) (Nat.cast_nonneg N)
  nlinarith

theorem complete_mean_tendsto_zero {f : ℕ → ℂ} (hf : OneBounded f)
    (hNP : UniformlyNonpretentious f) :
    Tendsto (fun N : ℕ => (N:ℂ)⁻¹*∑n∈Finset.Icc 1 N, complete f n) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨M,hsmall⟩ := complete_partial_small hf hNP (ε/2) (by positivity)
  refine ⟨max 1 ⌈M⌉₊,?_⟩
  intro N hN
  have hN1 : 1≤N := le_trans (le_max_left _ _) hN
  have hNr : 0<(N:ℝ) := by exact_mod_cast hN1
  have hMN : M≤(N:ℝ) := le_trans (Nat.le_ceil M) (by exact_mod_cast le_trans (le_max_right _ _) hN)
  rw [_root_.dist_zero_right,norm_mul,norm_inv,Complex.norm_natCast]
  have hh := mul_le_mul_of_nonneg_left (hsmall N hMN) (inv_nonneg.mpr hNr.le)
  have he : (N:ℝ)⁻¹*(ε/2*(N:ℝ))=ε/2 := by field_simp
  rw [he] at hh
  exact lt_of_le_of_lt hh (by linarith)

end OrdinaryCorrelations.PretentiousEuler

end

end OAI

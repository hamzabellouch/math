import OAI.NumberTheory.OrdinaryCorrelations.AbsoluteDefect.Phase

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
open Finset Filter

namespace OrdinaryDirichletFiberMoments
open OrdinaryDirichletMeanSquare Finset MeasureTheory
variable {ι : Type*}

def collect (S : Finset ι) (location : ι → ℕ) (a : ι → ℂ) (n : ℕ) : ℂ :=
  ∑ z ∈ S.filter (fun z => location z = n), a z

lemma collect_polynomial [DecidableEq ι] (S : Finset ι) (location : ι → ℕ)
    (a : ι → ℂ) (t : ℝ) :
    polynomial (S.image location) (collect S location a) (fun n => Real.log n) t =
      ∑ z ∈ S, a z * phase (Real.log (location z)) t := by
  unfold polynomial collect
  simp_rw [sum_mul]
  calc
    _ = ∑ n ∈ S.image location, ∑ z ∈ S.filter (fun z => location z = n),
        a z * phase (Real.log (location z)) t := by
      apply sum_congr rfl
      intro n hn
      apply sum_congr rfl
      intro z hz
      rw [(mem_filter.mp hz).2]
    _ = _ := sum_fiberwise_of_maps_to (fun z hz => mem_image.mpr ⟨z,hz,rfl⟩) _

lemma collect_norm_sq [DecidableEq ι] (S : Finset ι) (location : ι → ℕ)
    (a : ι → ℂ) (n : ℕ) :
    ‖collect S location a n‖^2 ≤
      ((S.filter (fun z => location z = n)).card : ℝ) *
        ∑ z ∈ S.filter (fun z => location z = n), ‖a z‖^2 := by
  unfold collect
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) _).trans
    sq_sum_le_card_mul_sum_sq

variable [DecidableEq ι]

lemma collect_energy (S : Finset ι) (location : ι → ℕ) (a : ι → ℂ) :
    (∑ n ∈ S.image location, ‖collect S location a n‖^2) ≤
      ∑ z ∈ S, ((S.filter (fun w => location w = location z)).card : ℝ)*‖a z‖^2 := by
  calc
    _ ≤ ∑ n ∈ S.image location,
        ((S.filter (fun z => location z = n)).card : ℝ) *
          ∑ z ∈ S.filter (fun z => location z = n), ‖a z‖^2 :=
      sum_le_sum fun n hn => collect_norm_sq S location a n
    _ = _ := by
      simp_rw [mul_sum]
      calc
        _ = ∑ n ∈ S.image location, ∑ z ∈ S.filter (fun z => location z = n),
            ((S.filter (fun w => location w = location z)).card : ℝ)*‖a z‖^2 := by
          apply sum_congr rfl
          intro n hn
          apply sum_congr rfl
          intro z hz
          rw [(mem_filter.mp hz).2]
        _ = _ := sum_fiberwise_of_maps_to (fun z hz => mem_image.mpr ⟨z,hz,rfl⟩) _

theorem fiber_interval_energy (S : Finset ι) (location : ι → ℕ) (a : ι → ℂ)
    {Q T : ℝ} (hQ : 0 < Q) (hT : 0 < T)
    (hS : ∀ z ∈ S, 0 < (location z : ℝ) ∧ (location z : ℝ) ≤ Q) :
    (∫ t : ℝ in Set.Icc (-T) T,
      ‖∑ z ∈ S, a z * phase (Real.log (location z)) t‖^2) ≤
      4 * Real.exp (1+1/4) * gaussianConstant * (T+Q) *
        ∑ z ∈ S, ((S.filter (fun w => location w = location z)).card : ℝ)*‖a z‖^2 := by
  simp_rw [← collect_polynomial]
  apply (logarithmic_interval_energy (S.image location) (collect S location a) hQ hT
    (by intro n hn; obtain ⟨z,hz,rfl⟩ := mem_image.mp hn; exact hS z hz)).trans
  exact mul_le_mul_of_nonneg_left (collect_energy S location a) (by
    have hg : 0 ≤ gaussianConstant := norm_nonneg _
    positivity)

end OrdinaryDirichletFiberMoments

end

end OAI

import Mathlib
import OAI.Combinatorics.KMedian.Sparse.SparsePreparedBudget

namespace OAI

section
section
namespace MetricKMedian.SparsePrepared
open Finset SparseOuterLaw
open SparseSignedPreparation (State)
variable {n m : ℕ}

theorem opening_probability (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ) (Δ : ℕ)
    (hc : ∀ e,0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e,0 ≤ q e) (g : ℚ)
    (δ : Fin n → ℝ) {γ B : ℝ} (hg : 0 < g) (hγ : 0 < γ)
    (heven : Even Δ) (hunit : g*(Δ:ℚ)=1) (hδ : ∀ j,0 ≤ δ j)
    (hmean : ∀ j,(g:ℝ)*(targetMean D q j:ℝ)=(1+γ)*δ j)
    (hsmall : ∀ j,(1+γ)*δ j ≤ 1/4)
    (hplan : (g:ℝ)*(((n:ℚ)*(Δ:ℚ)+(∑ e,SparseSignedPreparation.signed D c e*q e):ℚ):ℝ)=
      B-γ*∑ j,δ j) :
    1-4*(g:ℝ)*(1+γ)/γ ≤ (SparseOuterLaw.law D c q hc hq).realIndex.prob (fun a =>
      (g:ℝ)*(opening D c q Δ (SparseOuterLaw.law D c q hc hq).states[a.val]:ℝ) ≤ B+3*(g:ℝ)) := by
  classical
  apply (SparseOuterLaw.clipping_budget D c q g hc hq δ hg.le hγ hδ hmean hsmall).trans
  apply FiniteLaw.prob_mono
  intro a ha
  have hh0 := opening_le D c q Δ hc hq a
  have hh : (opening D c q Δ (SparseOuterLaw.law D c q hc hq).states[a.val]:ℝ) ≤
      (((n:ℚ)*(Δ:ℚ)+(∑ e,SparseSignedPreparation.signed D c e*q e):ℚ):ℝ)+3+
      ∑ j,(discarded D q Δ (SparseOuterLaw.law D c q hc hq).states[a.val] j:ℝ) := by
    exact_mod_cast hh0
  have hhg := mul_le_mul_of_nonneg_left hh (show (0:ℝ) ≤ g by exact_mod_cast hg.le)
  have hdiscard : (g:ℝ)*(∑ j,(discarded D q Δ (SparseOuterLaw.law D c q hc hq).states[a.val] j:ℝ))=
      ∑ j,((deficit D q g (SparseOuterLaw.law D c q hc hq).states[a.val] j:ℝ)-
        min (deficit D q g (SparseOuterLaw.law D c q hc hq).states[a.val] j:ℝ) (1/2)) := by
    rw [mul_sum]
    exact sum_congr rfl (fun j _ => discarded_mass D q Δ _ j hg heven hunit)
  rw [mul_add,mul_add,hplan,hdiscard] at hhg
  linarith only [hhg,ha]

theorem total_deficit_identity (D : Fin m → Finset (Fin n)) (q : Fin m → ℚ) (Δ : ℕ)
    (z : State n m) (j : Fin n) {g : ℚ} (hg : 0 < g) (heven : Even Δ)
    (hunit : g*(Δ:ℚ)=1) :
    (g:ℝ)*(total D q Δ z j:ℝ)=1-min (deficit D q g z j:ℝ) (1/2) := by
  have he : (deficit D q g z j:ℝ)=(g:ℝ)*((∑ e,activationCount D q z e j):ℕ) := by
    simp only [deficit,Rat.cast_mul,Rat.cast_sum,Nat.cast_sum,← activationCount_cast,
      Rat.cast_natCast]
  rw [he]
  exact (Preparation.grid_clip (by exact_mod_cast hg) heven (by exact_mod_cast hunit)
    (∑ e,activationCount D q z e j)).2.1.symm

theorem total_deviation (D : Fin m → Finset (Fin n)) (c q : Fin m → ℚ) (Δ : ℕ)
    (hc : ∀ e,0 ≤ c e ∧ c e ≤ 1) (hq : ∀ e,0 ≤ q e) (g : ℚ)
    (p δ : Fin n → ℝ) {γ : ℝ} (hg : 0 < g) (hγ : 0 ≤ γ)
    (heven : Even Δ) (hunit : g*(Δ:ℚ)=1) (hδ : ∀ j,0 ≤ δ j)
    (hδhalf : ∀ j,δ j ≤ 1/2) (hp : ∀ j,p j+δ j=1)
    (hmean : ∀ j,(g:ℝ)*(targetMean D q j:ℝ)=(1+γ)*δ j) (j : Fin n) :
    (SparseOuterLaw.law D c q hc hq).realIndex.expect (fun a =>
      |(g:ℝ)*(total D q Δ (SparseOuterLaw.law D c q hc hq).states[a.val] j:ℝ)-p j|) ≤
      γ*δ j+Real.sqrt ((g:ℝ)*(1+γ)*δ j) := by
  have hvar := SparseOuterLaw.deficit_variance D c q g hc hq j
  have he : (g:ℝ)^2*(targetMean D q j:ℝ)=(g:ℝ)*(1+γ)*δ j := by
    rw [pow_two,mul_assoc,hmean]
    ring
  rw [he] at hvar
  have hh := FiniteLaw.rescaling_noise (SparseOuterLaw.law D c q hc hq).realIndex
    (fun a => (deficit D q g (SparseOuterLaw.law D c q hc hq).states[a.val] j:ℝ))
    (hδ j) (hδhalf j) hγ (show (0:ℝ) ≤ g by exact_mod_cast hg.le)
    ((SparseOuterLaw.deficit_mean D c q g hc hq j).trans (hmean j)) hvar
  apply le_trans (le_of_eq ?_) hh
  apply FiniteLaw.expect_congr_support
  intro a _
  rw [total_deficit_identity D q Δ _ j hg heven hunit]
  congr 1
  linarith only [hp j]

end MetricKMedian.SparsePrepared
end
end

end OAI

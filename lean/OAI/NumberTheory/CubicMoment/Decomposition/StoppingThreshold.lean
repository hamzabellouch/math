import OAI.NumberTheory.CubicMoment.Estimates.GeometricStoppingKernel

namespace OAI

/-! The exact no-stop/stopped split. The original product kernel may
contain a sharp norm cutoff; no continuity is required. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def geometricStoppedElement (ρ X R Z : ℝ) (ψ : ℝ → ℝ) (w : ℝ)
    (K : Eisenstein → ℂ) (n : Eisenstein) : ℂ :=
  ∑ q ∈ stoppingLabelBox ρ X,
    ∑ t ∈ (primeBin (primaryPrimeFactors n) (geometricPrimeBin ρ X) q.1).powersetCard q.2.1,
      if (primeBin (stoppingRemainder (primaryPrimeFactors n) (geometricPrimeBin ρ X) q.1 t)
            (geometricPrimeBin ρ X) q.1).card = q.2.2 ∧
          (R*primeSurrogate (stoppingSelected (primaryPrimeFactors n)
              (geometricPrimeBin ρ X) q.1 t) (geometricPrimeBin ρ X) (geometricBinLower ρ X)/
              geometricBinLower ρ X q.1 < Z ∧
            Z ≤ R*primeSurrogate (stoppingSelected (primaryPrimeFactors n)
              (geometricPrimeBin ρ X) q.1 t) (geometricPrimeBin ρ X) (geometricBinLower ρ X)) then
        (Nat.choose (q.2.1+q.2.2) q.2.1:ℂ)⁻¹ *
          (cutoffMoebius ψ w (∏ p ∈ stoppingSelected (primaryPrimeFactors n)
              (geometricPrimeBin ρ X) q.1 t, p) *
            cutoffMoebius ψ w (∏ p ∈ stoppingRemainder (primaryPrimeFactors n)
              (geometricPrimeBin ρ X) q.1 t, p)) *
          K ((∏ p ∈ stoppingSelected (primaryPrimeFactors n) (geometricPrimeBin ρ X) q.1 t, p)*
            (∏ p ∈ stoppingRemainder (primaryPrimeFactors n) (geometricPrimeBin ρ X) q.1 t, p))
      else 0

lemma stoppingSelected_surrogate_le (s : Finset Eisenstein)
    (bin : Eisenstein → ℕ) (ell : ℕ → ℝ) (hell : ∀ j, 1 ≤ ell j)
    {j : ℕ} {t : Finset Eisenstein} (ht : t ⊆ primeBin s bin j) :
    primeSurrogate (stoppingSelected s bin j t) bin ell ≤ primeSurrogate s bin ell := by
  exact Finset.prod_le_prod_of_subset_of_one_le₀ (stoppingSelected_subset ht)
    (fun p _ => zero_le_one.trans (hell (bin p))) (fun p _ _ => hell (bin p))

/-- If the entire original factor set is below the threshold, every
putative stopping label contributes zero individually. -/
lemma geometricStoppedElement_eq_zero {ρ X R Z : ℝ} (hρ : 1 ≤ ρ) (hR : 0 ≤ R)
    (ψ : ℝ → ℝ) (w : ℝ) (K : Eisenstein → ℂ) (n : Eisenstein)
    (hbelow : R*primeSurrogate (primaryPrimeFactors n)
      (geometricPrimeBin ρ X) (geometricBinLower ρ X) < Z) :
    geometricStoppedElement ρ X R Z ψ w K n = 0 := by
  apply Finset.sum_eq_zero
  intro q _hq
  apply Finset.sum_eq_zero
  intro t ht
  apply ite_eq_right
  intro hc
  have hs := stoppingSelected_surrogate_le (primaryPrimeFactors n)
    (geometricPrimeBin ρ X) (geometricBinLower ρ X)
    (fun j => one_le_pow₀ hρ) (Finset.mem_powersetCard.mp ht).1
  exact (not_lt_of_ge (hc.2.2.trans (mul_le_mul_of_nonneg_left hs hR))) hbelow

/-- Unconditional in the end-crossing condition: the actual complete
label sum is exactly the original term times its stopping indicator. -/
theorem geometricStoppedElement_exact {n : Eisenstein} (hn : primary n)
    (hs : Squarefree n) {ρ X : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    (hX : 1 ≤ X) (hnorm : norm n ≤ X) {R Z : ℝ} (hR : 0 < R) (hstart : R < Z)
    (ψ : ℝ → ℝ) (w : ℝ) (K : Eisenstein → ℂ) :
    geometricStoppedElement ρ X R Z ψ w K n =
      if Z ≤ R*primeSurrogate (primaryPrimeFactors n)
          (geometricPrimeBin ρ X) (geometricBinLower ρ X) then
        cutoffMoebius ψ w n*K n else 0 := by
  by_cases hend : Z ≤ R*primeSurrogate (primaryPrimeFactors n)
      (geometricPrimeBin ρ X) (geometricBinLower ρ X)
  · rw [ite_eq_left hend]
    exact geometric_label_stopping_kernel hn hs hρ hρ₂ hX hnorm hR hstart hend ψ w K
  · rw [ite_eq_right hend]
    exact geometricStoppedElement_eq_zero hρ.le hR.le ψ w K n (lt_of_not_ge hend)

theorem stopping_threshold_split {n : Eisenstein} (hn : primary n)
    (hs : Squarefree n) {ρ X : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    (hX : 1 ≤ X) (hnorm : norm n ≤ X) {R Z : ℝ} (hR : 0 < R) (hstart : R < Z)
    (ψ : ℝ → ℝ) (w : ℝ) (K : Eisenstein → ℂ) :
    cutoffMoebius ψ w n*K n =
      (if R*primeSurrogate (primaryPrimeFactors n)
          (geometricPrimeBin ρ X) (geometricBinLower ρ X) < Z then
        cutoffMoebius ψ w n*K n else 0) + geometricStoppedElement ρ X R Z ψ w K n := by
  rw [geometricStoppedElement_exact hn hs hρ hρ₂ hX hnorm hR hstart]
  by_cases h : Z ≤ R*primeSurrogate (primaryPrimeFactors n)
      (geometricPrimeBin ρ X) (geometricBinLower ρ X)
  · simp only [h,not_lt_of_ge h,ite_true,ite_false,zero_add]
  · simp only [h,lt_of_not_ge h,ite_true,ite_false,add_zero]

/-- The actual finite coefficient sum splits into the un-stopped part
and the complete stopping-label sum, with the same kernel on both. -/
theorem finite_stopping_threshold_split (S : Finset Eisenstein)
    {ρ X : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2) (hX : 1 ≤ X)
    (hS : ∀ n ∈ S, primary n ∧ Squarefree n ∧ norm n ≤ X)
    {R Z : ℝ} (hR : 0 < R) (hstart : R < Z)
    (ψ : ℝ → ℝ) (w : ℝ) (K : Eisenstein → ℂ) :
    (∑ n ∈ S, cutoffMoebius ψ w n*K n) =
      (∑ n ∈ S with R*primeSurrogate (primaryPrimeFactors n)
          (geometricPrimeBin ρ X) (geometricBinLower ρ X) < Z,
        cutoffMoebius ψ w n*K n) +
      ∑ n ∈ S, geometricStoppedElement ρ X R Z ψ w K n := by
  rw [Finset.sum_filter,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  exact stopping_threshold_split (hS n hn).1 (hS n hn).2.1 hρ hρ₂ hX
    (hS n hn).2.2 hR hstart ψ w K

end CubicFirstMoment

end

end OAI

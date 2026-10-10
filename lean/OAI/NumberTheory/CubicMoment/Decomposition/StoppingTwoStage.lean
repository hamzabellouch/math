import OAI.NumberTheory.CubicMoment.Decomposition.StoppingPrefixCrossing
import OAI.NumberTheory.CubicMoment.Decomposition.StoppingThreshold

namespace OAI

/-! Exact two-stage stopping, first above a bin boundary and then after
failure of that high-prime stage. The original kernel and inverse
binomial coefficients remain unchanged. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def geometricStoppingLabel (ρ X R Z : ℝ) (ψ : ℝ → ℝ) (w : ℝ)
    (K : Eisenstein → ℂ) (n : Eisenstein) (q : ℕ × ℕ × ℕ) : ℂ :=
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


lemma geometricStoppedElement_eq_labels (ρ X R Z : ℝ) (ψ : ℝ → ℝ) (w : ℝ)
    (K : Eisenstein → ℂ) (n : Eisenstein) :
    geometricStoppedElement ρ X R Z ψ w K n =
      ∑ q ∈ stoppingLabelBox ρ X, geometricStoppingLabel ρ X R Z ψ w K n q := rfl

def geometricHighStoppedElement (ρ X R Z : ℝ) (h : ℕ) (ψ : ℝ → ℝ) (w : ℝ)
    (K : Eisenstein → ℂ) (n : Eisenstein) : ℂ :=
  ∑ q ∈ (stoppingLabelBox ρ X).filter (fun q => q.1 < h),
    geometricStoppingLabel ρ X R Z ψ w K n q

lemma geometricStoppingLabel_zero_boundary {ρ X R Z : ℝ} (hρ : 1 ≤ ρ) (hR : 0 ≤ R)
    (h : ℕ) (ψ : ℝ → ℝ) (w : ℝ) (K : Eisenstein → ℂ) (n : Eisenstein)
    {q : ℕ × ℕ × ℕ} (hq : q ∈ stoppingLabelBox ρ X)
    (hmiss : ¬ (q.1 < h ↔ Z ≤ R*primeSurrogate
      (primeBinPrefix (primaryPrimeFactors n) (geometricPrimeBin ρ X) h)
      (geometricPrimeBin ρ X) (geometricBinLower ρ X))) :
    geometricStoppingLabel ρ X R Z ψ w K n q = 0 := by
  apply Finset.sum_eq_zero
  intro t ht
  apply ite_eq_right
  intro hc
  exact hmiss (selected_crossing_before_prefix_iff (primaryPrimeFactors n)
    (geometricPrimeBin ρ X) (geometricBinLower ρ X)
    (fun j => one_le_pow₀ hρ) hR ht (Finset.mem_filter.mp hq).2 hc.2.1 hc.2.2)

theorem geometricHighStoppedElement_exact {n : Eisenstein} (hn : primary n)
    (hs : Squarefree n) {ρ X : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    (hX : 1 ≤ X) (hnorm : norm n ≤ X) {R Z : ℝ} (hR : 0 < R) (hstart : R < Z)
    (h : ℕ) (ψ : ℝ → ℝ) (w : ℝ) (K : Eisenstein → ℂ) :
    geometricHighStoppedElement ρ X R Z h ψ w K n =
      if Z ≤ R*primeSurrogate
        (primeBinPrefix (primaryPrimeFactors n) (geometricPrimeBin ρ X) h)
        (geometricPrimeBin ρ X) (geometricBinLower ρ X) then
          cutoffMoebius ψ w n*K n else 0 := by
  by_cases hh : Z ≤ R*primeSurrogate
      (primeBinPrefix (primaryPrimeFactors n) (geometricPrimeBin ρ X) h)
      (geometricPrimeBin ρ X) (geometricBinLower ρ X)
  · rw [ite_eq_left hh]
    have he : geometricHighStoppedElement ρ X R Z h ψ w K n =
        geometricStoppedElement ρ X R Z ψ w K n := by
      rw [geometricStoppedElement_eq_labels]
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro q hq hnot
      apply geometricStoppingLabel_zero_boundary hρ.le hR.le h ψ w K n hq
      intro hc
      exact hnot (Finset.mem_filter.mpr ⟨hq,hc.mpr hh⟩)
    rw [he,geometricStoppedElement_exact hn hs hρ hρ₂ hX hnorm hR hstart]
    apply ite_eq_left
    apply hh.trans
    apply mul_le_mul_of_nonneg_left _ hR.le
    exact Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.filter_subset _ _)
      (fun p _ => zero_le_one.trans (one_le_pow₀ hρ.le))
      (fun p _ _ => one_le_pow₀ hρ.le)
  · rw [ite_eq_right hh]
    apply Finset.sum_eq_zero
    intro q hq
    obtain ⟨hq,hj⟩ := Finset.mem_filter.mp hq
    apply geometricStoppingLabel_zero_boundary hρ.le hR.le h ψ w K n hq
    intro hc
    exact hh (hc.mp hj)

/-- Exact ordinary two-stage decomposition before any estimate. The
late term carries the failed-prefix condition on the selected divisor. -/
theorem two_stage_stopping_split {n : Eisenstein} (hn : primary n)
    (hs : Squarefree n) {ρ X : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    (hX : 1 ≤ X) (hnorm : norm n ≤ X) {R Q Z : ℝ} (hR : 0 < R)
    (hstart : R < Q) (hQZ : Q ≤ Z) (h : ℕ)
    (ψ : ℝ → ℝ) (w : ℝ) (K : Eisenstein → ℂ) :
    cutoffMoebius ψ w n*K n =
      (if R*primeSurrogate
          (primeBinPrefix (primaryPrimeFactors n) (geometricPrimeBin ρ X) h)
          (geometricPrimeBin ρ X) (geometricBinLower ρ X) < Q ∧
        R*primeSurrogate (primaryPrimeFactors n)
          (geometricPrimeBin ρ X) (geometricBinLower ρ X) < Z then
        cutoffMoebius ψ w n*K n else 0) +
      geometricHighStoppedElement ρ X R Q h ψ w K n +
      (if R*primeSurrogate
          (primeBinPrefix (primaryPrimeFactors n) (geometricPrimeBin ρ X) h)
          (geometricPrimeBin ρ X) (geometricBinLower ρ X) < Q then
        geometricStoppedElement ρ X R Z ψ w K n else 0) := by
  rw [geometricHighStoppedElement_exact hn hs hρ hρ₂ hX hnorm hR hstart,
    geometricStoppedElement_exact hn hs hρ hρ₂ hX hnorm hR (hstart.trans_le hQZ)]
  by_cases hh : R*primeSurrogate
      (primeBinPrefix (primaryPrimeFactors n) (geometricPrimeBin ρ X) h)
      (geometricPrimeBin ρ X) (geometricBinLower ρ X) < Q
  · have hnh : ¬ Q ≤ R*primeSurrogate
        (primeBinPrefix (primaryPrimeFactors n) (geometricPrimeBin ρ X) h)
        (geometricPrimeBin ρ X) (geometricBinLower ρ X) := not_le.mpr hh
    by_cases hz : Z ≤ R*primeSurrogate (primaryPrimeFactors n)
        (geometricPrimeBin ρ X) (geometricBinLower ρ X)
    · simp only [hh,hnh,hz,not_lt_of_ge hz,true_and,ite_true,ite_false,zero_add,add_zero]
    · simp only [hh,hnh,hz,lt_of_not_ge hz,true_and,ite_true,ite_false,add_zero]
  · have hh' := le_of_not_gt hh
    simp only [hh,hh',false_and,ite_true,ite_false,zero_add,add_zero]

/-- The literal finite rough-Moebius sum has the same two-stage split,
with the product kernel unchanged in all three terms. -/
theorem finite_two_stage_stopping_split (S : Finset Eisenstein)
    {ρ X : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2) (hX : 1 ≤ X)
    (hS : ∀ n ∈ S, primary n ∧ Squarefree n ∧ norm n ≤ X)
    {R Q Z : ℝ} (hR : 0 < R) (hstart : R < Q) (hQZ : Q ≤ Z)
    (h : ℕ) (ψ : ℝ → ℝ) (w : ℝ) (K : Eisenstein → ℂ) :
    (∑ n ∈ S, cutoffMoebius ψ w n*K n) =
      (∑ n ∈ S with R*primeSurrogate
          (primeBinPrefix (primaryPrimeFactors n) (geometricPrimeBin ρ X) h)
          (geometricPrimeBin ρ X) (geometricBinLower ρ X) < Q ∧
        R*primeSurrogate (primaryPrimeFactors n)
          (geometricPrimeBin ρ X) (geometricBinLower ρ X) < Z,
        cutoffMoebius ψ w n*K n) +
      (∑ n ∈ S, geometricHighStoppedElement ρ X R Q h ψ w K n) +
      ∑ n ∈ S with R*primeSurrogate
          (primeBinPrefix (primaryPrimeFactors n) (geometricPrimeBin ρ X) h)
          (geometricPrimeBin ρ X) (geometricBinLower ρ X) < Q,
        geometricStoppedElement ρ X R Z ψ w K n := by
  simp only [Finset.sum_filter,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  exact two_stage_stopping_split (hS n hn).1 (hS n hn).2.1 hρ hρ₂ hX
    (hS n hn).2.2 hR hstart hQZ h ψ w K

end CubicFirstMoment

end

end OAI

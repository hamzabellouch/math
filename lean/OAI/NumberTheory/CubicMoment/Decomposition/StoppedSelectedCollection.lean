import OAI.NumberTheory.CubicMoment.Decomposition.StoppedSelectedReindex

namespace OAI

/-! Exact collection of the selected-bin free-prime rows, and the
complementary norm cutoff forced by the lower endpoint of the prime bin. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma stoppedSelectedPrimeSet_subset (B ρ a b : ℝ) (j j₀ k h : ℕ) (Z Q : ℝ)
    (early : Bool) (r c e : Eisenstein) :
    stoppedSelectedPrimeSet B ρ a b j j₀ k h Z Q early r c e ⊆ primeCutoff B := by
  intro p hp
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp
    (Finset.mem_filter.mp hp).1).1).1).1

lemma selectedStopped_row_collection (B ρ a b w u : ℝ) (j j₀ k h : ℕ) (Z Q : ℝ)
    (early : Bool) (r v e : Eisenstein) :
    (∑ t ∈ selectedStoppedRowPairs B ρ a b j j₀ k h Z Q early r e,
      cutoffMoebius primeDetectorCutoff w (t.2*t.1)*normTwist u (r*(t.2*t.1))*
        cubicSymbol (r*(t.2*t.1)) v) =
      ∑ c ∈ (primaryElementBall B).filter (fun c => Squarefree (r*c) ∧ IsCoprime (r*c) e),
        stoppedSelectedPrimeRow B ρ (a/norm (r*c)) (b/norm (r*c)) w u
          j j₀ k h Z Q early r c v e := by
  unfold selectedStoppedRowPairs
  rw [Finset.sum_filter,Finset.sum_product,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro c hc
  by_cases hrc : Squarefree (r*c) ∧ IsCoprime (r*c) e
  · simp only [hrc.1,hrc.2,true_and,ite_true]
    unfold stoppedSelectedPrimeRow
    rw [←Finset.sum_filter,Finset.filter_mem_eq_of_subset
      (stoppedSelectedPrimeSet_subset B ρ (a/norm (r*c)) (b/norm (r*c))
        j j₀ k h Z Q early r c e)]
  · have hzero (p : Eisenstein) :
        ¬(Squarefree (r*c) ∧ IsCoprime (r*c) e ∧
          p ∈ stoppedSelectedPrimeSet B ρ (a/norm (r*c)) (b/norm (r*c))
            j j₀ k h Z Q early r c e) := fun hp => hrc ⟨hp.1,hp.2.1⟩
    simp only [hzero,ite_false,Finset.sum_const_zero,hrc]

lemma selectedStopped_complement_bound {B ρ a b : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    {j j₀ k h : ℕ} (hj : j < geometricBinCount ρ B) {Z Q : ℝ} {early : Bool}
    {r c e p : Eisenstein} (hr : primary r) (hc : primary c)
    (hp : p ∈ stoppedSelectedPrimeSet B ρ (a/norm (r*c)) (b/norm (r*c))
      j j₀ k h Z Q early r c e) :
    norm (r*c) ≤ b/geometricBinLower ρ B j := by
  have hpP := stoppedSelectedPrimeSet_primary B ρ _ _ j j₀ k h Z Q early r c e hp
  have hpB := (mem_primeCutoff.mp (stoppedSelectedPrimeSet_subset B ρ _ _ j j₀ k h
    Z Q early r c e hp)).2
  have hrow := (Finset.mem_filter.mp hp).1
  have hbin := (Finset.mem_filter.mp hrow).2.2
  have hint := (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hrow).1).1).2
  have hnorm := (geometricPrimeBin_eq_iff hρ hρ₂ hj hpP hpB).mp hbin
  have hnrc : 0 < norm (r*c) := norm_pos_of_ne_zero
    (mul_ne_zero (primary_ne_zero hr) (primary_ne_zero hc))
  have hnb : norm p*norm (r*c) ≤ b := (le_div_iff₀ hnrc).mp hint.2
  apply (le_div_iff₀ (zero_lt_one.trans (geometricBinLower_gt_one hρ hj))).mpr
  calc
    norm (r*c)*geometricBinLower ρ B j ≤ norm (r*c)*norm p :=
      mul_le_mul_of_nonneg_left hnorm.1 hnrc.le
    _ ≤ b := by simpa only [mul_comm] using hnb

lemma selectedStopped_row_eq_zero {B ρ a b w u : ℝ} (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    {j j₀ k h : ℕ} (hj : j < geometricBinCount ρ B) {Z Q : ℝ} {early : Bool}
    {r c v e : Eisenstein} (hr : primary r) (hc : primary c)
    (hbig : b/geometricBinLower ρ B j < norm (r*c)) :
    stoppedSelectedPrimeRow B ρ (a/norm (r*c)) (b/norm (r*c)) w u
      j j₀ k h Z Q early r c v e = 0 := by
  unfold stoppedSelectedPrimeRow
  apply Finset.sum_eq_zero
  intro p hp
  exact (not_lt_of_ge (selectedStopped_complement_bound hρ hρ₂ hj hr hc hp) hbig).elim

theorem selectedStopped_original_rows (B ρ a b w u : ℝ) (j j₀ k h : ℕ) (Z Q : ℝ)
    (early : Bool) (r v e : Eisenstein) (hr : primary r) (hbB : b ≤ B) :
    (∑ d ∈ selectedStoppedDivisorSet B ρ a b j j₀ k h Z Q early r e,
      cutoffMoebius primeDetectorCutoff w d*normTwist u (r*d)*cubicSymbol (r*d) v) =
      ∑ c ∈ (primaryElementBall B).filter (fun c => Squarefree (r*c) ∧ IsCoprime (r*c) e),
        stoppedSelectedPrimeRow B ρ (a/norm (r*c)) (b/norm (r*c)) w u
          j j₀ k h Z Q early r c v e := by
  rw [selectedStopped_sum_reindex B ρ a b j j₀ k h Z Q early r e hr hbB]
  exact selectedStopped_row_collection B ρ a b w u j j₀ k h Z Q early r v e

end CubicFirstMoment

end

end OAI

import Mathlib
import OAI.Combinatorics.TriangleRemoval.Probability.HistoryLawPathSupport
import OAI.Combinatorics.TriangleRemoval.Process.RelativeSafeCopyIncrement

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open scoped BigOperators
open scoped BigOperators ENNReal Classical
open Filter MeasureTheory
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

noncomputable def relativeScaleBudget (s : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ k ∈ Finset.range j, (s k / s (k+1) - 1)

theorem history_relative_loss_counter {α : Type*} [Fintype α]
    (K : ℕ → α → PMF α) (f : α → ℝ) (s : ℕ → ℝ)
    (T j : ℕ) (hj : j ≤ T) (ω : History α T) :
    historyCounter (fun k a => (f a-pmfMean (K k a) f)/s (k+1)) T j ω =
      f (ω (historyIndex T 0))/s 0 - f (ω (historyIndex T j))/s j +
      (∑ k ∈ Finset.range j, f (ω (historyIndex T k)) * (1/s (k+1)-1/s k)) +
      historyNoise K (fun k a => f a/s k) T j ω := by
  unfold historyCounter historyNoise historyIncrement
  simp only [Nat.min_eq_left hj,div_eq_mul_inv,pmfMean_mul_const]
  have he : (∑ k ∈ Finset.range j,
      (f (ω (historyIndex T k))-pmfMean (K k (ω (historyIndex T k))) f) * (s (k+1))⁻¹) =
    (∑ k ∈ Finset.range j,
      (f (ω (historyIndex T k)) * (s k)⁻¹-
        f (ω (historyIndex T (k+1))) * (s (k+1))⁻¹)) +
    (∑ k ∈ Finset.range j,
      f (ω (historyIndex T k)) * (1*(s (k+1))⁻¹-1*(s k)⁻¹)) +
    (∑ k ∈ Finset.range j,
      (f (ω (historyIndex T (k+1))) * (s (k+1))⁻¹-
        pmfMean (K k (ω (historyIndex T k))) f * (s (k+1))⁻¹)) := by
    rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [he,Finset.sum_range_sub']

lemma relativeScaleBudget_nonneg (s : ℕ → ℝ) (T : ℕ)
    (hs : ∀ j ≤ T, 0 < s j) (hdec : ∀ j < T, s (j+1) ≤ s j) :
    0 ≤ relativeScaleBudget s T := by
  apply Finset.sum_nonneg
  intro j hj
  have hjT := Finset.mem_range.mp hj
  exact sub_nonneg.mpr ((one_le_div (hs (j+1) (by omega))).mpr
    (hdec j (Finset.mem_range.mp hj)))

lemma relativeScaleBudget_mono (s : ℕ → ℝ) (T : ℕ)
    (hs : ∀ j ≤ T, 0 < s j) (hdec : ∀ j < T, s (j+1) ≤ s j)
    {j : ℕ} (hj : j ≤ T) : relativeScaleBudget s j ≤ relativeScaleBudget s T := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hj)
  intro k hk _
  exact sub_nonneg.mpr ((one_le_div (hs (k+1) (by have := Finset.mem_range.mp hk; omega))).mpr
    (hdec k (Finset.mem_range.mp hk)))

theorem relativeCopyCounter_le {n : ℕ} {α : Type*} [Fintype α]
    (required : α → Graph n) (T j : ℕ) (hj : j ≤ T) (L s : ℕ → ℝ)
    (c B : ℝ) (hc : 0 ≤ c) (hB : 0 ≤ B)
    (hs : ∀ k ≤ T, 0 < s k) (hdec : ∀ k < T, s (k+1) ≤ s k)
    (hjump : ∀ k < T, 3*L k/s (k+1) ≤ c)
    (ω : History (Graph n) T)
    (hcount : ∀ k < j, copyCount required (ω (historyIndex T k)) ≤ B*s k) :
    historyCounter (relativeCopyVarianceRate required L s) T j ω ≤
      c*(copyCount required (ω (historyIndex T 0))/s 0 + B*relativeScaleBudget s T +
        historyNoise (fun _ => step) (fun k H => copyCount required H/s k) T j ω) := by
  have hsum : historyCounter (relativeCopyVarianceRate required L s) T j ω ≤
      c*historyCounter (fun k H =>
        (copyCount required H-pmfMean (step H) (copyCount required))/s (k+1)) T j ω := by
    unfold historyCounter
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have hkj : k < j := by simpa only [Nat.min_eq_left hj,Finset.mem_range] using hk
    have hkT : k < T := hkj.trans_le hj
    have ht : 0 ≤ copyCount required (ω (historyIndex T k))-
        pmfMean (step (ω (historyIndex T k))) (copyCount required) := by
      apply sub_nonneg.mpr
      rw [← pmfMean_const (step (ω (historyIndex T k)))
        (copyCount required (ω (historyIndex T k)))]
      apply pmfMean_mono
      intro H hH
      exact copyCount_mono required (step_support_subset hH)
    calc
      _ = (3*L k/s (k+1))*
          ((copyCount required (ω (historyIndex T k))-
          pmfMean (step (ω (historyIndex T k))) (copyCount required))/s (k+1)) := by
        unfold relativeCopyVarianceRate copyVarianceRate
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (hjump k hkT)
        (div_nonneg ht (hs (k+1) (by omega)).le)
  apply hsum.trans
  rw [history_relative_loss_counter _ _ _ _ _ hj]
  apply mul_le_mul_of_nonneg_left _ hc
  have hnon : 0 ≤ copyCount required (ω (historyIndex T j))/s j :=
    div_nonneg (copyCount_nonneg _ _) (hs j hj).le
  have hbudget : (∑ k ∈ Finset.range j,
      copyCount required (ω (historyIndex T k)) * (1/s (k+1)-1/s k)) ≤
        B*relativeScaleBudget s T := by
    calc
      _ ≤ B*relativeScaleBudget s j := by
        unfold relativeScaleBudget
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro k hk
        have hkj := Finset.mem_range.mp hk
        have hkT : k < T := hkj.trans_le hj
        have hsk := hs k (by omega)
        have hsk1 := hs (k+1) (by omega)
        calc
          _ ≤ (B*s k)*(1/s (k+1)-1/s k) := by
            apply mul_le_mul_of_nonneg_right (hcount k hkj)
            exact sub_nonneg.mpr (one_div_le_one_div_of_le hsk1 (hdec k hkT))
          _ = _ := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left (relativeScaleBudget_mono s T hs hdec hj) hB
  linarith

end SharpTerminalLeave

end

end OAI

import OAI.Analysis.LipschitzHilbert.Fourier.DyadicLineFiniteTail
import OAI.Analysis.LipschitzHilbert.Estimates.CountableCarleson

namespace OAI

/-! Uniform tails for countably many actual maximal dyadic occurrences. -/

noncomputable section

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace LipschitzHilbert.DyadicLineGrid

theorem maximal_bad_countable_tail {ι B : Type*} [Countable ι]
    (q top : ℤ) (f : B → ℝ → ℝ) (bin : ι → B) (level pos : ι → ℤ)
    (hunique : ∀ i j, bin i = bin j → level i = level j → pos i = pos j → i = j)
    {β C : ℝ} (hβ : 0 < β) (hC : 0 < C)
    (hmax : ∀ i, MaximalBad q top (Bad q (f (bin i)) β) (level i) (pos i))
    (hf : ∀ b, Measurable (f b)) (hbound : ∀ b x, 0 ≤ f b x ∧ f b x ≤ 1)
    (hsum : ∀ s : Finset B, ∀ x, (∑ b ∈ s, f b x) ≤ C)
    (rootLevel rootPos : ℤ)
    (hsub : ∀ i, cell q (level i) (pos i) ⊆ cell q rootLevel rootPos)
    {lambda : ℝ} (hlambda : 0 ≤ lambda) :
    volume.real ({x | ENNReal.ofReal lambda < occurrenceCount (fun i => cell q (level i) (pos i)) x} ∩
      cell q rootLevel rootPos) ≤
      2 * scale rootLevel * Real.exp (-lambda / (2 * (C / β))) := by
  classical
  apply occurrenceCount_root_tail_of_finite _ volume
    (fun i => cell_measurable q (level i) (pos i)) measure_Ico_lt_top.ne hlambda
    (mul_nonneg (mul_nonneg (by norm_num) (scale_pos rootLevel).le) (Real.exp_pos _).le)
  intro s
  have ht := maximal_bad_finite_tail (ι := s) q top f (fun i => bin i.1)
    (fun i => level i.1) (fun i => pos i.1)
    (fun i j hb hl hp => Subtype.ext (hunique i.1 j.1 hb hl hp)) hβ hC
    (fun i => hmax i.1) hf hbound hsum rootLevel rootPos (fun i => hsub i.1) lambda
  have heq (x : ℝ) : laminarCount (fun i : s => cell q (level i.1) (pos i.1)) x =
      finiteOccurrenceCount (fun i => cell q (level i) (pos i)) s x := by
    exact (Finset.sum_subtype s (fun _ => Iff.rfl)
      (fun i => (cell q (level i) (pos i)).indicator (1 : ℝ → ℝ) x)).symm
  simp_rw [heq] at ht
  simpa only [cell] using ht

end LipschitzHilbert.DyadicLineGrid

end

end OAI

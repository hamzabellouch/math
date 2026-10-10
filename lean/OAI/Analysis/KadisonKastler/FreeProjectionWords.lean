import OAI.Analysis.KadisonKastler.ModelWordExpansion
import OAI.Analysis.KadisonKastler.FreeModelCutBounds
import OAI.Analysis.KadisonKastler.FactorialCuts
import OAI.Analysis.KadisonKastler.FreeWordConstants
import OAI.Analysis.KadisonKastler.ModelScalarRestoration

namespace OAI

/-!
# Summing the cuts of free diagonal projection words

The estimates here concern the structural free diagonal model itself.
Every cut is factored through the ordered-tuple matrix, and the factorial
factors in the preservation cuts are summed before scalar restoration.
-/

namespace KadisonKastler.FreeDiagonalModel

open Finset

noncomputable section

variable {ι α H : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M : FreeDiagonalModel ι α H) (W : Finset α)

theorem norm_sum_noPreservationWordCut_le {r k : ℕ} (hW : W.card = r)
    (position : Fin r → ι) (hk : k ≤ r) :
    ‖∑ t : OrderedLabelTuple W r, M.noPreservationWordCut W position t k‖ ≤
      Real.sqrt (r.factorial : ℝ) / Real.sqrt ((Fintype.card α : ℝ) ^ r) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [M.sum_noPreservationWordCut_eq]
  exact M.norm_noPreservationSum_le W hW _ _

theorem norm_sum_preservationWordCut_le {r k : ℕ} (hW : W.card = r)
    (position : Fin r → ι) (hk : k < r) :
    ‖∑ t : OrderedLabelTuple W r, M.preservationWordCut W position t k‖ ≤
      (Real.sqrt (k.factorial : ℝ) * Real.sqrt (((r - 1) - k).factorial : ℝ)) *
        (1 + (r : ℝ) / Fintype.card α) /
          Real.sqrt ((Fintype.card α : ℝ) ^ (r - 1)) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hk)
  rw [M.sum_preservationWordCut_eq]
  have h := M.norm_preservationSum_le W hW
    (position ∘ cutPrefixIndex k q) (position (cutMiddleIndex k q))
    (position ∘ cutSuffixIndex k q)
  have hs : k + 1 + q - 1 = k + q := by omega
  simp only [hs, Nat.add_sub_cancel_left]
  convert h using 1
  push_cast
  ring

/-- All cuts without a preserved letter have one common denominator. -/
theorem norm_noPreservationCuts_le {r : ℕ} (hW : W.card = r)
    (position : Fin r → ι) :
    ‖∑ k ∈ range (r + 1), ∑ t : OrderedLabelTuple W r,
      M.noPreservationWordCut W position t k‖ ≤
      (r + 1 : ℝ) * Real.sqrt (r.factorial : ℝ) /
        Real.sqrt ((Fintype.card α : ℝ) ^ r) := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _k ∈ range (r + 1),
        Real.sqrt (r.factorial : ℝ) / Real.sqrt ((Fintype.card α : ℝ) ^ r) := by
      apply sum_le_sum
      intro k hk
      exact M.norm_sum_noPreservationWordCut_le W hW position
        (Nat.le_of_lt_succ (mem_range.mp hk))
    _ = _ := by simp only [sum_const, card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]; ring

/-- Summing preservation cuts retains the reciprocal-binomial factor,
which is uniformly bounded independently of the word length. -/
theorem norm_preservationCuts_le {r : ℕ} (hr : 1 ≤ r) (hW : W.card = r)
    (position : Fin r → ι) :
    ‖∑ k ∈ range r, ∑ t : OrderedLabelTuple W r,
      M.preservationWordCut W position t k‖ ≤
      (1 + (r : ℝ) / Fintype.card α) *
        (Real.sqrt ((r - 1).factorial : ℝ) /
          Real.sqrt ((Fintype.card α : ℝ) ^ (r - 1))) *
        (∑ k ∈ range r, 1 / Real.sqrt ((r - 1).choose k : ℝ)) := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ k ∈ range r,
        (Real.sqrt (k.factorial : ℝ) * Real.sqrt (((r - 1) - k).factorial : ℝ)) *
          (1 + (r : ℝ) / Fintype.card α) /
            Real.sqrt ((Fintype.card α : ℝ) ^ (r - 1)) := by
      apply sum_le_sum
      intro k hk
      exact M.norm_sum_preservationWordCut_le W hW position (mem_range.mp hk)
    _ = (∑ k ∈ range r,
        Real.sqrt (k.factorial : ℝ) * Real.sqrt (((r - 1) - k).factorial : ℝ)) *
          (1 + (r : ℝ) / Fintype.card α) /
            Real.sqrt ((Fintype.card α : ℝ) ^ (r - 1)) := by
      rw [← sum_div, ← sum_mul]
    _ = _ := by
      have he := sum_sqrt_factorial_products (r - 1)
      rw [Nat.sub_add_cancel hr] at he
      rw [he]
      ring

/-- The complete centered sum is bounded by its two families of cuts. -/
theorem norm_sum_centeredWord_le {r : ℕ} (hr : 1 ≤ r) (hW : W.card = r)
    (position : Fin r → ι) (hposition : Function.Injective position) :
    ‖∑ t : OrderedLabelTuple W r, M.centeredWord W position t‖ ≤
      (1 + (r : ℝ) / Fintype.card α) *
        (Real.sqrt ((r - 1).factorial : ℝ) /
          Real.sqrt ((Fintype.card α : ℝ) ^ (r - 1))) *
        (∑ k ∈ range r, 1 / Real.sqrt ((r - 1).choose k : ℝ)) +
      (r + 1 : ℝ) * Real.sqrt (r.factorial : ℝ) /
        Real.sqrt ((Fintype.card α : ℝ) ^ r) := by
  rw [M.sum_centeredWord_eq_cuts W position hposition]
  exact (norm_add_le _ _).trans
    ((add_le_add (M.norm_noPreservationCuts_le W hW position)
      (M.norm_preservationCuts_le W hr hW position)).trans_eq (add_comm _ _))

/-- The full distinct-label projection sum satisfies the constant-seven
bound. The dimension threshold depends only on the word length. -/
theorem norm_sum_distinct_projectionWord_le {r : ℕ} (hr : 1 ≤ r)
    (hd : freeWordThreshold r ≤ Fintype.card α) (hW : W.card = r)
    (position : Fin r → ι) (hposition : Function.Injective position) :
    ‖∑ t : OrderedLabelTuple W r, M.projectionWord position t.val‖ ≤
      7 * Real.sqrt ((r - 1).factorial : ℝ) /
        Real.sqrt ((Fintype.card α : ℝ) ^ (r - 1)) := by
  apply distinct_freeWord_constant_of_threshold hr hd
    (M.norm_preservationCuts_le W hr hW position)
    (M.norm_noPreservationCuts_le W hW position)
    (M.norm_sum_distinct_projectionWord_sub_centeredWord_le W (by omega)
      hW position hposition)
  calc
    _ = ‖(∑ t : OrderedLabelTuple W r, M.centeredWord W position t) +
        ((∑ t : OrderedLabelTuple W r, M.projectionWord position t.val) -
          ∑ t : OrderedLabelTuple W r, M.centeredWord W position t)‖ := by
      congr 1
      abel
    _ ≤ ‖∑ t : OrderedLabelTuple W r, M.centeredWord W position t‖ +
        ‖(∑ t : OrderedLabelTuple W r, M.projectionWord position t.val) -
          ∑ t : OrderedLabelTuple W r, M.centeredWord W position t‖ := norm_add_le _ _
    _ ≤ _ := by
      rw [M.sum_centeredWord_eq_cuts W position hposition]
      have h := norm_add_le
        (∑ k ∈ range (r + 1), ∑ t : OrderedLabelTuple W r,
          M.noPreservationWordCut W position t k)
        (∑ k ∈ range r, ∑ t : OrderedLabelTuple W r,
          M.preservationWordCut W position t k)
      linarith

end

end KadisonKastler.FreeDiagonalModel

end OAI

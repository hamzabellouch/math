import OAI.NumberTheory.TwoPoint.Bounds.FixedColumnWords
import OAI.NumberTheory.TwoPoint.Bounds.RunTransitionPaths

namespace OAI

/-! Nonzero actual word intervals force nonzero quotient-run coefficients. -/

namespace TwoPointCorrelations

open Finset

namespace ColumnWordPattern

variable {α : Type*}

/-- The coefficient sum of a constant column run cannot vanish when its
actual integer displacement does not vanish. -/
lemma constant_run_coefficient_ne_zero (w : ColumnWordPattern α) (h : ℕ)
    (value : α → ℕ) (a b : ℕ) (hab : a ≤ b) (hb : b ≤ w.length) (z : α)
    (hconst : ∀ t ∈ Ico a b, w.label t = z)
    (hnonzero : wordDisplacement h (wordSlice (w.word value) a b) ≠ 0) :
    (∑ t ∈ Ico a b, w.coefficient h t) ≠ 0 := by
  intro hz
  apply hnonzero
  rw [wordSlice_displacement h (w.word value) hab]
  change (∑ t ∈ Ico a b, wordStepDisplacement h (w.word value) t) = 0
  calc
    _ = ∑ t ∈ Ico a b, w.coefficient h t * (value z : ℤ) := by
      apply sum_congr rfl
      intro t ht
      rw [w.displacement h value t ((mem_Ico.mp ht).2.trans_le hb), hconst t ht]
    _ = (∑ t ∈ Ico a b, w.coefficient h t) * (value z : ℤ) := (sum_mul _ _ _).symm
    _ = 0 := by rw [hz, zero_mul]

lemma constant_run_real_coefficient_ne_zero (w : ColumnWordPattern α) (h : ℕ)
    (value : α → ℕ) (a b : ℕ) (hab : a ≤ b) (hb : b ≤ w.length) (z : α)
    (hconst : ∀ t ∈ Ico a b, w.label t = z)
    (hnonzero : wordDisplacement h (wordSlice (w.word value) a b) ≠ 0) :
    (∑ t ∈ Ico a b, (w.coefficient h t : ℝ)) ≠ 0 := by
  have hn := w.constant_run_coefficient_ne_zero h value a b hab hb z hconst hnonzero
  exact_mod_cast hn

/-- The manuscript's nonzero-subinterval conclusion supplies every scalar
non-reversal condition needed by the greedy regular-segment path. -/
theorem regular_segment_quotient_data [Fintype α]
    {ι : Type*} [DecidableEq ι]
    (w : ColumnWordPattern α) (h : ℕ) (value : α → ℕ)
    (D : Submodule ℝ (α → ℝ)) (anchor : ι → (α → ℝ) ⧸ D)
    (regularLabel : ι → α) (runLabel : ℕ → ι) (start len : ℕ)
    (hlen : 0 < len) (hend : start + len ≤ w.length)
    (hlabel : ∀ t ∈ Ico start (start + len), w.label t = regularLabel (runLabel t))
    (hline : ∀ t ∈ Ico start (start + len),
      ∃ c : ℝ, D.mkQ (formalDeparture w.label (fun j => (w.coefficient h j : ℝ)) t) =
        anchor (runLabel t) + c • D.mkQ (Pi.basisFun ℝ α (regularLabel (runLabel t))))
    (hnonzero : ∀ a b, start ≤ a → a < b → b ≤ start + len →
      wordDisplacement h (wordSlice (w.word value) a b) ≠ 0) :
    QuotientRunData D anchor regularLabel w.label (fun j => (w.coefficient h j : ℝ))
      start (runLabel start)
      (scanRunTransitions runLabel (start + 1) (len - 1) (runLabel start)) := by
  apply regular_segment_run_data D anchor regularLabel w.label
    (fun j => (w.coefficient h j : ℝ)) runLabel start len hlen hlabel hline
  intro a b i ha hab hb hconst
  exact w.constant_run_real_coefficient_ne_zero h value a b hab.le (hb.trans hend)
    (regularLabel i) hconst (hnonzero a b ha hab hb)

end ColumnWordPattern

end TwoPointCorrelations

end OAI

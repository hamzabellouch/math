import OAI.GroupTheory.PolycyclicRecognition.Algebra.SequenceSubexponential
import Mathlib.Order.Filter.AtTopBot.Finite

namespace OAI

/-! # Passing all profile data to the same sequence of good scales -/

namespace PolycyclicRecognition

open Filter

/-- Subexponential losses are unchanged on a subsequence tending to infinity. -/
theorem HasSubexponentialLowerBoundSeq.comp {scale f : ℕ → ℝ} {v : ℕ → ℕ}
    (hf : HasSubexponentialLowerBoundSeq scale f) (hv : Tendsto v atTop atTop) :
    HasSubexponentialLowerBoundSeq (scale ∘ v) (f ∘ v) :=
  fun ε hε => hv.eventually (hf ε hε)

theorem HasSubexponentialUpperBoundSeq.comp {scale f : ℕ → ℝ} {v : ℕ → ℕ}
    (hf : HasSubexponentialUpperBoundSeq scale f) (hv : Tendsto v atTop atTop) :
    HasSubexponentialUpperBoundSeq (scale ∘ v) (f ∘ v) :=
  fun ε hε => hv.eventually (hf ε hε)

/-- The eventual cell and slack conditions can hold at every retained index,
while the physical scales are strictly increasing. No interpolation of the
profiles or of the group laws is needed. -/
theorem exists_increasing_good_scale_subsequence {scale : ℕ → ℝ}
    (hscale : Tendsto scale atTop atTop) {P : ℕ → Prop} (hP : ∀ᶠ n in atTop, P n) :
    ∃ u : ℕ → ℕ, StrictMono u ∧ StrictMono (scale ∘ u) ∧ ∀ n, P (u n) := by
  obtain ⟨v, hv, hPv⟩ := extraction_of_eventually_atTop hP
  obtain ⟨w, hw, hsw⟩ := strictMono_subseq_of_tendsto_atTop (hscale.comp hv.tendsto_atTop)
  exact ⟨v ∘ w, hv.comp hw, hsw, fun n => hPv (w n)⟩

end PolycyclicRecognition

end OAI

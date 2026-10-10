import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Data.Nat.Find

namespace OAI

/-! # A diagonal index for countably many ultrafilter-large sets -/

namespace KadisonKastler

open Filter

noncomputable section

/-- The index grows along the free ultrafilter, while its corresponding
constraint holds at the chosen coordinate. -/
theorem exists_ultrafilter_diagonal_index (ω : Ultrafilter ℕ)
    (hω : (ω : Filter ℕ) ≤ atTop) (A : ℕ → Set ℕ) (hA : ∀ n, A n ∈ ω) :
    ∃ k : ℕ → ℕ, Tendsto k (ω : Filter ℕ) atTop ∧ ∀ᶠ j in (ω : Filter ℕ), j ∈ A (k j) := by
  classical
  let k : ℕ → ℕ := fun j => Nat.findGreatest (fun n => j ∈ A n) j
  refine ⟨k, ?_, ?_⟩
  · apply tendsto_atTop.mpr
    intro n
    filter_upwards [hA n, hω (eventually_ge_atTop n)] with j hj hjn
    exact Nat.le_findGreatest hjn hj
  · filter_upwards [hA 0] with j hj
    exact Nat.findGreatest_spec (P := fun n => j ∈ A n) (Nat.zero_le j) hj

end

end KadisonKastler

end OAI

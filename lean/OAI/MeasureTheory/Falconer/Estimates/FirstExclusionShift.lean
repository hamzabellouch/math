import OAI.MeasureTheory.Falconer.Measures.FirstExclusionMass

namespace OAI

/-! # Earlier-scale exclusions disappear from every later first-loss set -/

namespace Falconer
open Set MeasureTheory

variable {X : Type*}

theorem firstExclusion_shift_subset (E : ℕ → Set X) (j₀ n m : ℕ)
    (hm₀ : j₀ ≤ m) (hmn : m < j₀+n) :
    firstExclusion (fun i => E (j₀+i)) n ⊆ E (j₀+n) \ E m := by
  intro x hx
  refine ⟨hx.1,?_⟩
  intro hxm
  apply hx.2
  refine mem_iUnion₂.mpr ⟨m-j₀,Finset.mem_range.mpr (by omega),?_⟩
  simpa only [Nat.add_sub_of_le hm₀] using hxm

end Falconer

end OAI

import OAI.Combinatorics.MatrixRemoval.CanonicalCopyBound
import OAI.Combinatorics.MatrixRemoval.OrderedRepairDistance
import OAI.Combinatorics.MatrixRemoval.SequenceAssembly
import OAI.Combinatorics.MatrixRemoval.Consequence

namespace OAI

noncomputable section
namespace Problem348

theorem counterexample_sequence :
    ∀ h : ℕ, 1 ≤ h →
  let d : ℕ := 386 * h + 2
  let n : ℕ := d * 2 ^ h
  ∃ A : BinaryMatrix n,
    fixedDistance A ≥ 1 / ((d : ℝ) ^ 2) ∧
    (copyCount fixedH A : ℝ) / ((n : ℝ) ^ 132) ≤
      (1 / ((d : ℝ) ^ 2)) * (1 / ((2 : ℝ) ^ h)) := by
  apply SequenceAssembly.counterexample_sequence_of_integer_bounds
  intro h hh
  refine ⟨Construction.hostMatrix (OrderedHost.rowIndex h) (OrderedHost.columnIndex h), ?_,
    OrderedHost.canonical_copyCount_le h⟩
  intro B hfree
  exact OrderedHost.hammingDistance_ge hh B hfree

theorem no_polynomial_removal_bound :
    ∀ c C : ℝ, 0 < c → 0 < C →
  ∃ n : ℕ, 1 ≤ n ∧
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      ∃ A : BinaryMatrix n,
        fixedDistance A ≥ ε ∧
        (copyCount fixedH A : ℝ) <
          c * Real.rpow ε C * ((n : ℝ) ^ 132) := by
  exact no_polynomial_removal_bound_of_sequence counterexample_sequence

end Problem348

end

end OAI

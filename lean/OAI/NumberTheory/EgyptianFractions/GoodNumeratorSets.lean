import Mathlib

namespace OAI
noncomputable section

namespace Problem337

/-- Finite backwards construction, indexed first by the number of remaining
steps so that its recursion is structurally terminating. -/
private def goodNumeratorAux
    (X : ℕ → ℝ) (I : ℕ → Finset ℕ) (res : ℕ → ℕ → ℕ → ℕ) :
    ℕ → ℕ → Finset ℕ
  | 0, j => Finset.Icc 1 ⌊X j⌋₊
  | n + 1, j => by
      classical
      exact (Finset.Icc 1 ⌊X j⌋₊).filter (fun u =>
        u ∈ goodNumeratorAux X I res n (j + 1) ∨
        ∃ i ∈ I j, res j i u = 0 ∨ res j i u ∈ goodNumeratorAux X I res n (j + 1))

private theorem goodNumeratorAux_subset
    (X : ℕ → ℝ) (I : ℕ → Finset ℕ) (res : ℕ → ℕ → ℕ → ℕ) (n j : ℕ) :
    goodNumeratorAux X I res n j ⊆ Finset.Icc 1 ⌊X j⌋₊ := by
  cases n with
  | zero => exact Finset.Subset.refl _
  | succ n => exact Finset.filter_subset _ _

/-- The good numerator sets exist for arbitrary finite indexed residue maps.
No arithmetic distribution or analytic estimate is required for this recursion. -/
theorem exists_good_numerator_sets
    (d : ℕ) (X : ℕ → ℝ) (I : ℕ → Finset ℕ) (res : ℕ → ℕ → ℕ → ℕ) :
    ∃ G : ℕ → Finset ℕ,
      (∀ j ≤ d, G j ⊆ Finset.Icc 1 ⌊X j⌋₊) ∧
      G d = Finset.Icc 1 ⌊X d⌋₊ ∧
      (∀ j < d, ∀ u : ℕ, u ∈ G j ↔
        u ∈ Finset.Icc 1 ⌊X j⌋₊ ∧
        (u ∈ G (j + 1) ∨ ∃ i ∈ I j, res j i u = 0 ∨ res j i u ∈ G (j + 1))) := by
  classical
  let G : ℕ → Finset ℕ := fun j => goodNumeratorAux X I res (d - j) j
  refine ⟨G, fun j _ => goodNumeratorAux_subset X I res (d - j) j, ?_, ?_⟩
  · simp [G, goodNumeratorAux]
  · intro j hj u
    have hsub : d - j = (d - (j + 1)) + 1 := by omega
    change u ∈ goodNumeratorAux X I res (d - j) j ↔ _
    rw [hsub]
    simp only [goodNumeratorAux, Finset.mem_filter]
    rfl

end Problem337

end

end OAI

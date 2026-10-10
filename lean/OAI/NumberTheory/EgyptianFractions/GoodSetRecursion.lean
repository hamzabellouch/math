import Mathlib

namespace OAI
noncomputable section

namespace Problem337

/-- A finite backwards recursion, extended constantly beyond its terminal index. -/
def backwardFiniteSequence {α : Type*} (d : ℕ) (terminal : α)
    (step : ℕ → α → α) (j : ℕ) : α :=
  Nat.rec terminal (fun t a => step (d - (t + 1)) a) (d - j)

@[simp] theorem backwardFiniteSequence_terminal {α : Type*} (d : ℕ) (terminal : α)
    (step : ℕ → α → α) : backwardFiniteSequence d terminal step d = terminal := by
  simp [backwardFiniteSequence]

theorem backwardFiniteSequence_step {α : Type*} (d : ℕ) (terminal : α)
    (step : ℕ → α → α) {j : ℕ} (hj : j < d) :
    backwardFiniteSequence d terminal step j =
      step j (backwardFiniteSequence d terminal step (j + 1)) := by
  unfold backwardFiniteSequence
  have hdiff : d - j = (d - (j + 1)) + 1 := by omega
  conv_lhs => rw [hdiff]
  change step (d - (d - (j + 1) + 1)) _ = step j _
  have hindex : d - (d - (j + 1) + 1) = j := by omega
  rw [hindex]

/-- The exact finite good-set recurrence used in the residue descent always
has a solution. Bounds may be arbitrary; monotonicity is not needed here. -/
theorem exists_backward_good_sets (d : ℕ) (bound : ℕ → ℕ)
    (indices : ℕ → Finset ℕ) (residue : ℕ → ℕ → ℕ → ℕ) :
    ∃ G : ℕ → Finset ℕ,
      (∀ j ≤ d, G j ⊆ Finset.Icc 1 (bound j)) ∧
      G d = Finset.Icc 1 (bound d) ∧
      (∀ j < d, ∀ u : ℕ, u ∈ G j ↔
        u ∈ Finset.Icc 1 (bound j) ∧
          (u ∈ G (j + 1) ∨ ∃ i ∈ indices j,
            residue j i u = 0 ∨ residue j i u ∈ G (j + 1))) := by
  classical
  let step : ℕ → Finset ℕ → Finset ℕ := fun j next =>
    (Finset.Icc 1 (bound j)).filter (fun u =>
      u ∈ next ∨ ∃ i ∈ indices j, residue j i u = 0 ∨ residue j i u ∈ next)
  let G := backwardFiniteSequence d (Finset.Icc 1 (bound d)) step
  have hterminal : G d = Finset.Icc 1 (bound d) :=
    backwardFiniteSequence_terminal d _ step
  have hstep (j : ℕ) (hj : j < d) : G j = step j (G (j + 1)) :=
    backwardFiniteSequence_step d _ step hj
  refine ⟨G, ?_, hterminal, ?_⟩
  · intro j hj
    rcases lt_or_eq_of_le hj with hj | rfl
    · rw [hstep j hj]
      exact Finset.filter_subset _ _
    · rw [hterminal]
  · intro j hj u
    rw [hstep j hj]
    exact Finset.mem_filter

end Problem337

end

end OAI

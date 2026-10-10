import OAI.NumberTheory.Ostmann.Construction.FinalReassignments
import OAI.NumberTheory.Ostmann.Characters.AnchorOneSidedEdge

namespace OAI

/-! # Selecting the actual small-anchor interaction between two reassignments -/

namespace Ostmann

def anchorCodeEntry {n : ℕ} (α : Fin n → ℤ) (t : Fin n → Bool)
    (j : Fin n) (positive : Bool) : ℤ :=
  if positive then (finiteAnchorCode α t j).1 else (finiteAnchorCode α t j).2

theorem anchorCodeEntry_sign {n : ℕ} (α : Fin n → ℤ)
    (hα : ∀ j, α j = 1 ∨ α j = -1) (t : Fin n → Bool) (j : Fin n) (b : Bool) :
    anchorCodeEntry α t j b = 1 ∨ anchorCodeEntry α t j b = -1 := by
  have hp := copyPathParity_sign (finiteCopyPath t) j
  rcases hα j with ha | ha <;> rcases hp with hp | hp <;>
    cases hb : t j <;> cases b <;>
    simp [anchorCodeEntry, finiteAnchorCode, anchorSignPair, ha, hp, hb]

theorem distinct_anchor_code_entry {n : ℕ} (α : Fin n → ℤ) (t u : Fin n → Bool)
    (hne : finiteAnchorCode α t ≠ finiteAnchorCode α u) :
    ∃ j b, anchorCodeEntry α t j b ≠ anchorCodeEntry α u j b := by
  by_contra h
  push Not at h
  apply hne
  funext j
  apply Prod.ext
  · exact h j true
  · exact h j false

/-- The small anchor suffices at the final stage because the constructed
reassignments preserve final parity. The forward exponent is exactly ±2 and
the reverse exponent is zero. -/
theorem final_reassignment_interaction {n m : ℕ}
    (α : Fin (n + 1) → ℤ) (hα : ∀ j, α j = 1 ∨ α j = -1)
    (e f : FinalParityReassignments n m) (hef : e ≠ f) :
    ∃ (x : ParityPathSum n × Fin m) (j : Fin (n + 1)) (b : Bool),
      let t := parityPathValue (paritySlotPerm e x).1
      let u := parityPathValue (paritySlotPerm f x).1
      let forward := finalCopyParity t * anchorCodeEntry α t j b -
        finalCopyParity u * anchorCodeEntry α u j b
      (forward = 2 ∨ forward = -2) ∧ finalCopyParity t - finalCopyParity u = 0 := by
  obtain ⟨x, hx⟩ := distinct_reassignments_change_code α hα e f hef
  obtain ⟨j, b, hj⟩ := distinct_anchor_code_entry α _ _ hx
  refine ⟨x, j, b, ?_⟩
  dsimp only
  have he := (paritySlotPerm_preserves_parity e x).trans (paritySlotPerm_preserves_parity f x).symm
  have hp := copyPathParity_sign (finiteCopyPath (parityPathValue (paritySlotPerm e x).1)) (n + 1)
  change finalCopyParity (parityPathValue (paritySlotPerm e x).1) = 1 ∨
    finalCopyParity (parityPathValue (paritySlotPerm e x).1) = -1 at hp
  have hc := anchorCodeEntry_sign α hα (parityPathValue (paritySlotPerm e x).1) j b
  have hc' := anchorCodeEntry_sign α hα (parityPathValue (paritySlotPerm f x).1) j b
  rcases hp with hp | hp
  · have hpu := he.symm.trans hp
    rcases hc with hc | hc <;> rcases hc' with hc' | hc' <;>
      simp only [hc, hc', ne_eq, not_true_eq_false] at hj <;>
      norm_num [hp, hpu, hc, hc']
  · have hpu := he.symm.trans hp
    rcases hc with hc | hc <;> rcases hc' with hc' | hc' <;>
      simp only [hc, hc', ne_eq, not_true_eq_false] at hj <;>
      norm_num [hp, hpu, hc, hc']

end Ostmann

end OAI

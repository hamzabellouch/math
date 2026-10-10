import OAI.Combinatorics.LowSpaceSubsetSum.Counting.Model

namespace OAI

/-! # Testing a partial indexed mask before generating raw streams -/

namespace LowSpaceSubsetSum

structure MaskRestriction (n : ℕ) where
  ones : Finset (Fin n)
  zeros : Finset (Fin n)

namespace MaskRestriction

variable {n : ℕ} (P : MaskRestriction n)

def empty : MaskRestriction n := ⟨∅, ∅⟩

/-- A leaf checks only forced-one indices in its own top block. Forced zeros
can be tested against its selected top mask directly. -/
def Compatible (domain selected : Finset (Fin n)) : Prop :=
  P.ones ∩ domain ⊆ selected ∧ Disjoint P.zeros selected

instance (domain selected : Finset (Fin n)) : Decidable (P.Compatible domain selected) :=
  inferInstanceAs (Decidable (_ ∧ _))

def accept (domain selected : Finset (Fin n)) : Bool := decide (P.Compatible domain selected)

@[simp] theorem accept_eq_true (domain selected : Finset (Fin n)) :
    P.accept domain selected = true ↔ P.Compatible domain selected := by simp [accept]

@[simp] theorem empty_compatible (domain selected : Finset (Fin n)) :
    (empty (n := n)).Compatible domain selected := by simp [empty, Compatible]

theorem union_compatible {A B S T : Finset (Fin n)}
    (hS : P.Compatible A S) (hT : P.Compatible B T) :
    P.Compatible (A ∪ B) (S ∪ T) := by
  constructor
  · intro i hi
    obtain ⟨hiP, hi⟩ := Finset.mem_inter.mp hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact Finset.mem_union_left _ (hS.1 (Finset.mem_inter.mpr ⟨hiP, hi⟩))
    · exact Finset.mem_union_right _ (hT.1 (Finset.mem_inter.mpr ⟨hiP, hi⟩))
  · exact Finset.disjoint_union_right.mpr ⟨hS.2, hT.2⟩

/-- A compatible full mask yields a compatible leaf restriction because the
other leaf cannot contain an index in this leaf's disjoint top domain. -/
theorem left_compatible {A B S T : Finset (Fin n)}
    (hd : Disjoint A B) (hT : T ⊆ B) (h : P.Compatible (A ∪ B) (S ∪ T)) :
    P.Compatible A S := by
  constructor
  · intro i hi
    obtain ⟨hiP, hiA⟩ := Finset.mem_inter.mp hi
    have hiST := h.1 (Finset.mem_inter.mpr ⟨hiP, Finset.mem_union_left _ hiA⟩)
    rcases Finset.mem_union.mp hiST with hiS | hiT
    · exact hiS
    · exact (Finset.disjoint_left.mp hd hiA (hT hiT)).elim
  · exact h.2.mono_right Finset.subset_union_left

theorem right_compatible {A B S T : Finset (Fin n)}
    (hd : Disjoint A B) (hS : S ⊆ A) (h : P.Compatible (A ∪ B) (S ∪ T)) :
    P.Compatible B T := by
  apply P.left_compatible hd.symm hS
  simpa only [Finset.union_comm] using h

end MaskRestriction
end LowSpaceSubsetSum

end OAI

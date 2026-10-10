import OAI.GroupTheory.Thompson.BasicInterval
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Lean.Elab.Tactic.Omega

namespace OAI

/-!
# A concrete finite family of separated internal dyadic intervals

At depth 2D use the cells with indices 2i+1. The bound 2D < 2^(2D)
leaves room at the right endpoint. Each adjacent selected pair has a positive
gap. The finite occurrence type remembers parents and their children without
requiring an injectivity premise for the family.
-/

noncomputable section

namespace ThompsonNonamenability

/-- The actual ith selected dyadic cell at common depth 2D. -/
def selectedInterval (D : ℕ) (i : Fin D) : BasicInterval where
  depth := 2 * D
  index := ⟨2 * i.val + 1, by
    have hi := i.isLt
    have hsmall : 2 * i.val + 1 < 2 * D := by omega
    exact hsmall.trans (2 * D).lt_two_pow_self⟩

theorem selectedInterval_internal (D : ℕ) (i : Fin D) :
    (selectedInterval D i).Internal := by
  have hp : (0 : ℝ) < (2 : ℝ) ^ (2 * D) := pow_pos (by norm_num) _
  constructor
  · change (0 : ℝ) < ((2 * i.val + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (2 * D)
    exact div_pos (Nat.cast_pos.mpr (by omega)) hp
  · change (((2 * i.val + 1 : ℕ) : ℝ) + 1) / (2 : ℝ) ^ (2 * D) < 1
    apply (div_lt_one hp).2
    have hi := i.isLt
    have hsmall : 2 * i.val + 1 + 1 ≤ 2 * D := by omega
    have hlarge : 2 * i.val + 1 + 1 < 2 ^ (2 * D) :=
      hsmall.trans_lt (2 * D).lt_two_pow_self
    exact_mod_cast hlarge

theorem selectedInterval_before {D : ℕ} {i j : Fin D} (hij : i < j) :
    (selectedInterval D i).Before (selectedInterval D j) := by
  change (((2 * i.val + 1 : ℕ) : ℝ) + 1) / (2 : ℝ) ^ (2 * D) <
    ((2 * j.val + 1 : ℕ) : ℝ) / (2 : ℝ) ^ (2 * D)
  apply (div_lt_div_iff_of_pos_right (pow_pos (by norm_num : (0 : ℝ) < 2) _)).2
  have hv : i.val < j.val := hij
  have hn : 2 * i.val + 1 + 1 < 2 * j.val + 1 := by omega
  exact_mod_cast hn

/-- Strict separation permits either orientation and always has a positive gap. -/
def StrictlySeparated (I J : BasicInterval) : Prop := I.Before J ∨ J.Before I

theorem StrictlySeparated.symm {I J : BasicInterval}
    (h : StrictlySeparated I J) : StrictlySeparated J I := Or.symm h

theorem selectedInterval_separated {D : ℕ} {i j : Fin D} (hij : i ≠ j) :
    StrictlySeparated (selectedInterval D i) (selectedInterval D j) := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact Or.inl (selectedInterval_before h)
  · exact Or.inr (selectedInterval_before h)

theorem selected_siblings_separated {D : ℕ} (i : Fin D) {j k : Fin D}
    (hjk : j ≠ k) :
    StrictlySeparated ((selectedInterval D i).comp (selectedInterval D j))
      ((selectedInterval D i).comp (selectedInterval D k)) := by
  rcases selectedInterval_separated hjk with h | h
  · exact Or.inl ((selectedInterval D i).comp_before_comp h)
  · exact Or.inr ((selectedInterval D i).comp_before_comp h)

/-- A descendant is separated from every parent except its own parent. -/
theorem selected_child_parent_separated {D : ℕ} (i j k : Fin D) (hki : k ≠ i) :
    StrictlySeparated ((selectedInterval D i).comp (selectedInterval D j))
      (selectedInterval D k) := by
  have hc := (selectedInterval D i).comp_contained (selectedInterval D j)
  rcases selectedInterval_separated (Ne.symm hki) with h | h
  · exact Or.inl (lt_of_le_of_lt hc.2 h)
  · exact Or.inr (lt_of_lt_of_le h hc.1)

abbrev IntervalIndex (D : ℕ) := Fin D ⊕ (Fin D × Fin D)

/-- Actual parent and second-generation intervals indexed by their occurrences. -/
def familyInterval (D : ℕ) : IntervalIndex D → BasicInterval
  | .inl i => selectedInterval D i
  | .inr (i, j) => (selectedInterval D i).comp (selectedInterval D j)

theorem familyInterval_internal (D : ℕ) (q : IntervalIndex D) :
    (familyInterval D q).Internal := by
  rcases q with i | ⟨i, j⟩
  · exact selectedInterval_internal D i
  · exact (selectedInterval D i).comp_internal_of_internal_right
      (selectedInterval D j) (selectedInterval_internal D j)

/-- The actual finite interval set used by the single admissibility condition. -/
def intervalFamily (D : ℕ) : Finset BasicInterval :=
  Finset.univ.image (familyInterval D)

theorem familyInterval_mem (D : ℕ) (q : IntervalIndex D) :
    familyInterval D q ∈ intervalFamily D :=
  Finset.mem_image.mpr ⟨q, Finset.mem_univ q, rfl⟩

def firstIndex {D : ℕ} (hD : 2 ≤ D) : Fin D :=
  ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hD⟩

def secondIndex {D : ℕ} (hD : 2 ≤ D) : Fin D :=
  ⟨1, lt_of_lt_of_le (by decide : 1 < 2) hD⟩

theorem reference_before {D : ℕ} (hD : 2 ≤ D) :
    (selectedInterval D (firstIndex hD)).Before
      (selectedInterval D (secondIndex hD)) :=
  selectedInterval_before (show firstIndex hD < secondIndex hD from by
    change (0 : ℕ) < 1
    decide)

end ThompsonNonamenability

end

end OAI

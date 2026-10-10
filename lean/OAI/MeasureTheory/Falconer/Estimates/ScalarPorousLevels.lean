import OAI.MeasureTheory.Falconer.Estimates.ScalarLevelEnumeration
import OAI.MeasureTheory.Falconer.Recursion.ScalarTerminalPorousGain

namespace OAI

/-! The actual porous/nonporous partition. Collapsed levels have no
 geometric constraint and can be normalized to their coarser endpoint. -/
namespace Falconer.Regularization

def scalarEffectiveLevel (B : ℕ) (k n : ℕ → ℕ) (i : ℕ) : ℕ :=
  if k i = 0 then B*i else n i

 theorem scalar_effective_branching_level {B i : ℕ} {L : Finset (CellPath 1)}
    (k n : ℕ → ℕ) (h : ScalarBranchingLevel L (B*i) (B*(i+1)) (k i) (n i)) :
    ScalarBranchingLevel L (B*i) (B*(i+1)) (k i) (scalarEffectiveLevel B k n i) := by
  by_cases hz : k i = 0
  · simp only [scalarEffectiveLevel,ite_eq_left hz]
    refine ⟨h.exponent_le,le_rfl,Nat.mul_le_mul_left B (Nat.le_succ i),h.children_card,?_⟩
    intro p hp
    exact Or.inl hz
  · simpa only [scalarEffectiveLevel,ite_eq_right hz] using h

noncomputable def scalarPorousLevels (M B C : ℕ) (k n : ℕ → ℕ) : Finset ℕ :=
  (Finset.range M).filter fun i => k i = 0 ∨ n i+C < B*(i+1)

 theorem scalar_porous_margin {M B C : ℕ} (hCB : C ≤ B) (k n : ℕ → ℕ)
    {i : ℕ} (hi : i ∈ scalarPorousLevels M B C k n) :
    scalarEffectiveLevel B k n i+C ≤ B*(i+1) := by
  classical
  rcases (Finset.mem_filter.mp hi).2 with hz | hgap
  · simp only [scalarEffectiveLevel,ite_eq_left hz]
    nlinarith
  · by_cases hz : k i = 0
    · simp only [scalarEffectiveLevel,ite_eq_left hz]
      nlinarith
    · simpa only [scalarEffectiveLevel,ite_eq_right hz] using hgap.le

 theorem scalar_porous_nonporous_partition (M B C : ℕ) (k n : ℕ → ℕ) :
    scalarPorousLevels M B C k n = Finset.range M \ scalarNonporousLevels M B C k n := by
  classical
  ext i
  simp only [scalarPorousLevels,scalarNonporousLevels,Finset.mem_filter,Finset.mem_sdiff,
    Finset.mem_range]
  omega

 theorem scalar_porous_count (M B C : ℕ) (k n : ℕ → ℕ) :
    (scalarPorousLevels M B C k n).card+(scalarNonporousLevels M B C k n).card = M := by
  classical
  rw [scalar_porous_nonporous_partition]
  have hs : scalarNonporousLevels M B C k n ⊆ Finset.range M := Finset.filter_subset _ _
  simpa only [Finset.card_range] using Finset.card_sdiff_add_card_eq_card hs

 theorem scalar_nonporous_effective (M B C : ℕ) (k n : ℕ → ℕ) :
    scalarNonporousLevels M B C k (scalarEffectiveLevel B k n) =
      scalarNonporousLevels M B C k n := by
  classical
  ext i
  simp only [scalarNonporousLevels,Finset.mem_filter]
  by_cases hz : k i = 0
  · simp only [hz,ne_eq,not_true_eq_false,false_and,and_false]
  · simp only [scalarEffectiveLevel,ite_eq_right hz]

end Falconer.Regularization

end OAI

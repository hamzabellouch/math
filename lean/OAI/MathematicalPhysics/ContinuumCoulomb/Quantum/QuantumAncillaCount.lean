import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumHistorySpectrum

namespace OAI

/-! Replace the joint ancilla penalty by a sum of individual qubit penalties. -/

noncomputable section
namespace ContinuumCoulomb
open scoped BigOperators Classical

def qmaAncillaCount (c : QMACircuit) (s : SourceSpinBasis (c.work+1)) : ℝ :=
  ∑ i : Fin (c.work+1), if c.witness ≤ i.val ∧ s i ≠ 0 then 1 else 0

theorem qmaAncillaCount_nonneg (c : QMACircuit) (s : SourceSpinBasis (c.work+1)) :
    0 ≤ qmaAncillaCount c s := by
  unfold qmaAncillaCount
  positivity

theorem qmaAncillaCount_zero (c : QMACircuit) (s : SourceSpinBasis (c.work+1))
    (hs : QMAAncillaZero c s) : qmaAncillaCount c s = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  have hi : ¬(c.witness ≤ i.val ∧ s i ≠ 0) := by
    rintro ⟨hi,hne⟩
    exact hne (hs i hi)
  simp [hi]

theorem qmaAncillaCount_one_le (c : QMACircuit) (s : SourceSpinBasis (c.work+1))
    (hs : ¬QMAAncillaZero c s) : 1 ≤ qmaAncillaCount c s := by
  obtain ⟨i,hi,hne⟩ : ∃ i : Fin (c.work+1), c.witness ≤ i.val ∧ s i ≠ 0 := by
    by_contra hn
    apply hs
    intro i hi
    by_contra hne
    exact hn ⟨i,hi,hne⟩
  have h := Finset.single_le_sum
    (f := fun j : Fin (c.work+1) => if c.witness ≤ j.val ∧ s j ≠ 0 then (1:ℝ) else 0)
    (s := Finset.univ) (a := i) (by intro j _; positivity) (Finset.mem_univ _)
  simpa only [qmaAncillaCount,ite_eq_left (show c.witness ≤ i.val ∧ s i ≠ 0 from ⟨hi,hne⟩)] using h

theorem qmaAncillaCount_le (c : QMACircuit) (s : SourceSpinBasis (c.work+1)) :
    qmaAncillaCount c s ≤ c.work+1 := by
  calc
    qmaAncillaCount c s ≤ ∑ _i : Fin (c.work+1), (1:ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      split <;> norm_num
    _ = _ := by simp

theorem qmaAncillaCount_dominates (c : QMACircuit) (s : SourceSpinBasis (c.work+1)) :
    (if QMAAncillaZero c s then (0:ℝ) else 1) ≤ qmaAncillaCount c s := by
  by_cases hs : QMAAncillaZero c s
  · simpa only [ite_eq_left hs] using qmaAncillaCount_nonneg c s
  · simpa only [ite_eq_right hs] using qmaAncillaCount_one_le c s hs

end ContinuumCoulomb

end

end OAI

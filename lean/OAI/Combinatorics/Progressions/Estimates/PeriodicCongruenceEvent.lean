import OAI.Combinatorics.Progressions.Lattices.SelectedResidueApproximation

namespace OAI

section

namespace Erdos3

open scoped Classical

noncomputable def residuePatternEvent {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) [∀ j, NeZero (modulus j)]
    (Good : ColumnResiduePattern K I modulus → Prop) : Finset (ColumnResiduePattern K I modulus) :=
  Finset.univ.filter Good

theorem mem_residuePatternEvent {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) [∀ j, NeZero (modulus j)]
    (Good : ColumnResiduePattern K I modulus → Prop) (r : ColumnResiduePattern K I modulus) :
    r ∈ residuePatternEvent modulus Good ↔ Good r := by
  simp only [residuePatternEvent, Finset.mem_filter, Finset.mem_univ, true_and]

theorem residuePatternEvent_nonempty {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) [∀ j, NeZero (modulus j)]
    (Good : ColumnResiduePattern K I modulus → Prop) :
    (residuePatternEvent modulus Good).Nonempty ↔ ∃ r, Good r := by
  simp only [Finset.Nonempty, mem_residuePatternEvent]

theorem selectedResidueSmoothWeight_event {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) [∀ j, NeZero (modulus j)]
    (Good : ColumnResiduePattern K I modulus → Prop) (V : K × I → ℝ) (x : K × I → ℤ) :
    selectedResidueSmoothWeight modulus (residuePatternEvent modulus Good) V x =
      if Good (columnResiduePattern modulus x) then
        smoothProductProfile (K × I) (fun z => (x z : ℝ) / V z) else 0 := by
  simp only [selectedResidueSmoothWeight, mem_residuePatternEvent]

theorem selectedResidueSmoothPMF_event_toReal {K I : Type*} [Fintype K] [Fintype I]
    (modulus : I → ℕ) [∀ j, NeZero (modulus j)]
    (Good : ColumnResiduePattern K I modulus → Prop) (V : K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' y, selectedResidueSmoothWeight modulus (residuePatternEvent modulus Good) V y)
    (x : K × I → ℤ) :
    (selectedResidueSmoothPMF modulus (residuePatternEvent modulus Good) V hV hZ x).toReal =
      (if Good (columnResiduePattern modulus x) then
        smoothProductProfile (K × I) (fun z => (x z : ℝ) / V z) else 0) /
      ∑' y, if Good (columnResiduePattern modulus y) then
        smoothProductProfile (K × I) (fun z => (y z : ℝ) / V z) else 0 := by
  simp only [selectedResidueSmoothPMF_toReal, selectedResidueSmoothWeight_event]

end Erdos3

end

end OAI

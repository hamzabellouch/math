import OAI.Analysis.LipschitzHilbert.Trees.SourceScaleRestriction

namespace OAI

/-! Replace an arbitrary selected top length by a comparable existing
dyadic scale while retaining every packet below that top. -/
noncomputable section
namespace LipschitzHilbert.SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem exists_enclosing_scale (L : ℝ) (hLtop : L≤P.topLength)
    (hwitness : ∃ j, P.length j≤L) :
    ∃ first : Fin N, P.length first≤L ∧ L<2*P.length first ∧
      ∀ j, P.length j≤L → first≤j := by
  classical
  let S := Finset.univ.filter (fun j : Fin N => P.length j≤L)
  have hS : S.Nonempty := by
    obtain ⟨j,hj⟩ := hwitness
    exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩⟩
  let first := S.min' hS
  have hfirst : P.length first≤L := (Finset.mem_filter.mp (Finset.min'_mem S hS)).2
  have hmin (j : Fin N) (hj : P.length j≤L) : first≤j :=
    Finset.min'_le S j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩)
  refine ⟨first,hfirst,?_,hmin⟩
  by_cases hz : first.val=0
  · have he : P.length first=P.topLength := by simp only [length,hz,pow_zero,div_one]
    rw [he]
    linarith [P.topLength_pos]
  · let prev : Fin N := ⟨first.val-1,by have := first.isLt; omega⟩
    have hp : ¬P.length prev≤L := by
      intro hp
      have hh := hmin prev hp
      change first.val≤first.val-1 at hh
      omega
    have he : P.length prev=2*P.length first := by
      have hi : first.val=prev.val+1 := by dsimp [prev]; omega
      unfold length
      rw [hi,pow_succ]
      field_simp
    rw [←he]
    exact lt_of_not_ge hp

end LipschitzHilbert.SourceLabeledLattice

end

end OAI

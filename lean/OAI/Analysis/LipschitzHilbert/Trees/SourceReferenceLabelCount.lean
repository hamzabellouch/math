import OAI.Analysis.LipschitzHilbert.Trees.SourceReferenceMainRestriction
import OAI.Analysis.LipschitzHilbert.Trees.SourceSlopeLabels

namespace OAI

/-! A reference cone contains uniformly few original slope labels.
The estimate uses the manuscript's local angular multiplicity. -/
noncomputable section
open scoped BigOperators
namespace LipschitzHilbert.SourceLabeledLattice
attribute [local instance] Classical.propDecidable
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)

theorem referenceLabels_card_le_local (oldSlope t r cone w : ℝ) (hw : 0<w)
    (M Q : ℕ) (hQ : cone≤Q) (j : Fin N)
    (hlocal : SourceSlopeLabels.LocalMultiplicity Finset.univ
      (fun l : P.labels j => oldSlope+P.rowSlope j l) (w/P.length j) M) :
    (P.referenceLabels oldSlope t r cone w j).card≤(2*Q+1)*M := by
  let orig := P.referenceOriginalLabel oldSlope t r cone w j
  let S := SourceSlopeLabels.window Finset.univ
    (fun l : P.labels j => oldSlope+P.rowSlope j l) t (w/P.length j) cone
  have hm : Set.MapsTo orig (Finset.univ : Finset (P.referenceLabels oldSlope t r cone w j)) S := by
    intro l _
    have hl := (P.referenceLabel_bounds oldSlope t r cone w j l).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    change |oldSlope+P.rowSlope j (orig l)-t|≤cone*(w/P.length j)
    have he : oldSlope+P.rowSlope j (orig l)-t=
        P.rowSlope j (orig l)+(oldSlope-t) := by ring
    rw [he]
    simpa only [mul_div_assoc] using hl
  have hi : Set.InjOn orig (Finset.univ : Finset (P.referenceLabels oldSlope t r cone w j)) := by
    intro l _ m _ h
    exact Subtype.ext (congrArg (fun q : P.labels j => q.val) h)
  have hc := Finset.card_le_card_of_injOn orig hm hi
  have hwnd := SourceSlopeLabels.window_card_le Finset.univ
    (fun l : P.labels j => oldSlope+P.rowSlope j l) (t := t) (div_pos hw (P.length_pos j)) hlocal hQ
  simpa only [Finset.card_univ,Fintype.card_coe] using hc.trans hwnd

end LipschitzHilbert.SourceLabeledLattice

end

end OAI

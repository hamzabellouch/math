import OAI.NumberTheory.Ostmann.Characters.TemplateDiagonalMatchingCount
import OAI.NumberTheory.Ostmann.Characters.TemplateGraphFibers
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseAction

namespace OAI

noncomputable section
namespace Ostmann.Characters.Template.OneSidedPhase
open ParityActions
attribute [local instance] Classical.propDecidable

def anchorCodeEntry (k l : ℕ) (w : Word k l) (j : Fin l) (b : Bool) : ℤˣ :=
  if b then (AnchorCodes.code (fun _ => 1) (pathSigns k l w) j).1
  else (AnchorCodes.code (fun _ => 1) (pathSigns k l w) j).2

theorem graph_anchor_entry (k l : ℕ) (hl : l ≤ k) (big : Bool)
    (w : Word k l) (j : Fin l) (b : Bool) :
    graph k l (retiredAnchors k l hl big j b).val w.val =
      (rowSign k l w.val : ℤ) * (anchorCodeEntry k l w j b : ℤ) := by
  cases b
  · exact (graph_anchor_code k l hl big w j).2
  · exact (graph_anchor_code k l hl big w j).1

theorem changed_word_code_edge (k l : ℕ) (hl : l ≤ k) (w z : Word k l)
    (hc : AnchorCodes.code (fun _ => 1) (pathSigns k l w) ≠
      AnchorCodes.code (fun _ => 1) (pathSigns k l z)) :
    ∃j : Fin l, ∃b : Bool,
      ((graph k l (retiredAnchors k l hl false j b).val w.val -
          graph k l (retiredAnchors k l hl false j b).val z.val = 2 ∨
        graph k l (retiredAnchors k l hl false j b).val w.val -
          graph k l (retiredAnchors k l hl false j b).val z.val = -2) ∧
        graph k l w.val (retiredAnchors k l hl false j b).val -
          graph k l z.val (retiredAnchors k l hl false j b).val = 0) ∨
      ((graph k l w.val (retiredAnchors k l hl true j b).val -
          graph k l z.val (retiredAnchors k l hl true j b).val = 2 ∨
        graph k l w.val (retiredAnchors k l hl true j b).val -
          graph k l z.val (retiredAnchors k l hl true j b).val = -2) ∧
        graph k l (retiredAnchors k l hl true j b).val w.val -
          graph k l (retiredAnchors k l hl true j b).val z.val = 0) := by
  have hex : ∃j : Fin l, ∃b : Bool, anchorCodeEntry k l w j b ≠ anchorCodeEntry k l z j b := by
    by_contra hh
    push Not at hh
    apply hc
    funext j
    exact Prod.ext (hh j true) (hh j false)
  obtain ⟨j,b,hentry⟩ := hex
  refine ⟨j,b,?_⟩
  simp only [graph_anchor_entry,graph_word_retiredAnchor]
  rcases changed_code_one_sided (rowSign k l w.val) (rowSign k l z.val)
    (anchorCodeEntry k l w j b) (anchorCodeEntry k l z j b) hentry with h | h
  · exact Or.inl ⟨h.2.1,h.2.2⟩
  · exact Or.inr ⟨h.2.2,h.2.1⟩

def matchingPermutation (k n : ℕ) (width : Role → ℕ)
    (σ : Equiv.Perm (BulkSlot k n (width .word))) :
    Equiv.Perm ((schedule k (n+1)).Constituent width) :=
  σ.viaEmbedding (bulkEmbedding k n width)

@[simp] theorem matchingPermutation_bulk (k n : ℕ) (width : Role → ℕ)
    (σ : Equiv.Perm (BulkSlot k n (width .word))) (z : BulkSlot k n (width .word)) :
    matchingPermutation k n width σ (bulkEmbedding k n width z) =
      bulkEmbedding k n width (σ z) := Equiv.Perm.viaEmbedding_apply _ _ _

theorem matchingPermutation_nonword (k n : ℕ) (width : Role → ℕ)
    (σ : Equiv.Perm (BulkSlot k n (width .word))) (i : (schedule k (n+1)).Constituent width)
    (hi : (schedule k (n+1)).role i.1 ≠ .word) : matchingPermutation k n width σ i = i := by
  apply Equiv.Perm.viaEmbedding_apply_of_notMem
  rintro ⟨z,hz⟩
  apply hi
  rw [←hz]
  exact z.1.property.2

def anchorConstituent (k n : ℕ) (hn : n+1 ≤ k) (width : Role → ℕ)
    (hw : ∀j : Fin (n+1), ∀big, 0 < width (.anchor j big))
    (big : Bool) (j : Fin (n+1)) (b : Bool) : (schedule k (n+1)).Constituent width :=
  ⟨(retiredAnchors k (n+1) hn big j b).val,
    Fin.cast (congrArg width (retiredAnchors k (n+1) hn big j b).property.2).symm ⟨0,hw j big⟩⟩

@[simp] theorem anchorConstituent_role (k n : ℕ) (hn : n+1 ≤ k) (width : Role → ℕ)
    (hw : ∀j : Fin (n+1), ∀big, 0 < width (.anchor j big)) (big : Bool) (j : Fin (n+1)) (b : Bool) :
    (schedule k (n+1)).role (anchorConstituent k n hn width hw big j b).1 = .anchor j big :=
  (retiredAnchors k (n+1) hn big j b).property.2

@[simp] theorem matchingPermutation_anchor (k n : ℕ) (hn : n+1 ≤ k) (width : Role → ℕ)
    (hw : ∀j : Fin (n+1), ∀big, 0 < width (.anchor j big))
    (σ : Equiv.Perm (BulkSlot k n (width .word))) (big : Bool) (j : Fin (n+1)) (b : Bool) :
    matchingPermutation k n width σ (anchorConstituent k n hn width hw big j b) =
      anchorConstituent k n hn width hw big j b := by
  apply matchingPermutation_nonword
  rw [anchorConstituent_role]
  exact Role.noConfusion

theorem anchorConstituent_fst_ne_bulk (k n : ℕ) (hn : n+1 ≤ k) (width : Role → ℕ)
    (hw : ∀j : Fin (n+1), ∀big, 0 < width (.anchor j big))
    (big : Bool) (j : Fin (n+1)) (b : Bool) (z : BulkSlot k n (width .word)) :
    (anchorConstituent k n hn width hw big j b).1 ≠ (bulkEmbedding k n width z).1 := by
  intro he
  have hr := congrArg (schedule k (n+1)).role he
  rw [anchorConstituent_role] at hr
  change Role.anchor j big = (schedule k (n+1)).role z.1.val at hr
  rw [z.1.property.2] at hr
  exact Role.noConfusion hr

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI

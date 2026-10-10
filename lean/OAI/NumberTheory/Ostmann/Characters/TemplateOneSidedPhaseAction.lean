import Mathlib.GroupTheory.Perm.ViaEmbedding
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseQuotient
import OAI.NumberTheory.Ostmann.Characters.TemplateParityActionsAnchors

namespace OAI

noncomputable section
namespace Ostmann.Characters.Template.OneSidedPhase
open ParityActions
attribute [local instance] Classical.propDecidable

def bulkEmbedding (k n : ℕ) (width : Role → ℕ) :
    BulkSlot k n (width .word) ↪ (schedule k (n+1)).Constituent width where
  toFun z := ⟨z.1.val,Fin.cast (congrArg width z.1.property.2).symm z.2⟩
  inj' := by
    intro z w h
    apply Prod.ext
    · exact Subtype.ext (congrArg Sigma.fst h)
    · apply Fin.ext
      exact congrArg (fun i : (schedule k (n+1)).Constituent width=>i.2.val) h

def constituentPermutation (k n : ℕ) (width : Role → ℕ)
    (σ : Reassignments k n (width .word)) : Equiv.Perm ((schedule k (n+1)).Constituent width) :=
  (bulkPermutation k n (width .word) σ).viaEmbedding (bulkEmbedding k n width)

@[simp] theorem constituentPermutation_bulk (k n : ℕ) (width : Role → ℕ)
    (σ : Reassignments k n (width .word)) (z : BulkSlot k n (width .word)) :
    constituentPermutation k n width σ (bulkEmbedding k n width z)=
      bulkEmbedding k n width (bulkPermutation k n (width .word) σ z) :=
  Equiv.Perm.viaEmbedding_apply _ _ _

theorem constituentPermutation_nonword (k n : ℕ) (width : Role → ℕ)
    (σ : Reassignments k n (width .word)) (i : (schedule k (n+1)).Constituent width)
    (hi : (schedule k (n+1)).role i.1≠.word) : constituentPermutation k n width σ i=i := by
  apply Equiv.Perm.viaEmbedding_apply_of_notMem
  rintro ⟨z,hz⟩
  apply hi
  rw [←hz]
  exact z.1.property.2

def smallAnchorConstituent (k n : ℕ) (hn : n+1 ≤ k) (width : Role → ℕ)
    (hw : ∀j : Fin (n+1),0<width (.anchor j false)) (j : Fin (n+1)) (b : Bool) :
    (schedule k (n+1)).Constituent width :=
  ⟨(retiredAnchors k (n+1) hn false j b).val,
    Fin.cast (congrArg width (retiredAnchors k (n+1) hn false j b).property.2).symm ⟨0,hw j⟩⟩

@[simp] theorem smallAnchorConstituent_role (k n : ℕ) (hn : n+1 ≤ k) (width : Role → ℕ)
    (hw : ∀j : Fin (n+1),0<width (.anchor j false)) (j : Fin (n+1)) (b : Bool) :
    (schedule k (n+1)).role (smallAnchorConstituent k n hn width hw j b).1=.anchor j false :=
  (retiredAnchors k (n+1) hn false j b).property.2

@[simp] theorem constituentPermutation_anchor (k n : ℕ) (hn : n+1 ≤ k) (width : Role → ℕ)
    (hw : ∀j : Fin (n+1),0<width (.anchor j false))
    (σ : Reassignments k n (width .word)) (j : Fin (n+1)) (b : Bool) :
    constituentPermutation k n width σ (smallAnchorConstituent k n hn width hw j b)=
      smallAnchorConstituent k n hn width hw j b := by
  apply constituentPermutation_nonword
  rw [smallAnchorConstituent_role]
  exact Role.noConfusion

theorem constituentGraph_of_fst_ne (k l : ℕ) (width : Role → ℕ)
    (i h : (schedule k l).Constituent width) (hne : i.1≠h.1) :
    constituentGraph k l width i h=graph k l i.1 h.1 := by
  have hih : i≠h := fun he=>hne (congrArg Sigma.fst he)
  simp only [constituentGraph,liftGraph,ite_eq_right hih,ite_eq_right hne]

private theorem anchor_fst_ne_bulk (k n : ℕ) (hn : n+1 ≤ k) (width : Role → ℕ)
    (hw : ∀j : Fin (n+1),0<width (.anchor j false))
    (j : Fin (n+1)) (b : Bool) (z : BulkSlot k n (width .word)) :
    (smallAnchorConstituent k n hn width hw j b).1≠(bulkEmbedding k n width z).1 := by
  intro he
  have hr := congrArg (schedule k (n+1)).role he
  rw [smallAnchorConstituent_role] at hr
  change Role.anchor j false=(schedule k (n+1)).role z.1.val at hr
  rw [z.1.property.2] at hr
  exact Role.noConfusion hr

theorem distinct_reassignments_constituent_edge (k n : ℕ) (hn : n+1 ≤ k)
    (width : Role → ℕ) (hw : ∀j : Fin (n+1),0<width (.anchor j false))
    {σ ρ : Reassignments k n (width .word)} (hσρ : σ≠ρ) :
    ∃z : BulkSlot k n (width .word),∃j : Fin (n+1),∃b : Bool,
      let L := bulkEmbedding k n width z
      let S := smallAnchorConstituent k n hn width hw j b
      let D := fun i h=>permutedGraph (constituentGraph k (n+1) width)
        (constituentPermutation k n width σ) i h-
        permutedGraph (constituentGraph k (n+1) width) (constituentPermutation k n width ρ) i h
      L≠S ∧ (D S L=2 ∨ D S L= -2) ∧ D L S=0 := by
  obtain ⟨z,j,b,_hpos,_hs,hforward,hreverse⟩ :=
    distinct_reassignments_anchor k n (width .word) hn hσρ
  refine ⟨z,j,b,?_,?_,?_⟩
  · exact fun he=>anchor_fst_ne_bulk k n hn width hw j b z (congrArg Sigma.fst he.symm)
  · dsimp only
    simp only [permutedGraph]
    simp only [constituentPermutation_anchor k n hn width hw σ j b,
      constituentPermutation_anchor k n hn width hw ρ j b,
      constituentPermutation_bulk k n width σ z,constituentPermutation_bulk k n width ρ z]
    rw [constituentGraph_of_fst_ne _ _ _ _ _ (anchor_fst_ne_bulk k n hn width hw j b _),
      constituentGraph_of_fst_ne _ _ _ _ _ (anchor_fst_ne_bulk k n hn width hw j b _)]
    exact hforward
  · dsimp only
    simp only [permutedGraph]
    simp only [constituentPermutation_anchor k n hn width hw σ j b,
      constituentPermutation_anchor k n hn width hw ρ j b,
      constituentPermutation_bulk k n width σ z,constituentPermutation_bulk k n width ρ z]
    rw [constituentGraph_of_fst_ne _ _ _ _ _ (anchor_fst_ne_bulk k n hn width hw j b _).symm,
      constituentGraph_of_fst_ne _ _ _ _ _ (anchor_fst_ne_bulk k n hn width hw j b _).symm]
    exact hreverse

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI

import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseTerminal

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.Template.OneSidedPhase
open ParityActions
attribute [local instance] Classical.propDecidable

def prefixBulkEmbedding (k n : ℕ) (width : Role → ℕ) (m : ℕ) (hm : m ≤ width .word) :
    BulkSlot k n m ↪ (schedule k (n+1)).Constituent width where
  toFun z := ⟨z.1.val,Fin.cast (congrArg width z.1.property.2).symm (z.2.castLE hm)⟩
  inj' := by
    intro z w h
    apply Prod.ext
    · exact Subtype.ext (congrArg Sigma.fst h)
    · apply Fin.ext
      exact congrArg (fun i : (schedule k (n+1)).Constituent width => i.2.val) h

def prefixConstituentPermutation (k n : ℕ) (width : Role → ℕ) (m : ℕ) (hm : m ≤ width .word)
    (σ : Reassignments k n m) : Equiv.Perm ((schedule k (n+1)).Constituent width) :=
  (bulkPermutation k n m σ).viaEmbedding (prefixBulkEmbedding k n width m hm)

@[simp] theorem prefixConstituentPermutation_bulk (k n : ℕ) (width : Role → ℕ)
    (m : ℕ) (hm : m ≤ width .word) (σ : Reassignments k n m) (z : BulkSlot k n m) :
    prefixConstituentPermutation k n width m hm σ (prefixBulkEmbedding k n width m hm z) =
      prefixBulkEmbedding k n width m hm (bulkPermutation k n m σ z) :=
  Equiv.Perm.viaEmbedding_apply _ _ _

theorem prefixConstituentPermutation_nonword (k n : ℕ) (width : Role → ℕ)
    (m : ℕ) (hm : m ≤ width .word) (σ : Reassignments k n m)
    (i : (schedule k (n+1)).Constituent width) (hi : (schedule k (n+1)).role i.1 ≠ .word) :
    prefixConstituentPermutation k n width m hm σ i = i := by
  apply Equiv.Perm.viaEmbedding_apply_of_notMem
  rintro ⟨z,hz⟩
  apply hi
  rw [←hz]
  exact z.1.property.2

theorem prefixConstituentPermutation_tail (k n : ℕ) (width : Role → ℕ)
    (m : ℕ) (hm : m ≤ width .word) (σ : Reassignments k n m)
    (i : (schedule k (n+1)).Constituent width) (hi : m ≤ i.2.val) :
    prefixConstituentPermutation k n width m hm σ i = i := by
  apply Equiv.Perm.viaEmbedding_apply_of_notMem
  rintro ⟨z,hz⟩
  have he := congrArg (fun i : (schedule k (n+1)).Constituent width => i.2.val) hz
  change z.2.val = i.2.val at he
  exact (not_lt_of_ge hi) (he ▸ z.2.isLt)

@[simp] theorem prefixConstituentPermutation_anchor (k n : ℕ) (hn : n+1 ≤ k) (width : Role → ℕ)
    (hw : ∀j : Fin (n+1),0 < width (.anchor j false)) (m : ℕ) (hm : m ≤ width .word)
    (σ : Reassignments k n m) (j : Fin (n+1)) (b : Bool) :
    prefixConstituentPermutation k n width m hm σ (smallAnchorConstituent k n hn width hw j b) =
      smallAnchorConstituent k n hn width hw j b := by
  apply prefixConstituentPermutation_nonword
  rw [smallAnchorConstituent_role]
  exact Role.noConfusion

theorem smallAnchor_fst_ne_prefixBulk (k n : ℕ) (hn : n+1 ≤ k) (width : Role → ℕ)
    (hw : ∀j : Fin (n+1),0 < width (.anchor j false)) (m : ℕ) (hm : m ≤ width .word)
    (j : Fin (n+1)) (b : Bool) (z : BulkSlot k n m) :
    (smallAnchorConstituent k n hn width hw j b).1 ≠ (prefixBulkEmbedding k n width m hm z).1 := by
  intro he
  have hr := congrArg (schedule k (n+1)).role he
  rw [smallAnchorConstituent_role] at hr
  change Role.anchor j false = (schedule k (n+1)).role z.1.val at hr
  rw [z.1.property.2] at hr
  exact Role.noConfusion hr

theorem prefix_distinct_reassignments_edge (k n : ℕ) (hn : n+1 ≤ k) (width : Role → ℕ)
    (hw : ∀j : Fin (n+1),0 < width (.anchor j false)) (m : ℕ) (hm : m ≤ width .word)
    {σ ρ : Reassignments k n m} (hσρ : σ ≠ ρ) :
    ∃z : BulkSlot k n m, ∃j : Fin (n+1), ∃b : Bool,
      let L := prefixBulkEmbedding k n width m hm z
      let S := smallAnchorConstituent k n hn width hw j b
      let D := differenceGraph k (n+1) width (prefixConstituentPermutation k n width m hm σ)
        (prefixConstituentPermutation k n width m hm ρ)
      L ≠ S ∧ (D S L = 2 ∨ D S L = -2) ∧ D L S = 0 := by
  obtain ⟨z,j,b,_hpos,_hs,hforward,hreverse⟩ := distinct_reassignments_anchor k n m hn hσρ
  refine ⟨z,j,b,?_,?_,?_⟩
  · exact fun he => smallAnchor_fst_ne_prefixBulk k n hn width hw m hm j b z (congrArg Sigma.fst he.symm)
  · simp only [differenceGraph,permutedGraph]
    simp only [prefixConstituentPermutation_anchor k n hn width hw m hm σ j b,
      prefixConstituentPermutation_anchor k n hn width hw m hm ρ j b,
      prefixConstituentPermutation_bulk k n width m hm σ z,prefixConstituentPermutation_bulk k n width m hm ρ z]
    rw [constituentGraph_of_fst_ne _ _ _ _ _ (smallAnchor_fst_ne_prefixBulk k n hn width hw m hm j b _),
      constituentGraph_of_fst_ne _ _ _ _ _ (smallAnchor_fst_ne_prefixBulk k n hn width hw m hm j b _)]
    exact hforward
  · simp only [differenceGraph,permutedGraph]
    simp only [prefixConstituentPermutation_anchor k n hn width hw m hm σ j b,
      prefixConstituentPermutation_anchor k n hn width hw m hm ρ j b,
      prefixConstituentPermutation_bulk k n width m hm σ z,prefixConstituentPermutation_bulk k n width m hm ρ z]
    rw [constituentGraph_of_fst_ne _ _ _ _ _ (smallAnchor_fst_ne_prefixBulk k n hn width hw m hm j b _).symm,
      constituentGraph_of_fst_ne _ _ _ _ _ (smallAnchor_fst_ne_prefixBulk k n hn width hw m hm j b _).symm]
    exact hreverse

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI

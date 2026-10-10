import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateCopiedCodesEdgesBasic
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseActual

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.DiagonalEstimate
open Template HigherBiasSource HigherBiasSource.SourceTemplate TemplateDiagonalMatching
open Template.OneSidedPhase
attribute [local instance] Classical.propDecidable

theorem copied_anchor_bulk_edge {k : ℕ} (cfg : SourceConfiguration k) (m j : ℕ) (hj : j ≤ k)
    (σ ρ : Equiv.Perm (ActualCopied cfg m j))
    (hσ : CopiedBulkPreserving cfg m j σ) (hρ : CopiedBulkPreserving cfg m j ρ)
    (big : Bool) (a : Fin j) (b : Bool) (z : Word k j × Fin m) :
    differenceGraph k j (sourceWidth cfg m)
      (copiedPermutationExtension (schedule k j) j (sourceWidth cfg m) σ)
      (copiedPermutationExtension (schedule k j) j (sourceWidth cfg m) ρ)
      (copiedRetiredAnchor cfg m j hj big a b) (copiedBulkOld cfg m j z) =
    graph k j (retiredAnchors k j hj big a b).val (copiedBulkImage cfg m j σ hσ z).1.val -
      graph k j (retiredAnchors k j hj big a b).val (copiedBulkImage cfg m j ρ hρ z).1.val := by
  simp only [differenceGraph,permutedGraph,copiedPermutationExtension_retired,
    copiedExtension_bulk_image cfg m j σ hσ,copiedExtension_bulk_image cfg m j ρ hρ]
  rw [constituentGraph_of_fst_ne _ _ _ _ _ (copiedRetiredAnchor_fst_ne_bulk cfg m j hj big a b _),
    constituentGraph_of_fst_ne _ _ _ _ _ (copiedRetiredAnchor_fst_ne_bulk cfg m j hj big a b _)]
  rfl

theorem copied_bulk_anchor_edge {k : ℕ} (cfg : SourceConfiguration k) (m j : ℕ) (hj : j ≤ k)
    (σ ρ : Equiv.Perm (ActualCopied cfg m j))
    (hσ : CopiedBulkPreserving cfg m j σ) (hρ : CopiedBulkPreserving cfg m j ρ)
    (big : Bool) (a : Fin j) (b : Bool) (z : Word k j × Fin m) :
    differenceGraph k j (sourceWidth cfg m)
      (copiedPermutationExtension (schedule k j) j (sourceWidth cfg m) σ)
      (copiedPermutationExtension (schedule k j) j (sourceWidth cfg m) ρ)
      (copiedBulkOld cfg m j z) (copiedRetiredAnchor cfg m j hj big a b) =
    graph k j (copiedBulkImage cfg m j σ hσ z).1.val (retiredAnchors k j hj big a b).val -
      graph k j (copiedBulkImage cfg m j ρ hρ z).1.val (retiredAnchors k j hj big a b).val := by
  simp only [differenceGraph,permutedGraph,copiedPermutationExtension_retired,
    copiedExtension_bulk_image cfg m j σ hσ,copiedExtension_bulk_image cfg m j ρ hρ]
  rw [constituentGraph_of_fst_ne _ _ _ _ _ (copiedRetiredAnchor_fst_ne_bulk cfg m j hj big a b _).symm,
    constituentGraph_of_fst_ne _ _ _ _ _ (copiedRetiredAnchor_fst_ne_bulk cfg m j hj big a b _).symm]
  rfl

theorem copied_changed_code_edge {k : ℕ} (cfg : SourceConfiguration k) (m j : ℕ) (hj : j ≤ k)
    (σ ρ : Equiv.Perm (ActualCopied cfg m j))
    (hσ : CopiedBulkPreserving cfg m j σ) (hρ : CopiedBulkPreserving cfg m j ρ)
    (z : Word k j × Fin m)
    (hc : bulkCode k j m (copiedBulkImage cfg m j σ hσ z) ≠
      bulkCode k j m (copiedBulkImage cfg m j ρ hρ z)) :
    ∃a : Fin j, ∃b : Bool,
      let D := differenceGraph k j (sourceWidth cfg m)
        (copiedPermutationExtension (schedule k j) j (sourceWidth cfg m) σ)
        (copiedPermutationExtension (schedule k j) j (sourceWidth cfg m) ρ)
      let L := copiedBulkOld cfg m j z
      let S := copiedRetiredAnchor cfg m j hj false a b
      let B := copiedRetiredAnchor cfg m j hj true a b
      L ≠ S ∧ L ≠ B ∧
        (((D S L=2 ∨ D S L = -2) ∧ D L S=0) ∨
         ((D L B=2 ∨ D L B = -2) ∧ D B L=0)) := by
  obtain ⟨a,b,h⟩ := changed_word_code_edge k j hj
    (copiedBulkImage cfg m j σ hσ z).1 (copiedBulkImage cfg m j ρ hρ z).1 hc
  refine ⟨a,b,?_,?_,?_⟩
  · exact fun he => copiedRetiredAnchor_fst_ne_bulk cfg m j hj false a b z
      (congrArg Sigma.fst he.symm)
  · exact fun he => copiedRetiredAnchor_fst_ne_bulk cfg m j hj true a b z
      (congrArg Sigma.fst he.symm)
  · simpa only [copied_anchor_bulk_edge cfg m j hj σ ρ hσ hρ,
      copied_bulk_anchor_edge cfg m j hj σ ρ hσ hρ] using h

end Ostmann.Characters.DiagonalEstimate

end

end OAI

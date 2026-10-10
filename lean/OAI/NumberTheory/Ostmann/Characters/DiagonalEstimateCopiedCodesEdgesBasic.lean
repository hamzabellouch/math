import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateCopiedCodesPermutation
import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseMatchingGraph

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.DiagonalEstimate
open Template HigherBiasSource HigherBiasSource.SourceTemplate TemplateDiagonalMatching
open Template.OneSidedPhase
attribute [local instance] Classical.propDecidable

def CopiedBulkPreserving {k : ℕ} (cfg : SourceConfiguration k) (m j : ℕ)
    (σ : Equiv.Perm (ActualCopied cfg m j)) : Prop :=
  ∀i,IsCopiedBulk cfg m j i → IsCopiedBulk cfg m j (σ i)

def copiedBulkImage {k : ℕ} (cfg : SourceConfiguration k) (m j : ℕ)
    (σ : Equiv.Perm (ActualCopied cfg m j)) (hσ : CopiedBulkPreserving cfg m j σ)
    (z : Word k j × Fin m) : Word k j × Fin m :=
  copiedBulkEquiv cfg m j ⟨σ (copiedBulk cfg m j z),hσ _ (copiedBulk_isBulk cfg m j z)⟩

theorem copiedBulk_image {k : ℕ} (cfg : SourceConfiguration k) (m j : ℕ)
    (σ : Equiv.Perm (ActualCopied cfg m j)) (hσ : CopiedBulkPreserving cfg m j σ)
    (z : Word k j × Fin m) :
    σ (copiedBulk cfg m j z) = copiedBulk cfg m j (copiedBulkImage cfg m j σ hσ z) := by
  exact (congrArg Subtype.val ((copiedBulkEquiv cfg m j).symm_apply_apply
    ⟨σ (copiedBulk cfg m j z),hσ _ (copiedBulk_isBulk cfg m j z)⟩)).symm

def copiedBulkOld {k : ℕ} (cfg : SourceConfiguration k) (m j : ℕ)
    (z : Word k j × Fin m) : (schedule k j).Constituent (sourceWidth cfg m) :=
  copiedConstituentOld (schedule k j) j (sourceWidth cfg m) (copiedBulk cfg m j z)

def copiedRetiredAnchor {k : ℕ} (cfg : SourceConfiguration k) (m j : ℕ) (hj : j ≤ k)
    (big : Bool) (a : Fin j) (b : Bool) : (schedule k j).Constituent (sourceWidth cfg m) :=
  ⟨(retiredAnchors k j hj big a b).val,⟨0,by
    rw [(retiredAnchors k j hj big a b).property.2]
    simp only [sourceWidth_anchor,Nat.zero_lt_one]⟩⟩

@[simp] theorem copiedPermutationExtension_retired {k : ℕ} (cfg : SourceConfiguration k)
    (m j : ℕ) (hj : j ≤ k) (σ : Equiv.Perm (ActualCopied cfg m j))
    (big : Bool) (a : Fin j) (b : Bool) :
    copiedPermutationExtension (schedule k j) j (sourceWidth cfg m) σ
      (copiedRetiredAnchor cfg m j hj big a b) = copiedRetiredAnchor cfg m j hj big a b := by
  apply copiedPermutationExtension_not_copied
  intro h
  exact (retiredAnchors k j hj big a b).property.1 h.1

theorem copiedRetiredAnchor_fst_ne_bulk {k : ℕ} (cfg : SourceConfiguration k)
    (m j : ℕ) (hj : j ≤ k) (big : Bool) (a : Fin j) (b : Bool) (z : Word k j × Fin m) :
    (copiedRetiredAnchor cfg m j hj big a b).1 ≠ (copiedBulkOld cfg m j z).1 := by
  intro he
  change (retiredAnchors k j hj big a b).val = z.1.val at he
  apply (retiredAnchors k j hj big a b).property.1
  rw [he]
  exact z.1.property.1

theorem copiedExtension_bulk_image {k : ℕ} (cfg : SourceConfiguration k) (m j : ℕ)
    (σ : Equiv.Perm (ActualCopied cfg m j)) (hσ : CopiedBulkPreserving cfg m j σ)
    (z : Word k j × Fin m) :
    copiedPermutationExtension (schedule k j) j (sourceWidth cfg m) σ (copiedBulkOld cfg m j z) =
      copiedBulkOld cfg m j (copiedBulkImage cfg m j σ hσ z) := by
  rw [copiedBulkOld,copiedPermutationExtension_copied,copiedBulk_image cfg m j σ hσ z]
  rfl

end Ostmann.Characters.DiagonalEstimate

end

end OAI

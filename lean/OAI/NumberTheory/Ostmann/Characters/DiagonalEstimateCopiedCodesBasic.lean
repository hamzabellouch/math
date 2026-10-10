import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateNormalizationCounts
import OAI.NumberTheory.Ostmann.Characters.TemplateDiagonalMatchingWhole

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.DiagonalEstimate
open Template HigherBiasSource HigherBiasSource.SourceTemplate TemplateDiagonalMatching
attribute [local instance] Classical.propDecidable

abbrev ActualCopied {k : ℕ} (cfg : SourceConfiguration k) (m j : ℕ) :=
  CopiedConstituent (schedule k j) j (sourceWidth cfg m)

def IsCopiedBulk {k : ℕ} (cfg : SourceConfiguration k) (m j : ℕ)
    (i : ActualCopied cfg m j) : Prop :=
  (schedule k j).role i.1.val = .word ∧ i.2.val < m

abbrev CopiedNonbulk {k : ℕ} (cfg : SourceConfiguration k) (m j : ℕ) :=
  {i : ActualCopied cfg m j // ¬IsCopiedBulk cfg m j i}

def copiedBulk {k : ℕ} (cfg : SourceConfiguration k) (m j : ℕ)
    (z : Word k j × Fin m) : ActualCopied cfg m j :=
  ⟨⟨z.1.val,word_copied _ _ _ z.1.property.1 z.1.property.2⟩,
    ⟨z.2.val,by simpa only [z.1.property.2,sourceWidth_word] using
      Nat.lt_succ_of_lt z.2.isLt⟩⟩

@[simp] theorem copiedBulk_isBulk {k : ℕ} (cfg : SourceConfiguration k) (m j : ℕ)
    (z : Word k j × Fin m) : IsCopiedBulk cfg m j (copiedBulk cfg m j z) :=
  ⟨z.1.property.2,z.2.isLt⟩

def copiedBulkEquiv {k : ℕ} (cfg : SourceConfiguration k) (m j : ℕ) :
    {i : ActualCopied cfg m j // IsCopiedBulk cfg m j i} ≃ Word k j × Fin m where
  toFun i := (⟨i.val.1.val,i.val.1.property.1,i.property.1⟩,
    ⟨i.val.2.val,i.property.2⟩)
  invFun z := ⟨copiedBulk cfg m j z,copiedBulk_isBulk cfg m j z⟩
  left_inv i := by rcases i with ⟨⟨⟨i,hi⟩,⟨a,ha⟩⟩,h⟩; rfl
  right_inv z := rfl

def copiedBulkNonbulkEquiv {k : ℕ} (cfg : SourceConfiguration k) (m j : ℕ) :
    ActualCopied cfg m j ≃ (Word k j × Fin m) ⊕ CopiedNonbulk cfg m j :=
  (Equiv.sumCompl (IsCopiedBulk cfg m j)).symm.trans
    (Equiv.sumCongr (copiedBulkEquiv cfg m j) (Equiv.refl _))

@[simp] theorem copiedBulkNonbulkEquiv_bulk {k : ℕ} (cfg : SourceConfiguration k) (m j : ℕ)
    (z : Word k j × Fin m) :
    copiedBulkNonbulkEquiv cfg m j (copiedBulk cfg m j z) = Sum.inl z := by
  change (Equiv.sumCongr (copiedBulkEquiv cfg m j) (Equiv.refl _))
    ((Equiv.sumCompl (IsCopiedBulk cfg m j)).symm (copiedBulk cfg m j z)) = _
  rw [Equiv.sumCompl_symm_apply_of_pos (copiedBulk_isBulk cfg m j z)]
  rfl

@[simp] theorem copiedBulkNonbulkEquiv_nonbulk {k : ℕ} (cfg : SourceConfiguration k) (m j : ℕ)
    (z : CopiedNonbulk cfg m j) :
    copiedBulkNonbulkEquiv cfg m j z.val = Sum.inr z := by
  simp only [copiedBulkNonbulkEquiv,Equiv.trans_apply,
    Equiv.sumCompl_symm_apply_of_neg z.property,Equiv.sumCongr_apply,Sum.map_inr,
    Equiv.refl_apply]

theorem copied_top_nonbulk {k : ℕ} (cfg : SourceConfiguration k) (m j : ℕ)
    (i : ActualCopied cfg m j) (hi : i.2.val = m) : ¬IsCopiedBulk cfg m j i := by
  intro h
  have hh := h.2
  rw [hi] at hh
  exact (Nat.lt_irrefl m) hh

end Ostmann.Characters.DiagonalEstimate

end

end OAI

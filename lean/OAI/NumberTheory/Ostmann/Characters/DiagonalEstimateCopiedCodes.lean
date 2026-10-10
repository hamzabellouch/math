import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateCopiedCodesBasic

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.DiagonalEstimate
open Template HigherBiasSource HigherBiasSource.SourceTemplate TemplateDiagonalMatching
attribute [local instance] Classical.propDecidable

def codePermCongr {I J C : Type*} (e : I ≃ J) (code : J → C) :
    CodePerm (fun i => code (e i)) ≃ CodePerm code :=
  Equiv.subtypeEquiv e.permCongr (by
    intro σ
    constructor
    · intro h y
      simpa only [Equiv.permCongr_apply,Equiv.apply_symm_apply] using h (e.symm y)
    · intro h i
      simpa only [Equiv.permCongr_apply,Equiv.symm_apply_apply] using h (e i))

def actualCopiedCode {k : ℕ} (cfg : SourceConfiguration k) (m j : ℕ) :
    ActualCopied cfg m j → (Fin j → ℤˣ × ℤˣ) ⊕ Unit :=
  fun i => wholeCode k j m (CopiedNonbulk cfg m j) (copiedBulkNonbulkEquiv cfg m j i)

@[simp] theorem actualCopiedCode_bulk {k : ℕ} (cfg : SourceConfiguration k) (m j : ℕ)
    (z : Word k j × Fin m) :
    actualCopiedCode cfg m j (copiedBulk cfg m j z) = Sum.inl (bulkCode k j m z) := by
  rw [actualCopiedCode,copiedBulkNonbulkEquiv_bulk]
  rfl

@[simp] theorem actualCopiedCode_nonbulk {k : ℕ} (cfg : SourceConfiguration k) (m j : ℕ)
    (z : CopiedNonbulk cfg m j) : actualCopiedCode cfg m j z.val = Sum.inr () := by
  rw [actualCopiedCode,copiedBulkNonbulkEquiv_nonbulk]
  rfl

instance actualCopiedCodePermFintype {k : ℕ} (cfg : SourceConfiguration k) (m j : ℕ) :
    Fintype (CodePerm (actualCopiedCode cfg m j)) := Subtype.fintype _

theorem actualCopiedCodePerm_card_le {k : ℕ} (cfg : SourceConfiguration k) (m j : ℕ) :
    Fintype.card (CodePerm (actualCopiedCode cfg m j)) ≤
      (2*m)^(2^j*m) * (Fintype.card (CopiedNonbulk cfg m j))^
        (Fintype.card (CopiedNonbulk cfg m j)) := by
  classical
  change Fintype.card (CodePerm (fun i => wholeCode k j m (CopiedNonbulk cfg m j)
    (copiedBulkNonbulkEquiv cfg m j i))) ≤ _
  rw [Fintype.card_congr (codePermCongr (copiedBulkNonbulkEquiv cfg m j)
    (wholeCode k j m (CopiedNonbulk cfg m j)))]
  exact wholeCodePerm_card_le k j m (CopiedNonbulk cfg m j)

end Ostmann.Characters.DiagonalEstimate

end

end OAI

import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateCopiedCodesCounts
import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateCopiedCodesEdges
import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateCopiedCodesShells

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.DiagonalEstimate
open Template HigherBiasSource HigherBiasSource.SourceTemplate TemplateDiagonalMatching
attribute [local instance] Classical.propDecidable

def copiedRetiredOutside {k : ℕ} (cfg : SourceConfiguration k) (m j : ℕ) (hj : j ≤ k)
    (big : Bool) (a : Fin j) (b : Bool) :
    OutsideConstituent (schedule k j) j (sourceWidth cfg m) :=
  ⟨⟨(retiredAnchors k j hj big a b).val,
    ⟨fun h => (retiredAnchors k j hj big a b).property.1 h.1,
     fun h => (retiredAnchors k j hj big a b).property.1 h.1⟩⟩,
    (copiedRetiredAnchor cfg m j hj big a b).2⟩

@[simp] theorem copiedRetiredOutside_old {k : ℕ} (cfg : SourceConfiguration k)
    (m j : ℕ) (hj : j ≤ k) (big : Bool) (a : Fin j) (b : Bool) :
    outsideConstituentOld (schedule k j) j (sourceWidth cfg m)
      (copiedRetiredOutside cfg m j hj big a b) = copiedRetiredAnchor cfg m j hj big a b := rfl

theorem exists_bulk_code_change {k : ℕ} (cfg : SourceConfiguration k) (m j : ℕ)
    (σ ρ : Equiv.Perm (ActualCopied cfg m j))
    (hσ : ∀i,IsCopiedBulk cfg m j (σ i) ↔ IsCopiedBulk cfg m j i)
    (hρ : ∀i,IsCopiedBulk cfg m j (ρ i) ↔ IsCopiedBulk cfg m j i)
    (hc : ¬∀i,actualCopiedCode cfg m j (σ i) = actualCopiedCode cfg m j (ρ i)) :
    ∃z : Word k j × Fin m,
      bulkCode k j m (copiedBulkImage cfg m j σ (fun i hi => (hσ i).mpr hi) z) ≠
      bulkCode k j m (copiedBulkImage cfg m j ρ (fun i hi => (hρ i).mpr hi) z) := by
  by_contra hn
  push Not at hn
  apply hc
  intro i
  by_cases hi : IsCopiedBulk cfg m j i
  · let z := copiedBulkEquiv cfg m j ⟨i,hi⟩
    have hz : copiedBulk cfg m j z = i :=
      congrArg Subtype.val ((copiedBulkEquiv cfg m j).symm_apply_apply ⟨i,hi⟩)
    rw [←hz,copiedBulk_image cfg m j σ (fun i hi => (hσ i).mpr hi) z,
      copiedBulk_image cfg m j ρ (fun i hi => (hρ i).mpr hi) z,
      actualCopiedCode_bulk,actualCopiedCode_bulk]
    exact congrArg Sum.inl (hn z)
  · have hsi : ¬IsCopiedBulk cfg m j (σ i) := fun h => hi ((hσ i).mp h)
    have hri : ¬IsCopiedBulk cfg m j (ρ i) := fun h => hi ((hρ i).mp h)
    exact (actualCopiedCode_nonbulk cfg m j ⟨σ i,hsi⟩).trans
      (actualCopiedCode_nonbulk cfg m j ⟨ρ i,hri⟩).symm

end Ostmann.Characters.DiagonalEstimate

end

end OAI

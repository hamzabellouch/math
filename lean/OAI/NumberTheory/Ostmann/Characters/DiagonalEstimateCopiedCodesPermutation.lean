import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateCopiedCodes

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.DiagonalEstimate
open Template HigherBiasSource HigherBiasSource.SourceTemplate TemplateDiagonalMatching
attribute [local instance] Classical.propDecidable

def copiedOldEmbedding (T : Layout) (j : ℕ) (width : Role → ℕ) :
    CopiedConstituent T j width ↪ T.Constituent width where
  toFun := copiedConstituentOld T j width
  inj' := by
    rintro ⟨⟨i,hi⟩,a⟩ ⟨⟨h,hh⟩,b⟩ he
    have hih : i = h := congrArg Sigma.fst he
    subst h
    have hab : a = b := by simpa only [copiedConstituentOld,Sigma.mk.inj_iff,heq_eq_eq,
      true_and] using he
    subst b
    rfl

def copiedPermutationExtension (T : Layout) (j : ℕ) (width : Role → ℕ)
    (σ : Equiv.Perm (CopiedConstituent T j width)) : Equiv.Perm (T.Constituent width) :=
  σ.viaEmbedding (copiedOldEmbedding T j width)

@[simp] theorem copiedPermutationExtension_copied (T : Layout) (j : ℕ) (width : Role → ℕ)
    (σ : Equiv.Perm (CopiedConstituent T j width)) (i : CopiedConstituent T j width) :
    copiedPermutationExtension T j width σ (copiedConstituentOld T j width i) =
      copiedConstituentOld T j width (σ i) :=
  Equiv.Perm.viaEmbedding_apply _ _ _

theorem copiedPermutationExtension_not_copied (T : Layout) (j : ℕ) (width : Role → ℕ)
    (σ : Equiv.Perm (CopiedConstituent T j width)) (i : T.Constituent width)
    (hi : ¬T.IsCopied j i.1) : copiedPermutationExtension T j width σ i = i := by
  apply Equiv.Perm.viaEmbedding_apply_of_notMem
  rintro ⟨z,hz⟩
  apply hi
  have he := congrArg Sigma.fst hz
  exact he ▸ z.1.property

@[simp] theorem copiedPermutationExtension_outside (T : Layout) (j : ℕ) (width : Role → ℕ)
    (σ : Equiv.Perm (CopiedConstituent T j width)) (i : OutsideConstituent T j width) :
    copiedPermutationExtension T j width σ (outsideConstituentOld T j width i) =
      outsideConstituentOld T j width i :=
  copiedPermutationExtension_not_copied T j width σ _ i.1.property.2

theorem copiedPermutationExtension_pivot (T : Layout) (j : ℕ) (width : Role → ℕ)
    (σ : Equiv.Perm (CopiedConstituent T j width)) (i : T.Constituent width)
    (hi : T.IsPivot j i.1) : copiedPermutationExtension T j width σ i = i :=
  copiedPermutationExtension_not_copied T j width σ i (pivot_not_copied T j i.1 hi)

@[simp] theorem copiedPermutationExtension_bulk {k : ℕ} (cfg : SourceConfiguration k) (m j : ℕ)
    (σ : Equiv.Perm (ActualCopied cfg m j)) (z : Word k j × Fin m) :
    copiedPermutationExtension (schedule k j) j (sourceWidth cfg m) σ
      (copiedConstituentOld (schedule k j) j (sourceWidth cfg m) (copiedBulk cfg m j z)) =
    copiedConstituentOld (schedule k j) j (sourceWidth cfg m) (σ (copiedBulk cfg m j z)) :=
  copiedPermutationExtension_copied _ _ _ _ _

theorem copiedPermutationExtension_anchor {k : ℕ} (cfg : SourceConfiguration k) (m j : ℕ)
    (hj : j < k) (big : Bool) (σ : Equiv.Perm (ActualCopied cfg m j))
    (a : Fin (sourceWidth cfg m ((schedule k j).role (anchorCopied k j hj big).val))) :
    copiedPermutationExtension (schedule k j) j (sourceWidth cfg m) σ
      (copiedConstituentOld (schedule k j) j (sourceWidth cfg m) ⟨anchorCopied k j hj big,a⟩) =
    copiedConstituentOld (schedule k j) j (sourceWidth cfg m) (σ ⟨anchorCopied k j hj big,a⟩) :=
  copiedPermutationExtension_copied _ _ _ _ _

end Ostmann.Characters.DiagonalEstimate

end

end OAI

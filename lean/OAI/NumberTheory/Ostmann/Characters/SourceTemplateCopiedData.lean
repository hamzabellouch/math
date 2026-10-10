import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateCopiedCodesPermutation
import OAI.NumberTheory.Ostmann.Characters.SourceTemplateEligibleData

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.HigherBiasSource.SourceTemplate
open Construction Preliminaries Template DiagonalEstimate
attribute [local instance] Classical.propDecidable

theorem source_copied_characters {k Q : ℕ} (cfg : SourceConfiguration k) (m j : ℕ)
    (χ : (q:ℕ) → MulChar (ZMod q) ℂ)
    (σ : Equiv.Perm (CopiedConstituent (schedule k j) j (sourceWidth cfg m)))
    (i : (schedule k j).Constituent (sourceWidth cfg m)) (p : PrimeUpTo Q) :
    scheduledCharacterData k (sourceWidth cfg m) (sourceCharacterData cfg m (fun _=>χ)) j
      (copiedPermutationExtension (schedule k j) j (sourceWidth cfg m) σ i) p =
    scheduledCharacterData k (sourceWidth cfg m) (sourceCharacterData cfg m (fun _=>χ)) j i p := by
  by_cases hi : (schedule k j).IsCopied j i.1
  · let z : CopiedConstituent (schedule k j) j (sourceWidth cfg m) := ⟨⟨i.1,hi⟩,i.2⟩
    have he : copiedPermutationExtension (schedule k j) j (sourceWidth cfg m) σ i =
        copiedConstituentOld (schedule k j) j (sourceWidth cfg m) (σ z) :=
      copiedPermutationExtension_copied (schedule k j) j (sourceWidth cfg m) σ z
    rw [he]
    exact (scheduled_sourceCharacterData_copied cfg m j j χ
      (copiedConstituentOld (schedule k j) j (sourceWidth cfg m) (σ z)) (σ z).1.property p).trans
      (scheduled_sourceCharacterData_copied cfg m j j χ i hi p).symm
  · rw [copiedPermutationExtension_not_copied (schedule k j) j (sourceWidth cfg m) σ i hi]

theorem source_copied_centers {k Q : ℕ} (cfg : SourceConfiguration k) (m j : ℕ)
    (a : (q:ℕ) → ZMod q)
    (σ : Equiv.Perm (CopiedConstituent (schedule k j) j (sourceWidth cfg m)))
    (i : (schedule k j).Constituent (sourceWidth cfg m)) (p : PrimeUpTo Q) :
    scheduledTranslationData k (sourceWidth cfg m) (sourceTranslationData cfg m (fun _=>a)) j
      (copiedPermutationExtension (schedule k j) j (sourceWidth cfg m) σ i) p =
    scheduledTranslationData k (sourceWidth cfg m) (sourceTranslationData cfg m (fun _=>a)) j i p := by
  rw [scheduled_sourceTranslationData_all,scheduled_sourceTranslationData_all]

end Ostmann.Characters.HigherBiasSource.SourceTemplate

end

end OAI

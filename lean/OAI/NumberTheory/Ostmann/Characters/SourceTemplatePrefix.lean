import OAI.NumberTheory.Ostmann.Characters.SourceTemplatePrefixData

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.HigherBiasSource.SourceTemplate
open Construction Preliminaries Template ParityActions OneSidedPhase HigherBiasSourceWord
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem scheduled_sourceShell_prefix {k Q : ℕ} (cfg : SourceConfiguration k) (m n : ℕ)
    (hm : m ≤ sourceWidth cfg m .word) (bulk top E : Finset (PrimeUpTo Q))
    (z : BulkSlot k n m) :
    scheduledPrimeShells k (sourceWidth cfg m) (configurationPrimeShells cfg m bulk top E) (n+1)
      (prefixBulkEmbedding k n (sourceWidth cfg m) m hm z) = bulk := by
  change scheduledPrimeShells k (sourceWidth cfg m) (configurationPrimeShells cfg m bulk top E) (n+1)
    ⟨z.1.val,Fin.cast (congrArg (sourceWidth cfg m) z.1.property.2).symm (z.2.castLE hm)⟩ = bulk
  rw [scheduledPrimeShells_word cfg m (n+1) bulk top E z.1.val z.1.property.2]
  change roleShells bulk top m (Fin.castAdd 1 z.2) = bulk
  exact Fin.append_left _ _ _

theorem scheduled_sourceCharacter_prefix {k Q : ℕ} (cfg : SourceConfiguration k) (m n : ℕ)
    (hm : m ≤ sourceWidth cfg m .word) (χ : (q:ℕ) → MulChar (ZMod q) ℂ)
    (z : BulkSlot k n m) (p : PrimeUpTo Q) :
    scheduledCharacterData k (sourceWidth cfg m) (sourceCharacterData cfg m (fun _=>χ)) (n+1)
      (prefixBulkEmbedding k n (sourceWidth cfg m) m hm z) p = χ p.val :=
  scheduled_sourceCharacterData_word cfg m (n+1) χ z.1.val z.1.property.1 z.1.property.2 _ p

theorem scheduled_sourceTranslation_prefix {k Q : ℕ} (cfg : SourceConfiguration k) (m n : ℕ)
    (hm : m ≤ sourceWidth cfg m .word) (a : (q:ℕ) → ZMod q)
    (z : BulkSlot k n m) (p : PrimeUpTo Q) :
    scheduledTranslationData k (sourceWidth cfg m) (sourceTranslationData cfg m (fun _=>a)) (n+1)
      (prefixBulkEmbedding k n (sourceWidth cfg m) m hm z) p = a p.val :=
  scheduled_sourceTranslationData_word cfg m (n+1) a z.1.val z.1.property.1 z.1.property.2 _ p

theorem source_prefix_shells {k Q : ℕ} (cfg : SourceConfiguration k) (m n : ℕ)
    (hm : m ≤ sourceWidth cfg m .word) (bulk top E : Finset (PrimeUpTo Q))
    (σ : Reassignments k n m) (i : (schedule k (n+1)).Constituent (sourceWidth cfg m)) :
    scheduledPrimeShells k (sourceWidth cfg m) (configurationPrimeShells cfg m bulk top E) (n+1)
      (prefixConstituentPermutation k n (sourceWidth cfg m) m hm σ i) =
    scheduledPrimeShells k (sourceWidth cfg m) (configurationPrimeShells cfg m bulk top E) (n+1) i :=
  prefixConstituentPermutation_shells k n (sourceWidth cfg m) m hm _ (fun _=>bulk)
    (scheduled_sourceShell_prefix cfg m n hm bulk top E) σ i

theorem source_prefix_characters {k Q : ℕ} (cfg : SourceConfiguration k) (m n : ℕ)
    (hm : m ≤ sourceWidth cfg m .word) (χ : (q:ℕ) → MulChar (ZMod q) ℂ)
    (σ : Reassignments k n m) (i : (schedule k (n+1)).Constituent (sourceWidth cfg m))
    (p : PrimeUpTo Q) :
    scheduledCharacterData k (sourceWidth cfg m) (sourceCharacterData cfg m (fun _=>χ)) (n+1)
      (prefixConstituentPermutation k n (sourceWidth cfg m) m hm σ i) p =
    scheduledCharacterData k (sourceWidth cfg m) (sourceCharacterData cfg m (fun _=>χ)) (n+1) i p := by
  by_cases hi : i∈Set.range (prefixBulkEmbedding k n (sourceWidth cfg m) m hm)
  · obtain ⟨z,rfl⟩ := hi
    rw [prefixConstituentPermutation_bulk,scheduled_sourceCharacter_prefix,
      scheduled_sourceCharacter_prefix]
  · rw [show prefixConstituentPermutation k n (sourceWidth cfg m) m hm σ i = i from
      Equiv.Perm.viaEmbedding_apply_of_notMem _ _ i hi]

theorem source_prefix_centers {k Q : ℕ} (cfg : SourceConfiguration k) (m n : ℕ)
    (hm : m ≤ sourceWidth cfg m .word) (a : (q:ℕ) → ZMod q)
    (σ : Reassignments k n m) (i : (schedule k (n+1)).Constituent (sourceWidth cfg m))
    (p : PrimeUpTo Q) :
    scheduledTranslationData k (sourceWidth cfg m) (sourceTranslationData cfg m (fun _=>a)) (n+1)
      (prefixConstituentPermutation k n (sourceWidth cfg m) m hm σ i) p =
    scheduledTranslationData k (sourceWidth cfg m) (sourceTranslationData cfg m (fun _=>a)) (n+1) i p := by
  by_cases hi : i∈Set.range (prefixBulkEmbedding k n (sourceWidth cfg m) m hm)
  · obtain ⟨z,rfl⟩ := hi
    rw [prefixConstituentPermutation_bulk,scheduled_sourceTranslation_prefix,
      scheduled_sourceTranslation_prefix]
  · rw [show prefixConstituentPermutation k n (sourceWidth cfg m) m hm σ i = i from
      Equiv.Perm.viaEmbedding_apply_of_notMem _ _ i hi]

end Ostmann.Characters.HigherBiasSource.SourceTemplate

end

end OAI

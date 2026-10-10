import OAI.NumberTheory.Ostmann.Characters.SourceTemplatePrefixData

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.HigherBiasSource.SourceTemplate
open Construction Preliminaries Template
attribute [local instance] Classical.propDecidable

theorem scheduled_sourceCharacterData_eligible {k Q : ℕ} (cfg : SourceConfiguration k)
    (m j : ℕ) (χ : (q:ℕ) → MulChar (ZMod q) ℂ)
    (i : (schedule k j).Constituent (sourceWidth cfg m))
    (he : (schedule k j).eligible i.1) (p : PrimeUpTo Q) :
    scheduledCharacterData k (sourceWidth cfg m) (sourceCharacterData cfg m (fun _=>χ)) j i p =
      χ p.val := by
  unfold scheduledCharacterData
  have hel := scheduledConstituentOrigin_eligible k (sourceWidth cfg m) j i he
  generalize ho : scheduledConstituentOrigin k (sourceWidth cfg m) j i = x at hel ⊢
  rcases x with ⟨⟨r,b⟩,a⟩
  have hb : b = true := hel.1
  subst b
  change characterDoubleChar (fun _=>χ)
    (Fin.castAdd (sourceHalfSize cfg m) (halfRoleIndexEquiv cfg m ⟨r,a⟩)) p.val = χ p.val
  simp only [characterDoubleChar,Fin.append_left]

theorem scheduled_sourceCharacterData_copied {k Q : ℕ} (cfg : SourceConfiguration k)
    (m j l : ℕ) (χ : (q:ℕ) → MulChar (ZMod q) ℂ)
    (i : (schedule k j).Constituent (sourceWidth cfg m))
    (he : (schedule k j).IsCopied l i.1) (p : PrimeUpTo Q) :
    scheduledCharacterData k (sourceWidth cfg m) (sourceCharacterData cfg m (fun _=>χ)) j i p =
      χ p.val := scheduled_sourceCharacterData_eligible cfg m j χ i he.1 p

theorem scheduled_sourceTranslationData_all {k Q : ℕ} (cfg : SourceConfiguration k)
    (m j : ℕ) (a₀ : (q:ℕ) → ZMod q)
    (i : (schedule k j).Constituent (sourceWidth cfg m)) (p : PrimeUpTo Q) :
    scheduledTranslationData k (sourceWidth cfg m) (sourceTranslationData cfg m (fun _=>a₀)) j i p =
      a₀ p.val := by
  unfold scheduledTranslationData
  generalize ho : scheduledConstituentOrigin k (sourceWidth cfg m) j i = x
  rcases x with ⟨⟨r,b⟩,a⟩
  cases b
  · change characterDoubleCenter (fun _=>a₀)
      (Fin.natAdd (sourceHalfSize cfg m) (halfRoleIndexEquiv cfg m ⟨r,a⟩)) p.val = a₀ p.val
    simp only [characterDoubleCenter,Fin.append_right]
  · change characterDoubleCenter (fun _=>a₀)
      (Fin.castAdd (sourceHalfSize cfg m) (halfRoleIndexEquiv cfg m ⟨r,a⟩)) p.val = a₀ p.val
    simp only [characterDoubleCenter,Fin.append_left]

end Ostmann.Characters.HigherBiasSource.SourceTemplate

end

end OAI

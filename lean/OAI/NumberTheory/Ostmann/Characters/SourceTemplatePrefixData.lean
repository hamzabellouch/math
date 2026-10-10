import OAI.NumberTheory.Ostmann.Characters.SourceTemplatePhaseDefs
import OAI.NumberTheory.Ostmann.Characters.SourceTemplateShells
import OAI.NumberTheory.Ostmann.Characters.TemplateAmplitudeRecurrenceScheduledData
import OAI.NumberTheory.Ostmann.Characters.TemplateTerminalParity

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.HigherBiasSource.SourceTemplate
open Construction Preliminaries Template ParityActions OneSidedPhase
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem scheduledConstituentOrigin_eligible (k : ℕ) (width : Role → ℕ) (j : ℕ)
    (i : (schedule k j).Constituent width) (hi : (schedule k j).eligible i.1) :
    (schedule k 0).eligible (scheduledConstituentOrigin k width j i).1 := by
  induction j with
  | zero => exact hi
  | succ j ih =>
    rcases i with ⟨i,a⟩
    cases i with
    | inl z => exact ih ⟨z.1.val,a⟩ z.1.property.1
    | inr z => exact ih ⟨z.val,a⟩ hi

theorem scheduled_sourceCharacterData_word {k Q : ℕ} (cfg : SourceConfiguration k)
    (m j : ℕ) (χ : (q:ℕ) → MulChar (ZMod q) ℂ)
    (i : (schedule k j).Slot) (he : (schedule k j).eligible i)
    (hi : (schedule k j).role i = .word)
    (a : Fin (sourceWidth cfg m ((schedule k j).role i))) (p : PrimeUpTo Q) :
    scheduledCharacterData k (sourceWidth cfg m) (sourceCharacterData cfg m (fun _=>χ)) j ⟨i,a⟩ p =
      χ p.val := by
  unfold scheduledCharacterData
  have hr := scheduledConstituentOrigin_role k (sourceWidth cfg m) j ⟨i,a⟩
  have hel := scheduledConstituentOrigin_eligible k (sourceWidth cfg m) j ⟨i,a⟩ he
  rw [hi] at hr
  generalize ho : scheduledConstituentOrigin k (sourceWidth cfg m) j ⟨i,a⟩ = x at hr hel ⊢
  rcases x with ⟨⟨r,b⟩,v⟩
  have hb : b = true := hel.1
  subst b
  have hh : r = .word := by
    change r.role = .word at hr
    cases r <;> simp_all [InitialRole.role]
  subst r
  unfold sourceCharacterData
  rw [sourceIndexEquiv_word_true cfg m v]
  simp only [characterDoubleChar,Fin.append_left]

theorem scheduled_sourceTranslationData_word {k Q : ℕ} (cfg : SourceConfiguration k)
    (m j : ℕ) (a₀ : (q:ℕ) → ZMod q)
    (i : (schedule k j).Slot) (he : (schedule k j).eligible i)
    (hi : (schedule k j).role i = .word)
    (a : Fin (sourceWidth cfg m ((schedule k j).role i))) (p : PrimeUpTo Q) :
    scheduledTranslationData k (sourceWidth cfg m) (sourceTranslationData cfg m (fun _=>a₀)) j ⟨i,a⟩ p =
      a₀ p.val := by
  unfold scheduledTranslationData
  have hr := scheduledConstituentOrigin_role k (sourceWidth cfg m) j ⟨i,a⟩
  have hel := scheduledConstituentOrigin_eligible k (sourceWidth cfg m) j ⟨i,a⟩ he
  rw [hi] at hr
  generalize ho : scheduledConstituentOrigin k (sourceWidth cfg m) j ⟨i,a⟩ = x at hr hel ⊢
  rcases x with ⟨⟨r,b⟩,v⟩
  have hb : b = true := hel.1
  subst b
  have hh : r = .word := by
    change r.role = .word at hr
    cases r <;> simp_all [InitialRole.role]
  subst r
  unfold sourceTranslationData
  rw [sourceIndexEquiv_word_true cfg m v]
  simp only [characterDoubleCenter,Fin.append_left]

end Ostmann.Characters.HigherBiasSource.SourceTemplate

end

end OAI

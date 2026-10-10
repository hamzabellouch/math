import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedPhaseSurvivingRetained

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.Template.OneSidedPhase
open Preliminaries HigherBiasSource HigherBiasSource.SourceTemplate

theorem orderOf_star_character {q : ℕ} (χ : MulChar (ZMod q) ℂ) :
    orderOf (star χ)=orderOf χ := by
  rw [orderOf_eq_orderOf_iff]
  intro n
  rw [←star_pow]
  exact star_injective.eq_iff' (by simp)

theorem scheduled_sourceCharacterData_order {k Q : ℕ} (cfg : SourceConfiguration k)
    (m j : ℕ) (χ : (q:ℕ)→MulChar (ZMod q) ℂ)
    (i : (schedule k j).Constituent (sourceWidth cfg m)) (p : PrimeUpTo Q) :
    orderOf (scheduledCharacterData k (sourceWidth cfg m)
      (sourceCharacterData cfg m (fun _=>χ)) j i p)=orderOf (χ p.val) := by
  unfold scheduledCharacterData
  generalize ho : scheduledConstituentOrigin k (sourceWidth cfg m) j i = x
  rcases x with ⟨⟨r,b⟩,a⟩
  cases b
  · change orderOf (characterDoubleChar (fun _=>χ)
      (Fin.natAdd (sourceHalfSize cfg m) (halfRoleIndexEquiv cfg m ⟨r,a⟩)) p.val)=_
    simp only [characterDoubleChar,Fin.append_right,orderOf_star_character]
  · change orderOf (characterDoubleChar (fun _=>χ)
      (Fin.castAdd (sourceHalfSize cfg m) (halfRoleIndexEquiv cfg m ⟨r,a⟩)) p.val)=_
    simp only [characterDoubleChar,Fin.append_left]

end Ostmann.Characters.Template.OneSidedPhase

end

end OAI

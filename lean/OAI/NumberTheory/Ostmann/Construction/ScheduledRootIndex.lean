import OAI.NumberTheory.Ostmann.Construction.ScheduledFrequencyHistory

namespace OAI

/-! # The root frequency as an element of its actual finite cutoff range -/

namespace Ostmann

noncomputable def scheduledRootIndex (V : ℕ → ℕ) (n : ℕ)
    (d : ScheduledFrequencyIndex V n) : transferFrequencyRange (V n) :=
  ⟨frequencyRoot n (scheduledFrequencyHistory V n d),
    (mem_transferFrequencyRange _ _).mpr (scheduledFrequencyHistory_root_bound V n d)⟩

theorem scheduledRootIndex_eq_iff (V : ℕ → ℕ) (n : ℕ) (d d' : ScheduledFrequencyIndex V n) :
    scheduledRootIndex V n d = scheduledRootIndex V n d' ↔
      frequencyRoot n (scheduledFrequencyHistory V n d) =
        frequencyRoot n (scheduledFrequencyHistory V n d') := Subtype.ext_iff

end Ostmann

end OAI

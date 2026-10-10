import OAI.NumberTheory.Ostmann.Construction.ConstituentGuardedNext

namespace OAI

/-! # Finite frequency histories with the actual cutoff at every level -/

namespace Ostmann

open scoped Classical

def ScheduledFrequencyIndex (V : ℕ → ℕ) : ℕ → Type
  | 0 => transferFrequencyRange (V 0)
  | n + 1 => (transferFrequencyRange (V (n + 1))) ×
      (ScheduledFrequencyIndex V n × ScheduledFrequencyIndex V n)

instance scheduledFrequencyIndexFintype (V : ℕ → ℕ) (n : ℕ) :
    Fintype (ScheduledFrequencyIndex V n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype (transferFrequencyRange (V 0)))
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (Fintype ((transferFrequencyRange (V (n + 1))) ×
      (ScheduledFrequencyIndex V n × ScheduledFrequencyIndex V n)))

noncomputable def scheduledFrequencyHistory (V : ℕ → ℕ) :
    (n : ℕ) → ScheduledFrequencyIndex V n → FrequencyTree ℤ n
  | 0, a => a.val
  | n + 1, a => (a.1.val, scheduledFrequencyHistory V n a.2.1, scheduledFrequencyHistory V n a.2.2)

theorem scheduledFrequencyHistory_succ (V : ℕ → ℕ) (n : ℕ) :
    scheduledFrequencyHistory V (n + 1) =
      copiedConstituentHistory (scheduledFrequencyHistory V n) (V (n + 1)) := rfl

theorem scheduledFrequencyHistory_root_bound (V : ℕ → ℕ) (n : ℕ)
    (a : ScheduledFrequencyIndex V n) :
    (frequencyRoot n (scheduledFrequencyHistory V n a)).natAbs ≤ V n := by
  cases n with
  | zero => exact (mem_transferFrequencyRange _ _).mp a.property
  | succ n => exact (mem_transferFrequencyRange _ _).mp a.1.property

/-- The largest level cutoff controls every actual child frequency. -/
theorem scheduledFrequencyHistory_all_bound (V : ℕ → ℕ) (hV : Monotone V) (n : ℕ)
    (a : ScheduledFrequencyIndex V n) (s : ℤ)
    (hs : s ∈ allFrequencyList n (scheduledFrequencyHistory V n a)) : s.natAbs ≤ V n := by
  induction n with
  | zero =>
    have he : s = a.val := by simpa only [allFrequencyList, scheduledFrequencyHistory, List.mem_singleton] using hs
    subst s
    exact scheduledFrequencyHistory_root_bound V 0 a
  | succ n ih =>
    rcases List.mem_cons.mp hs with he | hc
    · subst s
      exact scheduledFrequencyHistory_root_bound V (n + 1) a
    · rcases List.mem_append.mp hc with hL | hR
      · exact (ih a.2.1 hL).trans (hV (Nat.le_succ n))
      · exact (ih a.2.2 hR).trans (hV (Nat.le_succ n))

theorem scheduledFrequencyHistory_injective (V : ℕ → ℕ) (n : ℕ) :
    Function.Injective (scheduledFrequencyHistory V n) := by
  induction n with
  | zero => exact Subtype.val_injective
  | succ n ih =>
    intro a b he
    have hr : a.1 = b.1 := Subtype.ext (congrArg Prod.fst he)
    have hl := ih (congrArg (fun x : FrequencyTree ℤ (n + 1) => x.2.1) he)
    have hright := ih (congrArg (fun x : FrequencyTree ℤ (n + 1) => x.2.2) he)
    exact Prod.ext hr (Prod.ext hl hright)

end Ostmann

end OAI

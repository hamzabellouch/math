import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.RecorderSimulation

namespace OAI

noncomputable section
namespace BalancedTransport.Recorder.Checkpoint

theorem coded_halting_iff {Q Γ : Type*} [Fintype Q] [Fintype Γ]
    [DecidableEq Q] [DecidableEq Γ] (M : Machine Q Γ) (c : Checkpoint Q Γ) :
    (∃ n d, Exec M n (c.expand M) d ∧ d.code M ∈ observer) ↔
      ∃ e, Relation.ReflTransGen (WorkStep M) c e ∧ e.state = M.halt := by
  constructor
  · rintro ⟨n, d, h, hd⟩
    exact (halting_iff M c).mp ⟨n, d, h, (code_mem_observer_iff M d).mp hd⟩
  · intro h
    obtain ⟨n, d, hh, hd⟩ := (halting_iff M c).mpr h
    exact ⟨n, d, hh, (code_mem_observer_iff M d).mpr hd⟩

end BalancedTransport.Recorder.Checkpoint
end

noncomputable section
namespace BalancedTransport.FiniteMachine

def normalized (M : FiniteMachine) :
    Recorder.Machine (Option (Fin (M.states + 1))) (Fin (M.symbols + 1)) where
  halt := none
  blank := M.blank
  transition q a := match q with
    | none => ⟨none, a, .stay⟩
    | some q => match M.transition q a with
      | none => ⟨none, a, .stay⟩
      | some v => ⟨some v.state, v.write, v.move⟩

abbrev WorkConfiguration (M : FiniteMachine) :=
  Recorder.Checkpoint (Option (Fin (M.states + 1))) (Fin (M.symbols + 1))

def initialWork (M : FiniteMachine) (w : Input M) : WorkConfiguration M :=
  Recorder.Checkpoint.initial M.normalized (some M.initial) w

end BalancedTransport.FiniteMachine
end

noncomputable section
namespace BalancedTransport.TapeConfiguration

def advance {M : FiniteMachine} (c : TapeConfiguration M)
    (v : Recorder.Transition (Fin (M.states + 1)) (Fin (M.symbols + 1))) :
    TapeConfiguration M :=
  ⟨v.state, c.head + (match v.move with | .stay => 0 | .left => -1 | .right => 1),
    Function.update c.tape c.head v.write⟩

end BalancedTransport.TapeConfiguration
end

noncomputable section
namespace BalancedTransport.FiniteMachine
open Recorder
open Stream'

structure Represents (M : FiniteMachine) (w : M.WorkConfiguration)
    (c : TapeConfiguration M) : Prop where
  current : w.current = c.tape c.head
  left : ∀ n : ℕ, w.left n = c.tape (c.head - ((n : ℤ) + 1))
  right : ∀ n : ℕ, w.right[n]?.getD M.blank = c.tape (c.head + ((n : ℤ) + 1))

theorem initialWork_represents (M : FiniteMachine) (w : Input M) :
    Represents M (M.initialWork w) (initialConfiguration M w) := by
  constructor
  · cases w <;> simp [initialWork, Checkpoint.initial, normalized, initialConfiguration]
  · intro n
    change M.blank = (if 0 ≤ (0 : ℤ) - ((n : ℤ) + 1)
      then w[((0 : ℤ) - ((n : ℤ) + 1)).toNat]?.getD M.blank else M.blank)
    rw [ite_eq_right (by omega)]
  · intro n
    simp only [initialWork, Checkpoint.initial, normalized, initialConfiguration, zero_add,
      show (0 : ℤ) ≤ (n : ℤ) + 1 by omega, ↓reduceIte]
    have hn : ((n : ℤ) + 1).toNat = n + 1 := by omega
    rw [hn]
    cases w <;> simp

end BalancedTransport.FiniteMachine
end

noncomputable section
namespace BalancedTransport.FiniteMachine.Represents
open Recorder
open Stream'
variable {M : FiniteMachine} {w : M.WorkConfiguration} {c : TapeConfiguration M}

theorem advance (h : Represents M w c)
    (v : Transition (Fin (M.states + 1)) (Fin (M.symbols + 1)))
    (hv : M.normalized.transition w.state w.current = ⟨some v.state, v.write, v.move⟩) :
    Represents M (w.next M.normalized) (c.advance v) := by
  cases hm : v.move with
  | stay =>
      simp only [Checkpoint.next, hv, hm]
      constructor
      · simp [TapeConfiguration.advance, hm]
      · intro n
        change w.left n = Function.update c.tape c.head v.write
          (c.head + (match v.move with | .stay => 0 | .left => -1 | .right => 1) -
            ((n : ℤ) + 1))
        simp only [hm, add_zero]
        rw [Function.update_of_ne (by omega) _ _]
        exact h.left n
      · intro n
        simp only [TapeConfiguration.advance, hm, add_zero]
        rw [Function.update_of_ne (by omega) _ _]
        exact h.right n
  | left =>
      simp only [Checkpoint.next, hv, hm]
      constructor
      · simp only [TapeConfiguration.advance, hm, Stream'.head, Stream'.get]
        rw [Function.update_of_ne (by omega) _ _]
        simpa [sub_eq_add_neg] using h.left 0
      · intro n
        simp only [TapeConfiguration.advance, hm, Stream'.tail, Stream'.get]
        rw [Function.update_of_ne (by omega) _ _]
        convert h.left (n + 1) using 1
        congr 1
        omega
      · intro n
        simp only [TapeConfiguration.advance, hm]
        cases n with
        | zero => simp
        | succ n =>
            rw [Function.update_of_ne (by omega) _ _]
            simp only [List.getElem?_cons_succ]
            convert h.right n using 1
            congr 1
            omega
  | right =>
      cases hr : w.right with
      | nil =>
          simp only [Checkpoint.next, hv, hm, hr]
          constructor
          · simp only [TapeConfiguration.advance, hm]
            rw [Function.update_of_ne (by omega) _ _]
            change M.blank = c.tape (c.head + 1)
            simpa only [hr, List.getElem?_nil, Option.getD_none, Nat.cast_zero, zero_add]
              using h.right 0
          · intro n
            simp only [TapeConfiguration.advance, hm]
            cases n with
            | zero => simp [Stream'.cons]
            | succ n =>
                rw [Function.update_of_ne (by omega) _ _]
                simp only [Stream'.cons]
                convert h.left n using 1
                congr 1
                omega
          · intro n
            simp only [TapeConfiguration.advance, hm]
            rw [Function.update_of_ne (by omega) _ _]
            have he : c.head + 1 + ((n : ℤ) + 1) =
                c.head + (((n + 1 : ℕ) : ℤ) + 1) := by omega
            rw [he]
            simpa only [hr, List.getElem?_nil, Option.getD_none] using h.right (n + 1)
      | cons a r =>
          simp only [Checkpoint.next, hv, hm, hr]
          constructor
          · simp only [TapeConfiguration.advance, hm]
            rw [Function.update_of_ne (by omega) _ _]
            simpa only [hr, List.getElem?_cons_zero, Option.getD_some, Nat.cast_zero, zero_add]
              using h.right 0
          · intro n
            simp only [TapeConfiguration.advance, hm]
            cases n with
            | zero => simp [Stream'.cons]
            | succ n =>
                rw [Function.update_of_ne (by omega) _ _]
                simp only [Stream'.cons]
                convert h.left n using 1
                congr 1
                omega
          · intro n
            simp only [TapeConfiguration.advance, hm]
            rw [Function.update_of_ne (by omega) _ _]
            have he : c.head + 1 + ((n : ℤ) + 1) =
                c.head + (((n + 1 : ℕ) : ℤ) + 1) := by omega
            rw [he]
            simpa only [hr, List.getElem?_cons_succ] using h.right (n + 1)

theorem stop (h : Represents M w c)
    (hv : M.normalized.transition w.state w.current = ⟨none, w.current, .stay⟩) :
    Represents M (w.next M.normalized) c := by
  simp only [Checkpoint.next, hv]
  exact ⟨h.current, h.left, h.right⟩

end BalancedTransport.FiniteMachine.Represents
end

noncomputable section
namespace BalancedTransport.Recorder.Checkpoint

theorem next_state {Q Γ : Type*} (M : Machine Q Γ) (w : Checkpoint Q Γ) :
    (w.next M).state = (M.transition w.state w.current).state := by
  cases hm : (M.transition w.state w.current).move <;>
    simp only [next, hm]
  cases w.right <;> rfl

end BalancedTransport.Recorder.Checkpoint
end

noncomputable section
namespace BalancedTransport.FiniteMachine
open Recorder
variable {M : FiniteMachine}

theorem lift_step {c d : TapeConfiguration M} {w : M.WorkConfiguration}
    (h : machineStep M c = some d) (hs : w.state = some c.state)
    (ht : Represents M w c) :
    Checkpoint.WorkStep M.normalized w (w.next M.normalized) ∧
    (w.next M.normalized).state = some d.state ∧
    Represents M (w.next M.normalized) d := by
  cases hv : M.transition c.state (c.tape c.head) with
  | none => simp [machineStep, hv] at h
  | some v =>
      have hd : c.advance v = d := by
        cases hm : v.move <;>
          simpa only [machineStep, hv, Option.map_some, Option.some.injEq,
            TapeConfiguration.advance, hm] using h
      subst d
      have hv' : M.normalized.transition w.state w.current =
          ⟨some v.state, v.write, v.move⟩ := by
        simp [normalized, hs, ht.current, hv]
      refine ⟨⟨?_, rfl⟩, ?_, ht.advance v hv'⟩
      · simp [normalized, hs]
      · rw [Checkpoint.next_state, hv']
        rfl

theorem lift_execution {c d : TapeConfiguration M}
    (h : Relation.ReflTransGen (fun c d => machineStep M c = some d) c d)
    {w : M.WorkConfiguration} (hs : w.state = some c.state) (ht : Represents M w c) :
    ∃ w', Relation.ReflTransGen (Checkpoint.WorkStep M.normalized) w w' ∧
      w'.state = some d.state ∧ Represents M w' d := by
  induction h with
  | refl => exact ⟨w, .refl, hs, ht⟩
  | @tail c' d hc' hd ih =>
      obtain ⟨w', hw', hs', ht'⟩ := ih
      obtain ⟨hstep, hs'', ht''⟩ := lift_step hd hs' ht'
      exact ⟨w'.next M.normalized, hw'.tail hstep, hs'', ht''⟩

theorem lift_halt {c : TapeConfiguration M} {w : M.WorkConfiguration}
    (h : machineStep M c = none) (hs : w.state = some c.state)
    (ht : Represents M w c) :
    Checkpoint.WorkStep M.normalized w (w.next M.normalized) ∧
    (w.next M.normalized).state = none := by
  have hv : M.transition c.state (c.tape c.head) = none := by
    simpa only [machineStep, Option.map_eq_none_iff] using h
  have hv' : M.normalized.transition w.state w.current =
      ⟨none, w.current, .stay⟩ := by
    simp [normalized, hs, ht.current, hv]
  refine ⟨⟨?_, rfl⟩, ?_⟩
  · simp [normalized, hs]
  · rw [Checkpoint.next_state, hv']

def Corresponds (M : FiniteMachine) (w : M.WorkConfiguration)
    (c : TapeConfiguration M) : Prop :=
  Represents M w c ∧
    (w.state = some c.state ∨ (w.state = none ∧ machineStep M c = none))

theorem reflect_step {c : TapeConfiguration M} {w w' : M.WorkConfiguration}
    (hc : Corresponds M w c) (h : Checkpoint.WorkStep M.normalized w w') :
    ∃ d, Relation.ReflTransGen (fun c d => machineStep M c = some d) c d ∧
      Corresponds M w' d := by
  obtain ⟨ht, hs | ⟨hs, _⟩⟩ := hc
  · obtain ⟨hnh, rfl⟩ := h
    cases hv : M.transition c.state (c.tape c.head) with
    | none =>
        have hv' : M.normalized.transition w.state w.current =
            ⟨none, w.current, .stay⟩ := by
          simp [normalized, hs, ht.current, hv]
        refine ⟨c, .refl, ht.stop hv', Or.inr ⟨?_, ?_⟩⟩
        · rw [Checkpoint.next_state, hv']
        · simp [machineStep, hv]
    | some v =>
        have hd : machineStep M c = some (c.advance v) := by
          cases hm : v.move <;> simp [machineStep, hv, TapeConfiguration.advance, hm]
        obtain ⟨_, hs', ht'⟩ := lift_step hd hs ht
        exact ⟨c.advance v, .single hd, ht', Or.inl hs'⟩
  · exact False.elim (h.1 hs)

theorem reflect_execution {c : TapeConfiguration M} {w w' : M.WorkConfiguration}
    (hc : Corresponds M w c)
    (h : Relation.ReflTransGen (Checkpoint.WorkStep M.normalized) w w') :
    ∃ d, Relation.ReflTransGen (fun c d => machineStep M c = some d) c d ∧
      Corresponds M w' d := by
  induction h with
  | refl => exact ⟨c, .refl, hc⟩
  | @tail w' w'' hw' hstep ih =>
      obtain ⟨d, hd, hcd⟩ := ih
      obtain ⟨e, he, hce⟩ := reflect_step hcd hstep
      exact ⟨e, hd.trans he, hce⟩

theorem normalized_halting_iff (M : FiniteMachine) (input : Input M) :
    (∃ w', Relation.ReflTransGen (Checkpoint.WorkStep M.normalized)
      (M.initialWork input) w' ∧ w'.state = M.normalized.halt) ↔ Halts M input := by
  constructor
  · rintro ⟨w', hw', hhalt⟩
    have hc : Corresponds M (M.initialWork input) (initialConfiguration M input) :=
      ⟨initialWork_represents M input, Or.inl rfl⟩
    obtain ⟨d, hd, _, hs | ⟨_, hterm⟩⟩ := reflect_execution hc hw'
    · simp only [normalized] at hhalt
      rw [hhalt] at hs
      cases hs
    · exact ⟨d, hd, hterm⟩
  · rintro ⟨d, hd, hterm⟩
    obtain ⟨w', hw', hs', ht'⟩ := lift_execution hd (w := M.initialWork input)
      rfl (initialWork_represents M input)
    obtain ⟨hst, hh⟩ := lift_halt hterm hs' ht'
    exact ⟨w'.next M.normalized, hw'.tail hst, hh⟩

theorem discrete_compiled_halting_iff (M : FiniteMachine) (input : Input M) :
    (∃ n d, Exec M.normalized n ((M.initialWork input).expand M.normalized) d ∧
      d.code M.normalized ∈ observer) ↔ Halts M input :=
  (Checkpoint.coded_halting_iff M.normalized (M.initialWork input)).trans
    (normalized_halting_iff M input)

end BalancedTransport.FiniteMachine
end

end OAI

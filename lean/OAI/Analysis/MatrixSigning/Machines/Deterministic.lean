import Mathlib
import OAI.Analysis.MatrixSigning.Machines.FixedSequential

namespace OAI

namespace KS.W29.Deterministic
open KS.W29.FixedSequential
open KS.W01.FixedStack (Config Machine)

def CoinIndependent {k : Nat} (P : Program k) : Prop :=
  ∀ (c : KS.W01.FixedStack.Config k P.states) (a b : Bool), P.toMachine.step c a = P.toMachine.step c b

theorem coinIndependent_compile {k q : Nat} (initial : Fin q) (input output : Fin k)
    (dispatch : Fin q → (Fin k → Fin 3) → Bool → KS.W01.FixedStack.Instruction k q)
    (h : ∀ s heads a b, dispatch s heads a = dispatch s heads b) :
    CoinIndependent (ofMachine (KS.W01.FixedStack.compile initial input output dispatch)) := by
  intro c a b
  rcases c with ⟨state, «stacks»⟩
  cases state with
  | none => rfl
  | some s =>
      change (KS.W01.FixedStack.compile initial input output dispatch).step ⟨some s, «stacks»⟩ a =
        (KS.W01.FixedStack.compile initial input output dispatch).step ⟨some s, «stacks»⟩ b
      erw [KS.W01.FixedStack.step_compile, KS.W01.FixedStack.step_compile]
      dsimp only
      rw [h s _ a b]

theorem run_eq_of_length_eq {k : Nat} (P : Program k) (h : CoinIndependent P)
    (c : KS.W01.FixedStack.Config k P.states) (xs ys : List Bool) (hlen : xs.length = ys.length) :
    P.toMachine.run c xs = P.toMachine.run c ys := by
  induction xs generalizing c ys with
  | nil =>
      have hy : ys = [] := List.length_eq_zero_iff.mp hlen.symm
      subst ys
      rfl
  | cons a xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons b ys =>
          have ht : xs.length = ys.length := by simpa using hlen
          erw [Machine.run.eq_2, Machine.run.eq_2, h c a b]
          exact ih _ ys ht

theorem run_eq_false {k : Nat} (P : Program k) (h : CoinIndependent P)
    (c : KS.W01.FixedStack.Config k P.states) (bits : List Bool) :
    P.toMachine.run c bits = P.toMachine.run c (List.replicate bits.length false) :=
  run_eq_of_length_eq P h c bits _ (by simp)

theorem activeFor_iff_of_length_eq {k : Nat} (P : Program k) (h : CoinIndependent P)
    (c : KS.W01.FixedStack.Config k P.states) (xs ys : List Bool) (hlen : xs.length = ys.length) :
    ActiveFor P c xs ↔ ActiveFor P c ys := by
  induction xs generalizing c ys with
  | nil =>
      have hy : ys = [] := List.length_eq_zero_iff.mp hlen.symm
      subst ys
      rfl
  | cons a xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons b ys =>
          have ht : xs.length = ys.length := by simpa using hlen
          change (c.state ≠ none ∧ ActiveFor P (P.toMachine.step c a) xs) ↔
            (c.state ≠ none ∧ ActiveFor P (P.toMachine.step c b) ys)
          rw [h c a b]
          exact and_congr Iff.rfl (ih _ ys ht)

theorem haltsAfter_iff_of_length_eq {k : Nat} (P : Program k) (h : CoinIndependent P)
    (c : KS.W01.FixedStack.Config k P.states) (xs ys : List Bool) (hlen : xs.length = ys.length) :
    HaltsAfter P c xs ↔ HaltsAfter P c ys := by
  unfold HaltsAfter
  rw [activeFor_iff_of_length_eq P h c xs ys hlen, run_eq_of_length_eq P h c xs ys hlen]

theorem exists_uniform_first_halt {k : Nat} (P : Program k) (h : CoinIndependent P)
    (c : KS.W01.FixedStack.Config k P.states) (fuel : Nat) (hhalt : HaltsFromWithin P c fuel) :
    ∃ duration : Nat, duration ≤ fuel ∧
      ∀ bits : List Bool, bits.length = duration → HaltsAfter P c bits := by
  obtain ⟨first, rest, heq, hf⟩ := exists_halting_prefix P c (List.replicate fuel false)
    (hhalt _ (by simp))
  have hlen : first.length ≤ fuel := by
    have ht := congrArg List.length heq
    simp only [List.length_replicate, List.length_append] at ht
    omega
  refine ⟨first.length, hlen, ?_⟩
  intro bits hbits
  exact (haltsAfter_iff_of_length_eq P h c first bits hbits.symm).1 hf

theorem exists_uniform_first_halt_output {k : Nat} (P : Program k) (h : CoinIndependent P)
    (c : KS.W01.FixedStack.Config k P.states) (fuel : Nat) (after : Fin k → List Bool)
    (houtput : ∀ bits : List Bool, bits.length = fuel →
      P.toMachine.run c bits = ⟨none, after⟩) :
    ∃ duration : Nat, duration ≤ fuel ∧
      ∀ bits : List Bool, bits.length = duration →
        HaltsAfter P c bits ∧ P.toMachine.run c bits = ⟨none, after⟩ := by
  have hfull := houtput (List.replicate fuel false) (by simp)
  obtain ⟨first, rest, heq, hf⟩ := exists_halting_prefix P c (List.replicate fuel false)
    (congrArg KS.W01.FixedStack.Config.state hfull)
  have hlen : first.length ≤ fuel := by
    have ht := congrArg List.length heq
    simp only [List.length_replicate, List.length_append] at ht
    omega
  have hfirst : P.toMachine.run c first = ⟨none, after⟩ := by
    erw [heq, Machine.run_append, Machine.run_halted _ _ hf.2] at hfull
    exact hfull
  refine ⟨first.length, hlen, ?_⟩
  intro bits hbits
  constructor
  · exact (haltsAfter_iff_of_length_eq P h c first bits hbits.symm).1 hf
  · rw [run_eq_of_length_eq P h c bits first hbits]
    exact hfirst

theorem activeFor_not_halted_take {k : Nat} (P : Program k) (c : KS.W01.FixedStack.Config k P.states)
    (bits : List Bool) (h : ActiveFor P c bits) {j : Nat} (hj : j < bits.length) :
    (P.toMachine.run c (bits.take j)).state ≠ none := by
  induction bits generalizing c j with
  | nil => simp at hj
  | cons b bs ih =>
      cases j with
      | zero => exact h.1
      | succ j =>
          have hjb : j < bs.length := by simpa using hj
          simpa [Machine.run] using ih (P.toMachine.step c b) h.2 hjb

theorem first_halt_length_unique {k : Nat} (P : Program k) (h : CoinIndependent P)
    (c : KS.W01.FixedStack.Config k P.states) (xs ys : List Bool)
    (hx : HaltsAfter P c xs) (hy : HaltsAfter P c ys) : xs.length = ys.length := by
  have no_lt : ∀ (leftBits rightBits : List Bool), HaltsAfter P c leftBits → HaltsAfter P c rightBits →
      ¬ leftBits.length < rightBits.length := by
    intro leftBits rightBits ha hb hab
    have hn := activeFor_not_halted_take P c rightBits hb.1 hab
    have he := run_eq_of_length_eq P h c (rightBits.take leftBits.length) leftBits
      (by simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hab)])
    exact hn (by rw [he]; exact ha.2)
  have hxy := no_lt xs ys hx hy
  have hyx := no_lt ys xs hy hx
  omega

theorem coinIndependent_compose {k : Nat} (P Q : Program k)
    (hP : CoinIndependent P) (hQ : CoinIndependent Q) : CoinIndependent (compose P Q) := by
  intro c a b
  rcases c with ⟨state, «stacks»⟩
  cases state with
  | none => rfl
  | some s =>
      by_cases hs : s.val < P.states
      · let t : Fin P.states := ⟨s.val, hs⟩
        have he : s = leftState P Q t := Fin.ext rfl
        rw [he]
        erw [step_left, step_left]
        exact congrArg (liftLeft P Q) (hP ⟨some t, «stacks»⟩ a b)
      · have hbound : s.val < P.states + Q.states := s.isLt
        let t : Fin Q.states := ⟨s.val - P.states, by omega⟩
        have he : s = rightState P Q t := by apply Fin.ext; dsimp [rightState, t]; omega
        rw [he]
        erw [step_right, step_right]
        exact congrArg (liftRight P Q) (hQ ⟨some t, «stacks»⟩ a b)

end KS.W29.Deterministic

end OAI

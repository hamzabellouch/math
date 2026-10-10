import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.FiniteRecorder

namespace OAI

/-! A finite executable alphabet for the reversible recorder. The blank is
assigned digit zero, so finite integer stacks represent infinite blank tails.
All seven guarded instruction rows are retained, including unreachable rows. -/

namespace ForcedComputation.ExpandingDetector
open Recorder

def controlCode (M : Alternating.Machine)
    (q : Control (State M) (Alphabet M)) : ℕ := (allControls M).idxOf q

theorem controlCode_lt (M : Alternating.Machine)
    (q : Control (State M) (Alphabet M)) : controlCode M q < (allControls M).length :=
  List.idxOf_lt_length_of_mem (mem_allControls M q)

theorem controlCode_injective (M : Alternating.Machine) :
    Function.Injective (controlCode M) := by
  intro q r h
  exact (List.idxOf_inj (mem_allControls M q)).mp h

def symbolList (M : Alternating.Machine) (blank : Recorder.Symbol (State M) (Alphabet M)) :
    List (Recorder.Symbol (State M) (Alphabet M)) :=
  blank :: (allSymbols M).filter (fun s => s != blank)

theorem mem_symbolList (M : Alternating.Machine)
    (blank s : Recorder.Symbol (State M) (Alphabet M)) : s ∈ symbolList M blank := by
  by_cases h : s = blank
  · simp [symbolList, h]
  · simp [symbolList, mem_allSymbols M s, h]

def symbolCode (M : Alternating.Machine)
    (blank s : Recorder.Symbol (State M) (Alphabet M)) : ℕ := (symbolList M blank).idxOf s

theorem symbolCode_lt (M : Alternating.Machine)
    (blank s : Recorder.Symbol (State M) (Alphabet M)) :
    symbolCode M blank s < (symbolList M blank).length :=
  List.idxOf_lt_length_of_mem (mem_symbolList M blank s)

theorem symbolCode_blank (M : Alternating.Machine)
    (blank : Recorder.Symbol (State M) (Alphabet M)) : symbolCode M blank blank = 0 := by
  simp [symbolCode, symbolList]

theorem symbolCode_injective (M : Alternating.Machine)
    (blank : Recorder.Symbol (State M) (Alphabet M)) : Function.Injective (symbolCode M blank) := by
  intro a b h
  exact (List.idxOf_inj (mem_symbolList M blank a)).mp h

theorem symbolCode_eq_zero (M : Alternating.Machine)
    (blank s : Recorder.Symbol (State M) (Alphabet M)) : symbolCode M blank s = 0 ↔ s = blank := by
  rw [← symbolCode_blank M blank]
  exact ⟨fun h => symbolCode_injective M blank h, congrArg (symbolCode M blank)⟩

def alphabetBase (M : Alternating.Machine)
    (blank : Recorder.Symbol (State M) (Alphabet M)) : ℕ := max 2 (symbolList M blank).length

theorem alphabetBase_two_le (M : Alternating.Machine)
    (blank : Recorder.Symbol (State M) (Alphabet M)) : 2 ≤ alphabetBase M blank := le_max_left _ _

theorem symbolCode_lt_base (M : Alternating.Machine)
    (blank s : Recorder.Symbol (State M) (Alphabet M)) : symbolCode M blank s < alphabetBase M blank :=
  (symbolCode_lt M blank s).trans_le (le_max_right _ _)

def encodedLocal (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (q a : ℕ) : Option (ℕ × ℕ × ℤ) := do
  let state ← (allControls M)[q]?
  let symbol ← (symbolList M blank)[a]?
  let out ← evalLocal (finiteMachine M hM) state symbol
  pure (controlCode M out.1, symbolCode M blank out.2.1, out.2.2)

theorem encodedLocal_complete (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M))
    {q q' : Control (State M) (Alphabet M)}
    {s s' : Recorder.Symbol (State M) (Alphabet M)} {d : ℤ}
    (h : LocalStep (finiteMachine M hM) q s q' s' d) :
    encodedLocal M hM blank (controlCode M q) (symbolCode M blank s) =
      some (controlCode M q', symbolCode M blank s', d) := by
  simp only [encodedLocal, controlCode, symbolCode,
    List.getElem?_idxOf (mem_allControls M q),
    List.getElem?_idxOf (mem_symbolList M blank s), Option.bind_eq_bind,
    Option.bind_some, Option.pure_def, h.eval]

theorem encodedLocal_predecessor_unique (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M))
    {q₁ q₂ q₁' q₂' : Control (State M) (Alphabet M)}
    {s₁ s₂ s₁' s₂' : Recorder.Symbol (State M) (Alphabet M)} {d₁ d₂ : ℤ}
    (h₁ : LocalStep (finiteMachine M hM) q₁ s₁ q₁' s₁' d₁)
    (h₂ : LocalStep (finiteMachine M hM) q₂ s₂ q₂' s₂' d₂)
    (hq : controlCode M q₁' = controlCode M q₂')
    (hs : symbolCode M blank s₁' = symbolCode M blank s₂') :
    controlCode M q₁ = controlCode M q₂ ∧
      symbolCode M blank s₁ = symbolCode M blank s₂ ∧ d₁ = d₂ := by
  have hq' := controlCode_injective M hq
  have hs' := symbolCode_injective M blank hs
  subst q₂'
  subst s₂'
  obtain ⟨rfl, rfl, hd⟩ := h₁.predecessor_unique h₂
  exact ⟨rfl, rfl, hd⟩

end ForcedComputation.ExpandingDetector

end OAI

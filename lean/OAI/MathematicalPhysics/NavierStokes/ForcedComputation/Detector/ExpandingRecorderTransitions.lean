import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Detector.ExpandingRecorderAlphabet
import OAI.MathematicalPhysics.NavierStokes.ForcedComputation.Programs.FiniteStackArithmetic

namespace OAI

/-! The full guarded recorder is injective on integer-stack configurations.
Incoming direction is recovered from the target control; the new stacks
then reveal the written symbol, and the seven-row inverse reveals the read
symbol. No invariant of the selected computation is assumed. -/

namespace ForcedComputation.ExpandingDetector
open Recorder

def moveCode (d : ℤ) : Fin 3 := if d = -1 then 0 else if d = 0 then 1 else 2

def IntegerStep (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M))
    (q : Control (State M) (Alphabet M)) (L R : ℕ)
    (q' : Control (State M) (Alphabet M)) (L' R' : ℕ) : Prop :=
  ∃ (read write : Recorder.Symbol (State M) (Alphabet M)) (d : ℤ),
    LocalStep (finiteMachine M hM) q read q' write d ∧
    symbolCode M blank read = R % alphabetBase M blank ∧
    Lattice.nextLeft (alphabetBase M blank) L (symbolCode M blank write) (moveCode d) = L' ∧
    Lattice.nextRight (alphabetBase M blank) L R (symbolCode M blank write) (moveCode d) = R'

def integerNext (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M)) (q L R : ℕ) : Option (ℕ × ℕ × ℕ) := do
  let out ← encodedLocal M hM blank q (R % alphabetBase M blank)
  pure (out.1, Lattice.nextLeft (alphabetBase M blank) L out.2.1 (moveCode out.2.2),
    Lattice.nextRight (alphabetBase M blank) L R out.2.1 (moveCode out.2.2))

theorem IntegerStep.compiled (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M))
    {q q' : Control (State M) (Alphabet M)} {L R L' R' : ℕ}
    (hs : IntegerStep M hM blank q L R q' L' R') :
    integerNext M hM blank (controlCode M q) L R = some (controlCode M q', L', R') := by
  obtain ⟨a, b, d, hs, hr, hL, hR⟩ := hs
  simp only [integerNext, ← hr, encodedLocal_complete M hM blank hs,
    Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  rw [hL, hR]

theorem IntegerStep.successor_unique (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M))
    {q q₁ q₂ : Control (State M) (Alphabet M)} {L R L₁ L₂ R₁ R₂ : ℕ}
    (h₁ : IntegerStep M hM blank q L R q₁ L₁ R₁)
    (h₂ : IntegerStep M hM blank q L R q₂ L₂ R₂) :
    q₁ = q₂ ∧ L₁ = L₂ ∧ R₁ = R₂ := by
  have he := Option.some.inj ((IntegerStep.compiled M hM blank h₁).symm.trans
    (IntegerStep.compiled M hM blank h₂))
  have hq := controlCode_injective M (congrArg Prod.fst he)
  exact ⟨hq, congrArg (fun p : ℕ × ℕ × ℕ => p.2.1) he,
    congrArg (fun p : ℕ × ℕ × ℕ => p.2.2) he⟩

theorem IntegerStep.predecessor_unique (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M))
    {q₁ q₂ q' : Control (State M) (Alphabet M)} {L₁ L₂ R₁ R₂ L' R' : ℕ}
    (h₁ : IntegerStep M hM blank q₁ L₁ R₁ q' L' R')
    (h₂ : IntegerStep M hM blank q₂ L₂ R₂ q' L' R') :
    q₁ = q₂ ∧ L₁ = L₂ ∧ R₁ = R₂ := by
  obtain ⟨a₁, b₁, d₁, hs₁, hr₁, hL₁, hR₁⟩ := h₁
  obtain ⟨a₂, b₂, d₂, hs₂, hr₂, hL₂, hR₂⟩ := h₂
  have hd : d₁ = d₂ := hs₁.incoming_eq.symm.trans hs₂.incoming_eq
  subst d₂
  have hb : 0 < alphabetBase M blank := lt_of_lt_of_le (by decide) (alphabetBase_two_le M blank)
  obtain ⟨hL, hR, hw⟩ := Lattice.nextStacks_recover hb
    (symbolCode_lt_base M blank b₁) (symbolCode_lt_base M blank b₂) (moveCode d₁)
    (hL₁.trans hL₂.symm) (hR₁.trans hR₂.symm)
  have hbb : b₁ = b₂ := symbolCode_injective M blank hw
  subst b₂
  obtain ⟨hq, ha, _⟩ := hs₁.predecessor_unique hs₂
  have hread : R₁ % alphabetBase M blank = R₂ % alphabetBase M blank := by
    rw [← hr₁, ← hr₂, ha]
  exact ⟨hq, hL, Lattice.nat_eq_of_mod_div_eq hread hR⟩

theorem IntegerStep.target_bounds (M : Alternating.Machine) (hM : M.WellFormed)
    (blank : Recorder.Symbol (State M) (Alphabet M))
    {q q' : Control (State M) (Alphabet M)} {L R L' R' d : ℕ}
    (hs : IntegerStep M hM blank q L R q' L' R') (hd : 0 < d)
    (hL : L < (alphabetBase M blank) ^ d) (hR : R < (alphabetBase M blank) ^ d) :
    L' < (alphabetBase M blank) ^ (d + 1) ∧
      R' < (alphabetBase M blank) ^ (d + 1) := by
  obtain ⟨a, b, m, _, _, rfl, rfl⟩ := hs
  exact Lattice.next_stacks_lt (alphabetBase_two_le M blank) hd hL hR
    (symbolCode_lt_base M blank b) (moveCode m)

end ForcedComputation.ExpandingDetector

end OAI

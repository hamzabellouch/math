import Mathlib
import OAI.Analysis.MatrixSigning.Arithmetic.DivisionLoopModel
import OAI.Analysis.MatrixSigning.Arithmetic.DivisionMachine

namespace OAI

section

namespace KS.W19.DivisionMachine
open KS.W01.FixedStack KS.W29.FixedSequential

def bodyFuel (d r : List Bool) : Nat :=
  (2 * r.length + 2) + ((2 * d.length + 2) + ((max r.length d.length + 1) +
    (1 + if subtractionBorrow r d false then max r.length d.length + 1
      else (r.length + 1) + (max r.length d.length + 1))))

def trialResult (d q r : List Bool) : List Bool × List Bool :=
  if subtractionBorrow r d false then (false :: q,r)
  else (true :: q, trimBits (subtractBits r d false))

theorem trialResult_advance (d q r : List Bool) (b : Bool) :
    trialResult d q (b :: r) = DivisionLoop.advance d b q r := rfl

theorem split_exact (bits : List Bool) (a b : Nat) (hb : bits.length = a + b) :
    ∃ first second, bits = first ++ second ∧ first.length = a ∧ second.length = b := by
  refine ⟨bits.take a, bits.drop a, (List.take_append_drop a bits).symm, ?_, ?_⟩
  · simp only [List.length_take, hb]
    omega
  · simp only [List.length_drop, hb]
    omega

theorem body_run_exact (d pending q r bits : List Bool) (hb : bits.length = bodyFuel d r) :
    body.toMachine.run ⟨some body.initial, «stacks» d pending q r [] [] [] []⟩ bits =
      ⟨none, «stacks» d pending (trialResult d q r).1 (trialResult d q r).2 [] [] [] []⟩ := by
  unfold bodyFuel at hb
  obtain ⟨first, rest, rfl, h₁, hrest⟩ := split_exact bits (2 * r.length + 2) _ hb
  obtain ⟨second, rest, rfl, h₂, hrest⟩ := split_exact rest (2 * d.length + 2) _ hrest
  obtain ⟨third, last, rfl, h₃, hlast⟩ := split_exact rest (max r.length d.length + 1) _ hrest
  cases last with
  | nil =>
    simp only [List.length_nil] at hlast
    omega
  | cons coin tail =>
    cases hc : subtractionBorrow r d false
    · have ht : tail.length = (r.length + 1) + (max r.length d.length + 1) := by
        simp only [hc, Bool.false_eq_true, ↓reduceIte, List.length_cons] at hlast
        omega
      obtain ⟨clear, trim, rfl, hclear, htrim⟩ := split_exact tail (r.length + 1) _ ht
      simpa only [trialResult, hc, Bool.false_eq_true, ↓reduceIte, List.append_assoc] using
        body_run_candidate d pending q r first second third clear trim coin hc h₁ h₂ h₃ hclear htrim
    · have ht : tail.length = max r.length d.length + 1 := by
        simp only [hc, ↓reduceIte, List.length_cons] at hlast
        omega
      simpa only [trialResult, hc, ↓reduceIte, List.append_assoc] using
        body_run_borrowed d pending q r first second third tail coin hc h₁ h₂ h₃ ht

theorem bodyFuel_linear (d r : List Bool) : bodyFuel d r ≤ 8 * (r.length + d.length + 1) := by
  unfold bodyFuel
  split <;> omega

theorem body_run_of_length_ge (d pending q r bits : List Bool) (hb : bodyFuel d r ≤ bits.length) :
    body.toMachine.run ⟨some body.initial, «stacks» d pending q r [] [] [] []⟩ bits =
      ⟨none, «stacks» d pending (trialResult d q r).1 (trialResult d q r).2 [] [] [] []⟩ := by
  have hh := body_run_exact d pending q r (bits.take (bodyFuel d r))
    (by simp [List.length_take, Nat.min_eq_left hb])
  conv_lhs => rw [← List.take_append_drop (bodyFuel d r) bits]
  rw [Machine.run_append, hh]
  exact body.toMachine.run_halted _ rfl _

theorem body_halts_linear (d pending q r : List Bool) :
    HaltsFromWithin body ⟨some body.initial, «stacks» d pending q r [] [] [] []⟩
      (8 * (r.length + d.length + 1)) := by
  intro bits hb
  exact congrArg Config.state
    (body_run_of_length_ge d pending q r bits (by rw [hb]; exact bodyFuel_linear d r))

end KS.W19.DivisionMachine

end

end OAI

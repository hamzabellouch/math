import OAI.Computability.PerfectCompleteness.Machines.TargetFinalizeMachine

namespace OAI

section

namespace PerfectCompleteness.TargetFinalizeBound

open Turing UniqueGamesTheorem.Foundations.Complexity
open TargetFinalizeMachine

variable {K Λ A : Type} [DecidableEq K] {stackCount : Nat}

omit [DecidableEq K] in
private theorem lengthSum_le (chosen : List K) (base : K → List Bool) (B : Nat)
    (bounded : ∀ k, (base k).length ≤ B) :
    MachineDrainMany.lengthSum chosen base ≤ chosen.length * B := by
  induction chosen with
  | nil => simp [MachineDrainMany.lengthSum]
  | cons k chosen ih =>
      simp only [MachineDrainMany.lengthSum, List.map_cons, List.sum_cons,
        List.length_cons, Nat.add_mul, Nat.one_mul] at *
      have hk := bounded k
      omega

theorem header_length (q count : Nat) (body : List Bool) :
    (encodeWords [count, count, q, count] ++ body).length =
      3 * (count + 1) + (q + 1) + body.length := by
  simp only [encodeWords, List.length_append, encodeWord_length, List.length_nil]
  omega

theorem headerTapes_length_le (q count : Nat) (tape : Fin 4 → K)
    (base : K → List Bool) (body : List Bool) (B : Nat)
    (bounded : ∀ k, (base k).length ≤ B) (bodyBound : body.length ≤ B)
    (countBound : count ≤ B) :
    ∀ k, (headerTapes q count tape base body k).length ≤ 4 * B + q + 4 := by
  intro k
  by_cases output : k = tape 3
  · subst k
    simp only [headerTapes, Function.update_self, header_length]
    omega
  · by_cases accumulator : k = tape 0
    · subst k
      simp [headerTapes, bodyTapes, output]
    · have hk := bounded k
      simp only [headerTapes, bodyTapes, Function.update_of_ne output,
        Function.update_of_ne accumulator]
      omega

theorem budget_le (q count : Nat) (enumeration : Fin stackCount ≃ K) (tape : Fin 4 → K)
    (base : K → List Bool) (body : List Bool) (B : Nat)
    (bounded : ∀ k, (base k).length ≤ B) (bodyBound : body.length ≤ B)
    (countBound : count ≤ B) :
    budget q count enumeration tape base body ≤
      (15 + stackCount * (q + 9)) * (B + 1) := by
  let chosen := MachineDrainMany.workTapes enumeration (tape 3)
  have hlength : chosen.length ≤ stackCount := MachineDrainMany.workTapes_length_le _ _
  have hsum := lengthSum_le chosen (headerTapes q count tape base body) (4 * B + q + 4)
    (headerTapes_length_le q count tape base body B bounded bodyBound countBound)
  have hsum' := hsum.trans (Nat.mul_le_mul_right (4 * B + q + 4) hlength)
  have hsmall : 4 * B + q + 5 ≤ (q + 9) * (B + 1) := by
    rw [Nat.mul_add, Nat.mul_one, Nat.add_mul]
    omega
  have hscaled := Nat.mul_le_mul_left stackCount hsmall
  have hfirst : body.length + 1 + (6 * (count + 2) + 1) + 1 ≤ 15 * (B + 1) := by
    omega
  calc
    budget q count enumeration tape base body ≤
        15 * (B + 1) + stackCount * (4 * B + q + 5) := by
          unfold budget
          dsimp only [chosen] at hsum' hlength
          rw [Nat.mul_add stackCount (4 * B + q + 4) 1, Nat.mul_one]
          omega
    _ ≤ 15 * (B + 1) + stackCount * ((q + 9) * (B + 1)) := Nat.add_le_add_left hscaled _
    _ = _ := by simp only [Nat.add_mul, Nat.mul_assoc]

def finalizeInTime (q : Nat) (enumeration : Fin stackCount ≃ K) (tape : Fin 4 → K)
    (distinct : Function.Injective tape) (initial : A)
    (labels : Labels enumeration (tape 3) → Λ)
    (program : Λ → TM2.Stmt (Alphabet (K := K)) Λ (State A))
    (atLabels : ∀ l, program (labels l) = instruction q enumeration tape initial labels l)
    (base : K → List Bool) (ambient : A) (register : Option Bool)
    (count : Nat) (body : List Bool)
    (reversed : base (tape 0) = body.reverse)
    (countWord : base (tape 1) = encodeWord count)
    (scratchEmpty : base (tape 2) = []) (outputEmpty : base (tape 3) = [])
    (B : Nat) (bounded : ∀ k, (base k).length ≤ B) :
    StateTransition.EvalsToInTime (TM2.step program)
      ⟨some (labels .reverse), (ambient, register), base⟩
      (some ⟨none, (initial, none), MachineDrainMany.haltTapes (tape 3)
        (encodeWords [count, count, q, count] ++ body)⟩)
      ((15 + stackCount * (q + 9)) * (B + 1)) := by
  let run := TargetFinalizeMachine.finalizeInTime q enumeration tape distinct initial labels
    program atLabels base ambient register count body reversed countWord scratchEmpty outputEmpty
  have bodyBound : body.length ≤ B := by simpa only [reversed, List.length_reverse] using bounded (tape 0)
  have countBound : count ≤ B := by
    have h := bounded (tape 1)
    rw [countWord, encodeWord_length] at h
    omega
  exact {
    steps := run.steps
    evals_in_steps := run.evals_in_steps
    steps_le_m := run.steps_le_m.trans (budget_le q count enumeration tape base body B
      bounded bodyBound countBound)
  }

end PerfectCompleteness.TargetFinalizeBound

end

end OAI

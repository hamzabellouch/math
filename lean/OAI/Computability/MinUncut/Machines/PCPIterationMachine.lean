import Mathlib
import OAI.Computability.MinUncut.Machines.MachineUnaryCounter

namespace OAI

section
namespace MinUncutGames.Foundations.Complexity.PCPIterationMachine

open Turing
open MachineCountedLoop

def rounds (n : Nat) : Nat := n.log2 + 1

theorem rounds_le (n : Nat) : rounds n ≤ n + 1 :=
  Nat.add_le_add_right (Nat.log2_le_self n) 1

theorem two_pow_rounds_le (n : Nat) : 2 ^ rounds n ≤ 2 * (n + 1) := by
  by_cases hn : n = 0
  · subst n; decide
  · have h := Nat.log2_self_le hn
    simp only [rounds, pow_succ]
    omega

theorem growth_pow_rounds_le (growth n : Nat) :
    growth ^ rounds n ≤ (2 * (n + 1)) ^ growth := by
  calc
    growth ^ rounds n ≤ (2 ^ growth) ^ rounds n :=
      Nat.pow_le_pow_left (Nat.le_of_lt (Nat.lt_two_pow_self (n := growth))) _
    _ = (2 ^ rounds n) ^ growth := by simp only [← pow_mul, Nat.mul_comm]
    _ ≤ (2 * (n + 1)) ^ growth := Nat.pow_le_pow_left (two_pow_rounds_le n) growth

def sizeEnvelope (growth n : Nat) : Nat := (n + 1) * (2 * (n + 1)) ^ growth

theorem semanticSize_geometric (sizes : Nat → Nat) (growth n : Nat)
    (initialBound : sizes 0 ≤ n + 1)
    (growthBound : ∀ i, i < rounds n → sizes (i + 1) ≤ growth * sizes i)
    (i : Nat) (hi : i ≤ rounds n) : sizes i ≤ (n + 1) * growth ^ i := by
  induction i with
  | zero => simpa only [pow_zero, Nat.mul_one] using initialBound
  | succ i ih =>
    have ilt : i < rounds n := by omega
    calc
      sizes (i + 1) ≤ growth * sizes i := growthBound i ilt
      _ ≤ growth * ((n + 1) * growth ^ i) :=
        Nat.mul_le_mul_left growth (ih (by omega))
      _ = (n + 1) * growth ^ (i + 1) := by rw [pow_succ]; ac_rfl

theorem semanticSize_bound (sizes : Nat → Nat) (growth n : Nat)
    (growthPositive : 0 < growth)
    (initialBound : sizes 0 ≤ n + 1)
    (growthBound : ∀ i, i < rounds n → sizes (i + 1) ≤ growth * sizes i)
    (i : Nat) (hi : i ≤ rounds n) : sizes i ≤ sizeEnvelope growth n := by
  calc
    sizes i ≤ (n + 1) * growth ^ i :=
      semanticSize_geometric sizes growth n initialBound growthBound i hi
    _ ≤ (n + 1) * growth ^ rounds n :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right growthPositive hi)
    _ ≤ sizeEnvelope growth n :=
      Nat.mul_le_mul_left _ (growth_pow_rounds_le growth n)

noncomputable def sizePolynomial (growth : Nat) : Polynomial Nat :=
  (Polynomial.X + 1) * (2 * (Polynomial.X + 1)) ^ growth

@[simp] theorem sizePolynomial_eval (growth n : Nat) :
    (sizePolynomial growth).eval n = sizeEnvelope growth n := by
  simp [sizePolynomial, sizeEnvelope]

noncomputable def timePolynomial (growth : Nat)
    (encodingSize bodyTime : Polynomial Nat) : Polynomial Nat :=
  (Polynomial.X + 1) *
    ((bodyTime.comp encodingSize).comp (sizePolynomial growth) + 1) + 2

@[simp] theorem timePolynomial_eval (growth n : Nat)
    (encodingSize bodyTime : Polynomial Nat) :
    (timePolynomial growth encodingSize bodyTime).eval n =
      (n + 1) * (bodyTime.eval (encodingSize.eval (sizeEnvelope growth n)) + 1) + 2 := by
  simp [timePolynomial]

variable {K Λ σ : Type} [DecidableEq K]

abbrev Alphabet (_ : K) := Bool
abbrev State (σ : Type) := σ × Option Bool
abbrev Labels (Λ : Type) := Bool ⊕ Λ

def program (counter : K) (entry : Λ)
    (body : Λ → TM2.Stmt (Alphabet (K := K)) (Labels Λ) (State σ)) :
    Labels Λ → TM2.Stmt (Alphabet (K := K)) (Labels Λ) (State σ)
  | .inl false => MachineUnaryCounter.guard counter (.inr entry) (.inl true)
  | .inl true => .pop counter (fun state _ => (state.1, none)) .halt
  | .inr label => body label

omit [DecidableEq K] in
@[simp] theorem program_guard (counter : K) (entry : Λ)
    (body : Λ → TM2.Stmt (Alphabet (K := K)) (Labels Λ) (State σ)) :
    program counter entry body (.inl false) =
      MachineUnaryCounter.guard counter (.inr entry) (.inl true) := rfl

def machine [Fintype K] [Fintype Λ] [Fintype σ]
    (counter output : K) (entry : Λ) (initial : σ)
    (body : Λ → TM2.Stmt (Alphabet (K := K)) (Labels Λ) (State σ)) : FinTM2 where
  K := K
  k₀ := counter
  k₁ := output
  Γ := Alphabet
  Λ := Labels Λ
  main := .inl false
  σ := State σ
  initialState := (initial, none)
  m := program counter entry body

def haltedConfiguration (counter : K) (suffix : List Bool)
    (ambient : Nat → σ) (base : Nat → K → List Bool) :
    TM2.Cfg (Alphabet (K := K)) (Labels Λ) (State σ) :=
  ⟨none, (ambient 0, none), Function.update (base 0) counter suffix⟩

theorem haltStep (counter : K) (entry : Λ)
    (body : Λ → TM2.Stmt (Alphabet (K := K)) (Labels Λ) (State σ))
    (suffix : List Bool) (ambient : Nat → σ) (base : Nat → K → List Bool) :
    TM2.step (program counter entry body)
      (exitConfiguration counter (.inl true) suffix ambient base) =
      some (haltedConfiguration counter suffix ambient base) := by
  change some (TM2.stepAux (.pop counter (fun state _ => (state.1, none)) .halt)
    (ambient 0, none) (MachineUnaryCounter.counterTapes counter (base 0) 0 suffix)) = _
  simp [TM2.stepAux, MachineUnaryCounter.counterTapes, encodeWord, haltedConfiguration]

theorem iterationTrace (counter : K) (entry : Λ)
    (body : Λ → TM2.Stmt (Alphabet (K := K)) (Labels Λ) (State σ))
    (suffix : List Bool) (ambient : Nat → σ) (register : Nat → Option Bool)
    (base : Nat → K → List Bool) (cost : Nat → Nat) (n : Nat)
    (bodyTraces : BodyTraces counter (.inl false) (.inr entry)
      (program counter entry body) suffix ambient register base cost (rounds n)) :
    (MachineComposition.advance (TM2.step (program counter entry body)))^[
        totalSteps cost (rounds n) + 1]
      (some (guardConfiguration counter (.inl false) suffix ambient register base (rounds n))) =
      some (haltedConfiguration counter suffix ambient base) := by
  rw [Function.iterate_succ_apply']
  rw [loopTrace counter (.inl false) (.inr entry) (.inl true)
    (program counter entry body) (program_guard counter entry body) suffix
    ambient register base cost (rounds n) bodyTraces]
  exact haltStep counter entry body suffix ambient base

theorem bodyCosts_bound (growth n : Nat) (growthPositive : 0 < growth)
    (sizes encodedSizes cost : Nat → Nat) (encodingSize bodyTime : Polynomial Nat)
    (initialBound : sizes 0 ≤ n + 1)
    (growthBound : ∀ i, i < rounds n → sizes (i + 1) ≤ growth * sizes i)
    (encodingBound : ∀ r, r < rounds n →
      encodedSizes r ≤ encodingSize.eval (sizes (rounds n - (r + 1))))
    (bodyCost : ∀ r, r < rounds n → cost r ≤ bodyTime.eval (encodedSizes r)) :
    ∀ r, r < rounds n →
      cost r ≤ bodyTime.eval (encodingSize.eval (sizeEnvelope growth n)) := by
  intro r hr
  have hs := semanticSize_bound sizes growth n growthPositive initialBound growthBound
    (rounds n - (r + 1)) (Nat.sub_le _ _)
  exact (bodyCost r hr).trans
    (MachineComposition.natPolynomial_eval_mono bodyTime
      ((encodingBound r hr).trans
        (MachineComposition.natPolynomial_eval_mono encodingSize hs)))

def iterationInTime (counter : K) (entry : Λ)
    (body : Λ → TM2.Stmt (Alphabet (K := K)) (Labels Λ) (State σ))
    (suffix : List Bool) (ambient : Nat → σ) (register : Nat → Option Bool)
    (base : Nat → K → List Bool) (cost : Nat → Nat) (growth n : Nat)
    (growthPositive : 0 < growth)
    (bodyTraces : BodyTraces counter (.inl false) (.inr entry)
      (program counter entry body) suffix ambient register base cost (rounds n))
    (sizes encodedSizes : Nat → Nat) (encodingSize bodyTime : Polynomial Nat)
    (initialBound : sizes 0 ≤ n + 1)
    (growthBound : ∀ i, i < rounds n → sizes (i + 1) ≤ growth * sizes i)
    (encodingBound : ∀ r, r < rounds n →
      encodedSizes r ≤ encodingSize.eval (sizes (rounds n - (r + 1))))
    (bodyCost : ∀ r, r < rounds n → cost r ≤ bodyTime.eval (encodedSizes r)) :
    StateTransition.EvalsToInTime (TM2.step (program counter entry body))
      (guardConfiguration counter (.inl false) suffix ambient register base (rounds n))
      (some (haltedConfiguration counter suffix ambient base))
      ((timePolynomial growth encodingSize bodyTime).eval n) where
  steps := totalSteps cost (rounds n) + 1
  evals_in_steps := iterationTrace counter entry body suffix ambient register base cost n bodyTraces
  steps_le_m := by
    rw [timePolynomial_eval]
    have h := totalSteps_le cost (rounds n)
      (bodyTime.eval (encodingSize.eval (sizeEnvelope growth n)))
      (bodyCosts_bound growth n growthPositive sizes encodedSizes cost encodingSize bodyTime
        initialBound growthBound encodingBound bodyCost)
    have hm := Nat.mul_le_mul_right
      (bodyTime.eval (encodingSize.eval (sizeEnvelope growth n)) + 1) (rounds_le n)
    omega

end MinUncutGames.Foundations.Complexity.PCPIterationMachine

end

end OAI

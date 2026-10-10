import Mathlib

namespace OAI

universe u v

noncomputable section
open scoped BigOperators
open Filter

namespace Thorp

abbrev Position (d : ℕ) := Fin d → Bool
abbrev State (d : ℕ) := Equiv.Perm (Position d)

def Coins : ℕ → Type
  | 0 => Unit
  | d + 1 => Position d → Bool

instance coinsFintype (d : ℕ) : Fintype (Coins d) := by
  cases d <;> simp only [Coins] <;> infer_instance

instance coinsInhabited (d : ℕ) : Inhabited (Coins d) := by
  cases d <;> simp only [Coins] <;> infer_instance

def pairSwitch (d : ℕ) (c : Position d → Bool) : Equiv.Perm (Bool × Position d) where
  toFun p := (p.1 ^^ c p.2, p.2)
  invFun p := (p.1 ^^ c p.2, p.2)
  left_inv p := by
    rcases p with ⟨b, s⟩
    cases b <;> cases h : c s <;> simp [h]
  right_inv p := by
    rcases p with ⟨b, s⟩
    cases b <;> cases h : c s <;> simp [h]

def rotate (d : ℕ) : State d :=
  Equiv.piCongrLeft (fun _ : Fin d => Bool) (finRotate d).symm

def step : (d : ℕ) → Coins d → State d
  | 0, _ => Equiv.refl _
  | d + 1, c =>
    (((Fin.consEquiv (fun _ : Fin (d + 1) => Bool)).symm.trans
      (pairSwitch d c)).trans
      (Fin.consEquiv (fun _ : Fin (d + 1) => Bool))).trans (rotate (d + 1))

abbrev History (d t : ℕ) := Fin t → Coins d

def run (d t : ℕ) (ω : History d t) : State d :=
  ((List.ofFn fun i : Fin t => step d (ω i)).reverse).prod

def fairMass {Ω : Type u} {α : Type v} [Fintype Ω] (f : Ω → α) (a : α) : ℝ := by
  classical
  exact (∑ ω : Ω, if f ω = a then (1 : ℝ) else 0) / Fintype.card Ω

def law (d t : ℕ) : State d → ℝ := fairMass (run d t)

def uniform (d : ℕ) (_ : State d) : ℝ := 1 / Fintype.card (State d)

def tv {α : Type u} [Fintype α] (μ ν : α → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ a : α, |μ a - ν a|

def distance (d t : ℕ) : ℝ := tv (law d t) (uniform d)

def lawFrom (d t : ℕ) (g₀ : State d) : State d → ℝ :=
  fairMass (fun ω : History d t => run d t ω * g₀)

def mixingTime (d : ℕ) : ℕ := sInf {t : ℕ | distance d t ≤ 1 / 4}

def supportThreshold (d : ℕ) : ℤ :=
  ⌈(2 / (2 ^ d : ℝ)) * Real.logb 2 (3 * ((2 ^ d).factorial : ℝ) / 4)⌉

def orderFunction (d : ℕ) : ℝ := d

end Thorp

end

end OAI

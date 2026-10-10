import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.Stacks

namespace OAI

noncomputable section
namespace VelocityDetection.Stacks
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
variable {N b : ℕ} (hb : 0 < b) (table : Fin N → Fin b → Option (Rule (Fin N) b))

def lookup (c : Configuration (Fin N)) : Option (Rule (Fin N) b) :=
  table c.state ⟨c.rightStack % b, Nat.mod_lt _ hb⟩

def next (c : Configuration (Fin N)) : Configuration (Fin N) :=
  (lookup hb table c).elim c (fun r => applyRule r c)

def orbit (c₀ : Configuration (Fin N)) : ℕ → Configuration (Fin N)
  | 0 => c₀
  | n + 1 => next hb table (orbit c₀ n)

@[simp] theorem orbit_zero (c₀ : Configuration (Fin N)) : orbit hb table c₀ 0 = c₀ := rfl

@[simp] theorem orbit_succ (c₀ : Configuration (Fin N)) (n : ℕ) :
    orbit hb table c₀ (n + 1) = next hb table (orbit hb table c₀ n) := rfl

theorem next_eq_of_lookup {c : Configuration (Fin N)} {r : Rule (Fin N) b}
    (h : lookup hb table c = some r) : next hb table c = applyRule r c := by
  simp only [next, h, Option.elim_some]

theorem next_eq_of_none {c : Configuration (Fin N)} (h : lookup hb table c = none) :
    next hb table c = c := by simp only [next, h, Option.elim_none]

theorem next_fits {m n : ℕ} (hm : 1 ≤ m) (c : Configuration (Fin N))
    (hc : c.leftStack < capacity b m n ∧ c.rightStack < capacity b m n) :
    (next hb table c).leftStack < capacity b m (n + 1) ∧
      (next hb table c).rightStack < capacity b m (n + 1) := by
  cases h : lookup hb table c with
  | none =>
    rw [next_eq_of_none hb table h, capacity_succ]
    have hB : capacity b m n ≤ b * capacity b m n := by
      simpa using Nat.mul_le_mul_right (capacity b m n) hb
    exact ⟨hc.1.trans_le hB, hc.2.trans_le hB⟩
  | some r =>
    rw [next_eq_of_lookup hb table h]
    exact update_capacity hb hm r.written.isLt hc.1 hc.2 r.move

theorem orbit_fits {m : ℕ} (hm : 1 ≤ m) (c₀ : Configuration (Fin N))
    (hc₀ : c₀.leftStack < capacity b m 0 ∧ c₀.rightStack < capacity b m 0) (n : ℕ) :
    (orbit hb table c₀ n).leftStack < capacity b m n ∧
      (orbit hb table c₀ n).rightStack < capacity b m n := by
  induction n with
  | zero => exact hc₀
  | succ n ih => exact next_fits hb table hm _ ih

def NoOutgoing (terminal : Fin N) : Prop := ∀ α, table terminal α = none

def Continues (terminal : Fin N) (c₀ : Configuration (Fin N)) : Prop :=
  ∀ n, (orbit hb table c₀ n).state ≠ terminal → (lookup hb table (orbit hb table c₀ n)).isSome

def Reaches (terminal : Fin N) (c₀ : Configuration (Fin N)) : Prop :=
  ∃ n, (orbit hb table c₀ n).state = terminal

theorem lookup_source_nonterminal {terminal : Fin N} (hterm : NoOutgoing table terminal)
    {c : Configuration (Fin N)} (hc : (lookup hb table c).isSome) : c.state ≠ terminal := by
  intro h
  change ∀ α, table terminal α = none at hterm
  simp only [lookup, h, hterm, Option.isSome_none, Bool.false_eq_true] at hc

theorem next_terminal {terminal : Fin N} (hterm : NoOutgoing table terminal)
    {c : Configuration (Fin N)} (hc : c.state = terminal) : next hb table c = c := by
  apply next_eq_of_none
  change ∀ α, table terminal α = none at hterm
  simp only [lookup, hc, hterm]

end VelocityDetection.Stacks
end

end OAI

import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.History

namespace OAI

noncomputable section
namespace VelocityDetection.Prelude
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open scoped Topology ContDiff ZeroAtInfty BigOperators
open scoped Topology
open Stacks
variable {N b : ℕ} (hb : 0 < b)
  (table : Fin N → Fin b → Option (Rule (Fin N) b)) (q₀ : Fin N)

def rule (r : Rule (Fin N) b) : Rule (Fin (N + 1)) b :=
  ⟨r.target.castSucc, r.written, r.move⟩

def table' : Fin (N + 1) → Fin b → Option (Rule (Fin (N + 1)) b) :=
  Fin.lastCases (fun a => some ⟨q₀.castSucc, a, .stay⟩)
    (fun q a => (table q a).map rule)

def embed (c : Configuration (Fin N)) : Configuration (Fin (N + 1)) :=
  ⟨c.state.castSucc, c.leftStack, c.rightStack⟩

def initial (x y : ℕ) : Configuration (Fin (N + 1)) := ⟨Fin.last N, x, y⟩

@[simp] theorem table_cast (q : Fin N) (a : Fin b) :
    table' table q₀ q.castSucc a = (table q a).map rule := by simp [table']

@[simp] theorem table_last (a : Fin b) :
    table' table q₀ (Fin.last N) a = some ⟨q₀.castSucc, a, .stay⟩ := by simp [table']

@[simp] theorem applyRule_embed (r : Rule (Fin N) b) (c : Configuration (Fin N)) :
    applyRule (rule r) (embed c) = embed (applyRule r c) := rfl

theorem lookup_embed (c : Configuration (Fin N)) :
    lookup hb (table' table q₀) (embed c) = (lookup hb table c).map rule := by
  simp [lookup, embed]

theorem lookup_initial (x y : ℕ) :
    (lookup hb (table' table q₀) (initial (N := N) x y)).isSome := by
  simp only [lookup, initial, table_last, Option.isSome_some]

theorem next_initial (x y : ℕ) :
    next hb (table' table q₀) (initial (N := N) x y) = embed ⟨q₀, x, y⟩ := by
  have hm : y % b ≤ y := Nat.mod_le y b
  simp only [next, lookup, initial, table_last, Option.elim_some, applyRule, Stacks.update, embed]
  congr 1
  omega

theorem next_embed (c : Configuration (Fin N)) :
    next hb (table' table q₀) (embed c) = embed (next hb table c) := by
  simp only [next, lookup_embed]
  cases h : lookup hb table c <;> rfl

theorem orbit_initial (x y n : ℕ) :
    orbit hb (table' table q₀) (initial (N := N) x y) (n + 1) =
      embed (orbit hb table ⟨q₀, x, y⟩ n) := by
  induction n with
  | zero => exact next_initial hb table q₀ x y
  | succ n ih => rw [orbit_succ, ih, next_embed, orbit_succ]

theorem halts_initial (x y : ℕ) :
    History.Halts hb (table' table q₀) (initial (N := N) x y) ↔
      History.Halts hb table ⟨q₀, x, y⟩ := by
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero =>
      have hi := lookup_initial hb table q₀ x y
      simp only [orbit_zero] at hn
      simp only [hn, Option.isSome_none, Bool.false_eq_true] at hi
    | succ n =>
      rw [orbit_initial, lookup_embed, Option.map_eq_none_iff] at hn
      exact ⟨n, hn⟩
  · rintro ⟨n, hn⟩
    refine ⟨n + 1, ?_⟩
    rw [orbit_initial, lookup_embed, hn, Option.map_none]

end VelocityDetection.Prelude
end

end OAI

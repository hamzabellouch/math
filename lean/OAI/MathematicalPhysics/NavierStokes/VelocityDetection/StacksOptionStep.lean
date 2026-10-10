import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.TailDifferentiability
import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.History

namespace OAI

noncomputable section
namespace VelocityDetection.Stacks
open scoped BigOperators Topology ContDiff
open Set Function Filter
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ContDiff
open scoped Topology ContDiff BigOperators
open scoped Topology ContDiff ZeroAtInfty
open scoped Topology ContDiff ZeroAtInfty BigOperators
open scoped Topology
variable {N b : ℕ} (hb : 0 < b) (table : Fin N → Fin b → Option (Rule (Fin N) b))

def optionStep (c : Configuration (Fin N)) : Option (Configuration (Fin N)) :=
  (lookup hb table c).map (fun r => applyRule r c)

theorem optionStep_none (c : Configuration (Fin N)) :
    optionStep hb table c = none ↔ lookup hb table c = none := Option.map_eq_none_iff

theorem next_eq_of_optionStep {c d : Configuration (Fin N)}
    (h : optionStep hb table c = some d) : next hb table c = d := by
  unfold optionStep at h
  cases hl : lookup hb table c with
  | none => simp [hl] at h
  | some r =>
    simp only [hl, Option.map_some, Option.some.injEq] at h
    exact (next_eq_of_lookup hb table hl).trans h

theorem reaches_orbit (c₀ : Configuration (Fin N)) (n : ℕ) :
    StateTransition.Reaches (optionStep hb table) c₀ (orbit hb table c₀ n) := by
  induction n with
  | zero => exact Relation.ReflTransGen.refl
  | succ n ih =>
    rw [orbit_succ]
    cases h : lookup hb table (orbit hb table c₀ n) with
    | none => rw [next_eq_of_none hb table h]; exact ih
    | some r =>
      apply ih.tail
      change optionStep hb table (orbit hb table c₀ n) = some _
      rw [optionStep, h, Option.map_some, next_eq_of_lookup hb table h]

theorem orbit_of_reaches {c₀ c : Configuration (Fin N)}
    (h : StateTransition.Reaches (optionStep hb table) c₀ c) :
    ∃ n, orbit hb table c₀ n = c := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ he ih =>
    obtain ⟨n, rfl⟩ := ih
    exact ⟨n + 1, next_eq_of_optionStep hb table he⟩

theorem eval_dom_iff_halts (c₀ : Configuration (Fin N)) :
    (StateTransition.eval (optionStep hb table) c₀).Dom ↔ History.Halts hb table c₀ := by
  rw [Part.dom_iff_mem]
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨hr, hs⟩ := StateTransition.mem_eval.mp hc
    obtain ⟨n, hn⟩ := orbit_of_reaches hb table hr
    exact ⟨n, hn ▸ (optionStep_none hb table c).mp hs⟩
  · rintro ⟨n, hn⟩
    exact ⟨_, StateTransition.mem_eval.mpr
      ⟨reaches_orbit hb table c₀ n, (optionStep_none hb table _).mpr hn⟩⟩

end VelocityDetection.Stacks
end

end OAI

import OAI.Analysis.Pureness.Cuntz.SemigroupStates
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.NormNum

namespace OAI
noncomputable section
namespace CuntzPureness
namespace OrderedSemigroup
open scoped ENNReal
variable {S : Type*} [AddCommMonoid S] [PartialOrder S] [IsOrderedAddMonoid S]

def restrictState (u : S) (f : StateSpace u) :
    StateSpace (⟨u, mem_principalIdeal u⟩ : principalIdeal u) :=
  ⟨fun a => f.1 a, f.at_zero, fun a b => f.at_add a b, fun _ _ h => f.monotone h, f.at_unit⟩

theorem restrict_extendState (hzero : ∀ a : S, 0 ≤ a) (u : S)
    (f : StateSpace (⟨u, mem_principalIdeal u⟩ : principalIdeal u)) :
    restrictState u (extendState hzero u f) = f := by
  apply Subtype.ext
  funext a
  exact extendState_apply hzero u f a

theorem nonempty_states_iff_principalIdeal (hzero : ∀ a : S, 0 ≤ a) (u : S) :
    Nonempty (StateSpace u) ↔
      Nonempty (StateSpace (⟨u, mem_principalIdeal u⟩ : principalIdeal u)) :=
  ⟨fun ⟨f⟩ => ⟨restrictState u f⟩, fun ⟨f⟩ => ⟨extendState hzero u f⟩⟩

theorem state_gap_iff_principalIdeal (hzero : ∀ a : S, 0 ≤ a) (u : S)
    (a : principalIdeal u) :
    (∀ f : StateSpace u, f.1 a < 1) ↔
      ∀ f : StateSpace (⟨u, mem_principalIdeal u⟩ : principalIdeal u), f.1 a < 1 := by
  constructor
  · intro h f
    simpa only [extendState_apply] using h (extendState hzero u f)
  · intro h f
    exact h (restrictState u f)

omit [IsOrderedAddMonoid S] in
theorem uniform_state_gap (u a : S) (h : ∀ f : StateSpace u, f.1 a < 1) :
    ∃ r : ℝ≥0∞, r < 1 ∧ ∀ f : StateSpace u, f.1 a ≤ r := by
  classical
  by_cases hn : Nonempty (StateSpace u)
  · obtain ⟨f₀⟩ := hn
    obtain ⟨f, _, hf⟩ := isCompact_univ.exists_isMaxOn
      (⟨f₀, Set.mem_univ _⟩ : (Set.univ : Set (StateSpace u)).Nonempty)
      (StateSpace.continuous_eval a).continuousOn
    exact ⟨f.1 a, h f, fun g => hf (Set.mem_univ g)⟩
  · exact ⟨0, zero_lt_one, fun f => False.elim (hn ⟨f⟩)⟩

def stateRealOnIdeal (u : S) (f : StateSpace u) : principalIdeal u →+ ℝ where
  toFun a := (f.1 a).toReal
  map_zero' := by simp
  map_add' a b := by
    change (f.1 (a.1+b.1)).toReal = _
    rw [f.at_add]
    exact ENNReal.toReal_add (state_finite_on_principalIdeal f a.2)
      (state_finite_on_principalIdeal f b.2)

theorem stateRealOnIdeal_monotone (u : S) (f : StateSpace u) :
    Monotone (stateRealOnIdeal u f) := by
  intro a b hab
  exact ENNReal.toReal_mono (state_finite_on_principalIdeal f b.2) (f.monotone hab)

theorem stateRealOnIdeal_unit (u : S) (f : StateSpace u) :
    stateRealOnIdeal u f ⟨u, mem_principalIdeal u⟩ = 1 := by
  change (f.1 u).toReal = 1
  simp

omit [IsOrderedAddMonoid S] in
theorem no_state_of_properlyInfinite (u : S) (h : 2 • u ≤ u) :
    IsEmpty (StateSpace u) := by
  refine ⟨fun f => ?_⟩
  have hb := f.monotone h
  rw [f.at_nsmul, f.at_unit] at hb
  norm_num [nsmul_eq_mul] at hb
end OrderedSemigroup
end CuntzPureness

end

end OAI

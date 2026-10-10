import OAI.Analysis.CircleDomains.Topology.CircleQuantileArcs
import Mathlib.Data.Set.Countable

namespace OAI

/-! Countable collar and arc choices can be made uniform on an uncountable set. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section
namespace CircleDomainRigidity

theorem exists_uncountable_common_choice {I K : Type*} [Countable K]
    (S : Set I) (hS : ¬ S.Countable) (P : I → K → Prop)
    (hP : ∀ i ∈ S, ∃ k, P i k) :
    ∃ k, ¬ {i | i ∈ S ∧ P i k}.Countable := by
  by_contra h
  push Not at h
  apply hS
  apply (countable_iUnion h).mono
  intro i hi
  obtain ⟨k, hk⟩ := hP i hi
  exact mem_iUnion.mpr ⟨k, hi, hk⟩

theorem exists_lt_of_uncountable {I : Type*} [LinearOrder I]
    {S : Set I} (hS : ¬ S.Countable) : ∃ i ∈ S, ∃ j ∈ S, i < j := by
  by_contra h
  push Not at h
  apply hS
  apply Set.Subsingleton.countable
  intro i hi j hj
  exact le_antisymm (h j hj i hi) (h i hi j hj)

theorem exists_common_four_circle_arcs {I : Type*} (S : Set I) (hS : ¬ S.Countable)
    (μ : I → ProbabilityMeasure UnitAddCircle)
    (hμ : ∀ i ∈ S, NullSingletonClass (μ i : Measure UnitAddCircle)) :
    ∃ l u : Fin 4 → ℚ,
      (∀ k, 0 < l k ∧ l k < u k ∧ u k < 1) ∧
      (∀ k j, k < j → u k < l j) ∧
      ¬ {i | i ∈ S ∧ ∀ k, (1 / 10 : ℝ≥0∞) <
        (μ i : Measure UnitAddCircle) (rationalCircleArc (l k) (u k))}.Countable := by
  let P (i : I) (a : (Fin 4 → ℚ) × (Fin 4 → ℚ)) : Prop :=
    (∀ k, 0 < a.1 k ∧ a.1 k < a.2 k ∧ a.2 k < 1 ∧
      (1 / 10 : ℝ≥0∞) < (μ i : Measure UnitAddCircle) (rationalCircleArc (a.1 k) (a.2 k))) ∧
    ∀ k j, k < j → a.2 k < a.1 j
  have hex : ∀ i ∈ S, ∃ a, P i a := by
    intro i hi
    have := hμ i hi
    obtain ⟨l, u, hmass, hord⟩ := exists_four_ordered_rational_circle_arcs (μ i)
    exact ⟨(l, u), hmass, hord⟩
  obtain ⟨⟨l, u⟩, h⟩ := exists_uncountable_common_choice S hS P hex
  have hne : {i | i ∈ S ∧ P i (l, u)}.Nonempty := by
    by_contra hn
    exact h (Set.not_nonempty_iff_eq_empty.mp hn ▸ countable_empty)
  obtain ⟨i, hi, hp⟩ := hne
  refine ⟨l, u, fun k => ⟨(hp.1 k).1, (hp.1 k).2.1, (hp.1 k).2.2.1⟩, hp.2, ?_⟩
  intro hc
  apply h
  apply hc.mono
  intro i hi
  exact ⟨hi.1, fun k => (hi.2.1 k).2.2.2⟩

end CircleDomainRigidity

end

end OAI

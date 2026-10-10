import Mathlib
import OAI.Combinatorics.KMedianRecovery.Algorithms.BudgetBound
import OAI.Combinatorics.KMedianRecovery.Sampling.PrefixData

namespace OAI

namespace MetricKMedianRecovery.PhaseTerminalProducer
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeInvariant HistoryPhaseBound
universe uD uX
variable {D : Type uD} {X : Type uX} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

lemma terminal_prefix {loc : D → X} {F B : Finset X} {v lam eta M Z : ℝ}
    {P : List (List X)} (hF : F.Nonempty) (hv : 0 < v) (hvsmall : v < 1/6)
    (hdiam : ∀ i ∈ F, ∀ j, dist i (loc j) ≤ M) (hZ : 0 < Z) (hbound : M+lam ≤ Z)
    (hp : PrefixData loc F B v lam eta (limit v Z+1) P) :
    ∀ j, ¬activeAt loc (1-3*v) ((1+v^2)^(limit v Z)) (after ∅ P) j := by
  intro j ha
  have he := clippedAt_of_active loc (1-3*v) ((1+v^2)^(limit v Z)) (after ∅ P) j
    (by linarith only [hvsmall]) ha
  have hpow : (1+v^2)^(limit v Z) ≤ (1+v^2)^(limit v Z+1) :=
    pow_le_pow_right₀ (by nlinarith only [sq_nonneg v]) (Nat.le_succ _)
  have hm := clippedAt_mono_phase loc (1-3*v) (after ∅ P) j hpow
  have hb := UniformRowDisabling.budget_bound loc F (after ∅ P) hF (1-3*v)
    ((1+v^2)^(limit v Z+1)) lam M hp.row hdiam j
  dsimp only at hm
  rw [he] at hm
  exact (not_lt_of_ge ((hm.trans hb).trans hbound)) (limit_threshold v Z hv hZ)

lemma terminal_next {loc : D → X} {F B : Finset X} {v lam eta M Z : ℝ}
    {P : List (List X)} (hF : F.Nonempty) (hv : 0 < v) (hvsmall : v < 1/6)
    (hdiam : ∀ i ∈ F, ∀ j, dist i (loc j) ≤ M) (hZ : 0 < Z) (hbound : M+lam ≤ Z)
    (hp : PrefixData loc F B v lam eta (limit v Z+1) P) :
    ∀ j, ¬activeAt loc (1-3*v) ((1+v^2)^P.length) (after ∅ P) j := by
  intro j ha
  apply terminal_prefix hF hv hvsmall hdiam hZ hbound hp j
  intro f hf
  have hh := ha f hf
  rw [hp.length_eq] at hh
  exact lt_of_le_of_lt (pow_le_pow_right₀ (by nlinarith only [sq_nonneg v]) (Nat.le_succ _)) hh

lemma copies_bound {loc : D → X} {F B : Finset X} {v lam eta : ℝ} {q : ℕ}
    {P : List (List X)} (hp : PrefixData loc F B v lam eta q P) :
    (after ∅ P \ F).card ≤ 3*q := by
  have h := free_count F ∅ P 3 hp.free_bound
  simpa only [Finset.empty_sdiff,Finset.card_empty,zero_add,hp.length_eq] using h

theorem finished_terminal {loc : D → X} {F : Finset X} {v eta lo hi M : ℝ} {k : ℕ}
    (hF : F.Nonempty) (hv : 0 < v) (hvsmall : v < 1/6)
    (hdiam : ∀ i ∈ F, ∀ j, dist i (loc j) ≤ M) (hZ : 0 < M+hi)
    (h : Finished loc F v eta lo hi (limit v (M+hi)+1) k) :
    ∃ B lam P, Disjoint F B ∧ lo ≤ lam ∧ lam ≤ hi ∧
      History loc F B v lam eta 0 ∅ P ∧
      P.length = limit v (M+hi)+1 ∧
      (∀ j, ¬activeAt loc (1-3*v) ((1+v^2)^(limit v (M+hi))) (after ∅ P) j) ∧
      ((after ∅ P) ∩ F).card = k ∧
      (after ∅ P \ F).card ≤ 3*(limit v (M+hi)+1) := by
  obtain ⟨B,lam,P,hd,hl,hu,hp,hk⟩ := h
  exact ⟨B,lam,P,hd,hl,hu,hp.history,hp.length_eq,
    terminal_prefix hF hv hvsmall hdiam hZ (by linarith only [hu]) hp,hk,copies_bound hp⟩

end MetricKMedianRecovery.PhaseTerminalProducer

end OAI

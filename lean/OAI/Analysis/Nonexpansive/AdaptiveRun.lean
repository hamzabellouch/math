import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Positivity

namespace OAI

/-!
# Successive choices with arbitrary auxiliary state

The state may contain the entire preceding candidate history.  A threshold
is read before the next map is selected; the transition relation supplies
auxiliary choices only after that map is known.  No convex coefficients
are involved in this infinite sequence.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace ReflexiveFixedPoints

universe u v w

/-- A legal infinite sequence exists even when every threshold and every legal
auxiliary transition depends on the whole preceding state.  The caller may
take the state to be a list of all previous candidate records. -/
theorem exists_adaptive_metric_run
    {S : Type u} {M : Type v} {W : Type w} [PseudoMetricSpace W]
    {q : ℕ} (hq : 0 < q) (target : Fin q → W)
    (eval : M → W) (family : ℕ → Set M)
    (threshold : ℕ → S → ℕ)
    (transition : ℕ → S → M → S → Prop) (initial : S)
    (hclosure : ∀ (i : ℕ) (s : S) (r : Fin q),
      target r ∈ closure (eval '' family (threshold i s)))
    (htransition : ∀ (i : ℕ) (s : S) (a : M),
      a ∈ family (threshold i s) → ∃ s', transition i s a s') :
    ∃ (state : ℕ → S) (selected : ℕ → M),
      state 0 = initial ∧ ∀ i,
        selected i ∈ family (threshold i (state i)) ∧
        dist (eval (selected i)) (target ⟨i % q, Nat.mod_lt i hq⟩) <
          1 / ((i : ℝ) + 1) ∧
        transition i (state i) (selected i) (state (i + 1)) := by
  classical
  have hstep (i : ℕ) (s : S) : ∃ (a : M) (s' : S),
      a ∈ family (threshold i s) ∧
      dist (eval a) (target ⟨i % q, Nat.mod_lt i hq⟩) <
        1 / ((i : ℝ) + 1) ∧ transition i s a s' := by
    have hpos : 0 < 1 / ((i : ℝ) + 1) := by positivity
    obtain ⟨y, hy, hdist⟩ := Metric.mem_closure_iff.mp
      (hclosure i s ⟨i % q, Nat.mod_lt i hq⟩) _ hpos
    obtain ⟨a, ha, rfl⟩ := hy
    obtain ⟨s', hs'⟩ := htransition i s a ha
    exact ⟨a, s', ha, by simpa only [dist_comm] using hdist, hs'⟩
  choose pick next hmem hdist hlegal using hstep
  let state : ℕ → S := Nat.rec initial (fun i s => next i s)
  refine ⟨state, fun i => pick i (state i), rfl, ?_⟩
  intro i
  exact ⟨hmem i (state i), hdist i (state i), hlegal i (state i)⟩

/-- Cycling through finitely many targets with a vanishing error gives a
convergent subsequence for each target.  The selected maps and their state
history are otherwise unrestricted. -/
theorem tendsto_cyclic_target
    {W : Type w} [PseudoMetricSpace W] {q : ℕ} (hq : 0 < q)
    (target : Fin q → W) (u : ℕ → W)
    (hclose : ∀ i, dist (u i) (target ⟨i % q, Nat.mod_lt i hq⟩) <
      1 / ((i : ℝ) + 1)) (r : Fin q) :
    Tendsto (fun n : ℕ => u (q * n + r.val)) atTop (𝓝 (target r)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) ε hε
  refine ⟨N, ?_⟩
  intro n hn
  have hn' : N ≤ q * n + r.val :=
    hn.trans ((Nat.le_mul_of_pos_left n hq).trans (Nat.le_add_right _ _))
  have hsmall : 1 / (((q * n + r.val : ℕ) : ℝ) + 1) < ε := by
    have h := hN (q * n + r.val) hn'
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity :
      0 ≤ 1 / (((q * n + r.val : ℕ) : ℝ) + 1))] using h
  have hindex : (⟨(q * n + r.val) % q, Nat.mod_lt _ hq⟩ : Fin q) = r := by
    apply Fin.ext
    simp [Nat.add_mod, Nat.mod_eq_of_lt r.isLt]
  have h := hclose (q * n + r.val)
  rw [hindex] at h
  exact h.trans hsmall

end ReflexiveFixedPoints

end

end OAI

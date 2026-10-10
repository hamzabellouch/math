import OAI.Combinatorics.GraphThreshold.FiniteProbability
import Mathlib.Tactic

namespace OAI

/-!
# Finite adaptive trials

The draws are independent, but whether an attempt succeeds may depend on the
entire current state. The head-tail identity below performs the conditioning
explicitly. No independence assumption is made about success indicators.
-/

noncomputable section
open scoped BigOperators

universe u v

namespace LeanBlast.SecondKahnKalai

variable {State : Type u} {Ω : Type v}

/-- Split a finite draw sequence into its first draw and remaining sequence. -/
def trialSplitEquiv (Ω : Type v) (n : ℕ) : Ω × (Fin n → Ω) ≃ (Fin (n + 1) → Ω) where
  toFun p := Fin.cases p.1 p.2
  invFun draws := (draws 0, fun i => draws i.succ)
  left_inv p := by cases p; rfl
  right_inv draws := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl

namespace FiniteLaw

variable [Fintype Ω]

@[simp] theorem iid_weight_cons (μ : FiniteLaw Ω) (n : ℕ) (head : Ω) (tail : Fin n → Ω) :
    (μ.iid (n + 1)).weight (Fin.cases head tail) = μ.weight head * (μ.iid n).weight tail := by
  simp [iid_weight, Fin.prod_univ_succ]

/-- Exact finite conditional-expectation identity for a fresh independent draw. -/
theorem iid_expectation_succ (μ : FiniteLaw Ω) (n : ℕ)
    (f : (Fin (n + 1) → Ω) → ℝ) :
    (μ.iid (n + 1)).expectation f =
      μ.expectation (fun head => (μ.iid n).expectation (fun tail => f (Fin.cases head tail))) := by
  unfold expectation
  rw [← (trialSplitEquiv Ω n).sum_comp
    (fun draws => (μ.iid (n + 1)).weight draws * f draws)]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro head _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro tail _
  change (μ.iid (n + 1)).weight (Fin.cases head tail) * f (Fin.cases head tail) = _
  rw [iid_weight_cons]
  ring

end FiniteLaw

/-- A deterministic adaptive update iterated over a finite sequence of draws. -/
def adaptiveRun (step : State → Ω → State) :
    (n : ℕ) → State → (Fin n → Ω) → State
  | 0, state, _ => state
  | n + 1, state, draws => adaptiveRun step n (step state (draws 0)) (fun i => draws i.succ)

/-- Number of failed attempts along the actual adaptive state trajectory. -/
def adaptiveFailureCount (step : State → Ω → State) (bad : State → Ω → Bool) :
    (n : ℕ) → State → (Fin n → Ω) → ℕ
  | 0, _, _ => 0
  | n + 1, state, draws =>
      (if bad state (draws 0) then 1 else 0) +
        adaptiveFailureCount step bad n (step state (draws 0)) (fun i => draws i.succ)

/-- A uniform state-dependent failure bound controls expected total failures.
This proof conditions at every step on the actual preceding draw and state. -/
theorem adaptiveFailureCount_expectation_le [Fintype Ω]
    (μ : FiniteLaw Ω) (step : State → Ω → State) (bad : State → Ω → Bool)
    (q : ℝ) (hbad : ∀ state, μ.prob (fun draw => bad state draw = true) ≤ q)
    (n : ℕ) (initial : State) :
    (μ.iid n).expectation (fun draws => (adaptiveFailureCount step bad n initial draws : ℝ)) ≤
      (n : ℝ) * q := by
  induction n generalizing initial with
  | zero => simp [adaptiveFailureCount]
  | succ n ih =>
      rw [FiniteLaw.iid_expectation_succ]
      have hstep : ∀ head,
          (μ.iid n).expectation (fun tail =>
            (adaptiveFailureCount step bad (n + 1) initial (Fin.cases head tail) : ℝ)) ≤
          (if bad initial head then (1 : ℝ) else 0) + (n : ℝ) * q := by
        intro head
        by_cases hbad : bad initial head = true
        · simpa only [adaptiveFailureCount, Fin.cases_zero, Fin.cases_succ, hbad,
            ite_true, Nat.cast_add, Nat.cast_one, FiniteLaw.expectation_add,
            FiniteLaw.expectation_const] using add_le_add_right (ih (step initial head)) 1
        · simpa only [adaptiveFailureCount, Fin.cases_zero, Fin.cases_succ, hbad,
            Bool.false_eq_true, ite_false, Nat.zero_add, zero_add] using ih (step initial head)
      have h := (μ.expectation_mono hstep).trans_eq
        (μ.expectation_add (fun head => if bad initial head then (1 : ℝ) else 0)
          (fun _ => (n : ℝ) * q))
      have hindicator : μ.expectation (fun head => if bad initial head then (1 : ℝ) else 0) =
          μ.prob (fun draw => bad initial draw = true) := by
        classical
        unfold FiniteLaw.expectation FiniteLaw.prob
        apply Finset.sum_congr rfl
        intro draw _
        cases hdraw : bad initial draw <;> simp [hdraw]
      rw [FiniteLaw.expectation_const, hindicator] at h
      have hlocal := hbad initial
      push_cast
      linarith

/-- Once the rank is zero, later draws are declared successful for the purpose
of counting failures. Before then, success means a strict rank decrease. -/
def rankFailure (rank : State → ℕ) (step : State → Ω → State)
    (state : State) (draw : Ω) : Bool :=
  decide (rank state ≠ 0 ∧ ¬ rank (step state draw) < rank state)

theorem adaptiveRun_rank_le (rank : State → ℕ) (step : State → Ω → State)
    (hstep : ∀ state draw, rank (step state draw) ≤ rank state)
    (n : ℕ) (initial : State) (draws : Fin n → Ω) :
    rank (adaptiveRun step n initial draws) ≤ rank initial := by
  induction n generalizing initial with
  | zero => exact le_rfl
  | succ n ih =>
      exact (ih (step initial (draws 0)) (fun i => draws i.succ)).trans (hstep _ _)

/-- On a trajectory that is still incomplete, every nonfailed attempt consumes
at least one unit of rank. The conclusion includes the final positive rank. -/
theorem adaptiveRun_rank_failure_bound (rank : State → ℕ) (step : State → Ω → State)
    (hstep : ∀ state draw, rank (step state draw) ≤ rank state)
    (n : ℕ) (initial : State) (draws : Fin n → Ω)
    (hincomplete : rank (adaptiveRun step n initial draws) ≠ 0) :
    n + rank (adaptiveRun step n initial draws) ≤
      rank initial + adaptiveFailureCount step (rankFailure rank step) n initial draws := by
  induction n generalizing initial with
  | zero => simp [adaptiveRun, adaptiveFailureCount]
  | succ n ih =>
      have htail := ih (step initial (draws 0)) (fun i => draws i.succ) hincomplete
      have hdecrease := hstep initial (draws 0)
      have hinit : rank initial ≠ 0 := by
        have hbound := adaptiveRun_rank_le rank step hstep (n + 1) initial draws
        omega
      change (n + 1) + rank (adaptiveRun step n (step initial (draws 0))
          (fun i => draws i.succ)) ≤
        rank initial + ((if rankFailure rank step initial (draws 0) then 1 else 0) +
          adaptiveFailureCount step (rankFailure rank step) n (step initial (draws 0))
            (fun i => draws i.succ))
      by_cases hprogress : rank (step initial (draws 0)) < rank initial
      · have hbad : rankFailure rank step initial (draws 0) = false := by
          simp [rankFailure, hprogress]
        simp [hbad]
        omega
      · have hbad : rankFailure rank step initial (draws 0) = true := by
          simp [rankFailure, hinit, hprogress]
        simp [hbad]
        omega

theorem rankFailure_probability_le [Fintype Ω] (μ : FiniteLaw Ω)
    (rank : State → ℕ) (step : State → Ω → State)
    (hprogress : ∀ state, rank state ≠ 0 →
      (3 / 4 : ℝ) ≤ μ.prob (fun draw => rank (step state draw) < rank state))
    (state : State) :
    μ.prob (fun draw => rankFailure rank step state draw = true) ≤ (1 / 4 : ℝ) := by
  by_cases hz : rank state = 0
  · simp [rankFailure, hz, FiniteLaw.prob]
  · have heq : μ.prob (fun draw => rankFailure rank step state draw = true) =
        1 - μ.prob (fun draw => rank (step state draw) < rank state) := by
      simpa [rankFailure, hz] using
        μ.prob_compl (fun draw => rank (step state draw) < rank state)
    rw [heq]
    linarith [hprogress state hz]

/-- Noncompletion by time `4*s` forces at least `3*s+1` failed attempts. -/
theorem adaptive_incomplete_many_failures (rank : State → ℕ) (step : State → Ω → State)
    (hstep : ∀ state draw, rank (step state draw) ≤ rank state)
    (s : ℕ) (initial : State) (hinitial : rank initial ≤ s)
    (draws : Fin (4 * s) → Ω)
    (hincomplete : rank (adaptiveRun step (4 * s) initial draws) ≠ 0) :
    3 * s + 1 ≤ adaptiveFailureCount step (rankFailure rank step) (4 * s) initial draws := by
  have h := adaptiveRun_rank_failure_bound rank step hstep (4 * s) initial draws hincomplete
  omega

/-- Adaptive finite completion bound. Only fresh draws are independent.
The chance of progress can depend arbitrarily on the current state.
The case `s=0` is included. -/
theorem adaptive_rank_completion [Fintype Ω] (μ : FiniteLaw Ω)
    (rank : State → ℕ) (step : State → Ω → State)
    (hstep : ∀ state draw, rank (step state draw) ≤ rank state)
    (hprogress : ∀ state, rank state ≠ 0 →
      (3 / 4 : ℝ) ≤ μ.prob (fun draw => rank (step state draw) < rank state))
    (s : ℕ) (initial : State) (hinitial : rank initial ≤ s) :
    (2 / 3 : ℝ) ≤ (μ.iid (4 * s)).prob
      (fun draws => rank (adaptiveRun step (4 * s) initial draws) = 0) := by
  let ν := μ.iid (4 * s)
  let F : (Fin (4 * s) → Ω) → ℝ := fun draws =>
    adaptiveFailureCount step (rankFailure rank step) (4 * s) initial draws
  have hF : ∀ draws, 0 ≤ F draws := fun _ => Nat.cast_nonneg _
  have hexpected := adaptiveFailureCount_expectation_le μ step (rankFailure rank step)
    (1 / 4) (rankFailure_probability_le μ rank step hprogress) (4 * s) initial
  have hE : ν.expectation F ≤ (s : ℝ) := by
    convert hexpected using 1
    push_cast
    ring
  have ht : 0 < 3 * (s : ℝ) + 1 := by positivity
  have hsubset : ν.prob (fun draws => rank (adaptiveRun step (4 * s) initial draws) ≠ 0) ≤
      ν.prob (fun draws => 3 * (s : ℝ) + 1 ≤ F draws) := by
    apply ν.prob_mono
    intro draws hinc
    have h := adaptive_incomplete_many_failures rank step hstep s initial hinitial draws hinc
    dsimp [F]
    exact_mod_cast h
  have hMarkov := ν.prob_ge_le_expectation_div F hF ht
  have hbad : ν.prob (fun draws => rank (adaptiveRun step (4 * s) initial draws) ≠ 0) ≤
      (s : ℝ) / (3 * (s : ℝ) + 1) :=
    (hsubset.trans hMarkov).trans (div_le_div_of_nonneg_right hE ht.le)
  have hratio : (s : ℝ) / (3 * (s : ℝ) + 1) ≤ (1 / 3 : ℝ) := by
    apply (div_le_iff₀ ht).mpr
    linarith
  have hbad' := hbad.trans hratio
  have hcomplement := ν.prob_compl
    (fun draws => rank (adaptiveRun step (4 * s) initial draws) = 0)
  change (2 / 3 : ℝ) ≤ ν.prob (fun draws => rank (adaptiveRun step (4 * s) initial draws) = 0)
  linarith

/-- Counter form for the tree reduction: counters never decrease, and while
fewer than `s` successful rounds have occurred the chance of an increase is
at least three quarters. No finite-state assumption is needed. -/
theorem adaptive_counter_completion [Fintype Ω] (μ : FiniteLaw Ω)
    (counter : State → ℕ) (step : State → Ω → State)
    (hstep : ∀ state draw, counter state ≤ counter (step state draw))
    (s : ℕ)
    (hprogress : ∀ state, counter state < s →
      (3 / 4 : ℝ) ≤ μ.prob (fun draw => counter state < counter (step state draw)))
    (initial : State) :
    (2 / 3 : ℝ) ≤ (μ.iid (4 * s)).prob
      (fun draws => s ≤ counter (adaptiveRun step (4 * s) initial draws)) := by
  let rank : State → ℕ := fun state => s - counter state
  have hrank : ∀ state draw, rank (step state draw) ≤ rank state := by
    intro state draw
    exact Nat.sub_le_sub_left (hstep state draw) s
  have hprob : ∀ state, rank state ≠ 0 →
      (3 / 4 : ℝ) ≤ μ.prob (fun draw => rank (step state draw) < rank state) := by
    intro state hne
    have hlt : counter state < s := by dsimp [rank] at hne; omega
    apply (hprogress state hlt).trans
    apply μ.prob_mono
    intro draw hdraw
    dsimp [rank]
    omega
  have h := adaptive_rank_completion μ rank step hrank hprob s initial (Nat.sub_le _ _)
  simpa only [rank, Nat.sub_eq_zero_iff_le] using h

end LeanBlast.SecondKahnKalai

end

end OAI

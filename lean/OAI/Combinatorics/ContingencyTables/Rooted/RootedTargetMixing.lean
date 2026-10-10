import OAI.Combinatorics.ContingencyTables.Rooted.RootedTargetTrace
import OAI.Combinatorics.ContingencyTables.Rooted.RootedTrace
import OAI.Combinatorics.ContingencyTables.Counting.CompanionTargetMixing

namespace OAI

/-! # Actual selected-root dyadic trace mixing and warm restart schedule -/

namespace ContingencyTables.RootedTargetMixing

open CommonBasesFPRAS CompanionFactorialApplication RootedBooleanPhase RootedTargetTrace
open RootedTraceWords RootedAnnealing RootedWarmStart CompanionRationalUpdates TwoLiftStates
open DegreeCompletion ObservableBounds
open CompanionBooleanPhase (State slowdown slowdown_bounds)
open CompanionConcentration (pairs_ne_nil square_width_one_le)
open CompanionTargetMixing (restartTime restart_schedule)
open scoped BigOperators Classical

noncomputable section

private theorem trace_exit_congr {X : Type*} [Fintype X]
    (C D : FiniteChain X) (B : X → Prop) [Nonempty (FiniteChain.Inside B)]
    (h : C=D)
    (hC : ∀ x : FiniteChain.Outside B,∃ y : FiniteChain.Inside B,0<C.P x.val y.val)
    (hD : ∀ x : FiniteChain.Outside B,∃ y : FiniteChain.Inside B,0<D.P x.val y.val) :
    C.traceChain B (C.killedChain B hC) (by intro x y; rfl)=
      D.traceChain B (D.killedChain B hD) (by intro x y; rfl) := by
  cases h
  rfl

variable {I J : Type} [Fintype I] [Fintype J]

def literalTrace (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ) (hp : 0<Fintype.card (Labels A))
    (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q) :
    FiniteChain (PlainIndex (pairs : List (Pair A))) :=
  metropolisTrace pairs PairedLabels.fresh (pairs_ne_nil A hp) PairedLabels.cover
    (fun p q => (w p q:ℝ)) (weight A R j)
    (fun p q => by exact_mod_cast hw p q) (weight_positive A R j)

theorem literalTrace_eq_completed (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ)
    (hp : 0<Fintype.card (Labels A)) (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q) :
    literalTrace A R j hp w hw=RootedTrace.trace A R j hp (fun p q => (w p q:ℝ))
      (fun p q => by exact_mod_cast hw p q) := by
  let := plainIndex_nonempty (pairs : List (Pair A)) PairedLabels.fresh PairedLabels.cover
  let F := completeDegree (weight A R j) (pairs : List (Pair A)).length
  have hF := completeDegree_positive (weight A R j) (pairs : List (Pair A)).length
    (actual_degree A R j).1
  have h := trace_exit_congr (referenceChain A R j hp w hw)
    (metropolisChain pairs PairedLabels.fresh (pairs_ne_nil A hp) PairedLabels.cover
      (fun p q => (w p q:ℝ)) F (fun p q => by exact_mod_cast hw p q) hF)
    (plainPredicate pairs) (referenceChain_eq_completed A R j hp w hw)
    (metropolis_plain_exit pairs PairedLabels.fresh (pairs_ne_nil A hp) PairedLabels.cover
      (fun p q => (w p q:ℝ)) (weight A R j)
      (fun p q => by exact_mod_cast hw p q) (weight_positive A R j))
    (metropolis_plain_exit pairs PairedLabels.fresh (pairs_ne_nil A hp) PairedLabels.cover
      (fun p q => (w p q:ℝ)) F (fun p q => by exact_mod_cast hw p q) hF)
  exact h

private lemma literalTrace_poincare (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ)
    (hp : 0<Fintype.card (Labels A)) (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q)
    (hgood : GoodMultipliers pairs (weight A R j) (fun p q => (w p q:ℝ)))
    (H : PlainIndex (pairs : List (Pair A)) → ℝ) :
    (literalTrace A R j hp w hw).variance H≤
      observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2)*
        (literalTrace A R j hp w hw).energy H := by
  rw [literalTrace_eq_completed]
  exact RootedTrace.trace_poincare A R j hp (fun p q => (w p q:ℝ)) hgood H

theorem targetTrace_poincare (A : Instance I J) (R : RootedCompletion.Selection A.T) (j : ℕ)
    (hp : 0<Fintype.card (Labels A)) (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q)
    (hgood : GoodMultipliers pairs (weight A R j) (fun p q => (w p q:ℝ)))
    (H : PlainIndex (pairs : List (Pair A)) → ℝ) :
    (RootedTargetTrace.actualTrace A R j hp w hw).variance H≤
      (2*observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2))*
        (RootedTargetTrace.actualTrace A R j hp w hw).energy H := by
  let := plainIndex_nonempty (pairs : List (Pair A)) PairedLabels.fresh PairedLabels.cover
  have hnonneg : 0≤observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2) := by
    unfold observableConstant
    positivity
  have hh := FiniteChainSlowdown.trace_variance_bound (referenceChain A R j hp w hw)
    (plainPredicate pairs) (sourceKilled A R j hp w hw) (by intro x y; rfl)
    (slowdown A) (by linarith [(slowdown_bounds A hp).1]) (slowdown_bounds A hp).2
    (slowdown_bounds A hp).1
    (observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2)) hnonneg H
    (literalTrace_poincare A R j hp w hw hgood H)
  exact hh

theorem target_point_mixing (A : Instance I J) (R : RootedCompletion.Selection A.T) (H K j : ℕ) (hj : j≤H)
    (hB : (∏ s : SmallCell A,((A.b s.val.1 s.val.2:ℝ)+1))≤(2:ℝ)^K)
    (hp : 0<Fintype.card (Labels A)) (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q)
    (hgood : GoodMultipliers pairs (weight A R j) (fun p q => (w p q:ℝ))) (t : ℕ)
    (x y : PlainIndex (pairs : List (Pair A))) :
    |((RootedTargetTrace.actualTrace A R j hp w hw).kernel.power t).P x y/
      law A R j y.val.val-1|≤
        Real.exp (-(t:ℝ)/(2*observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2)))/
          CompanionTrace.minimumMass A H K := by
  have hpR : (1:ℝ)≤Fintype.card (Labels A) := by exact_mod_cast hp
  have hK : 1≤2*observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2) := by
    have hh := observableConstant_lower (Fintype.card (Labels A)) ((A.W:ℝ)^2)
      hpR (square_width_one_le A)
    have hp5 : (1:ℝ)≤(Fintype.card (Labels A):ℝ)^5 := one_le_pow₀ hpR
    linarith
  have hmin (S : PlainIndex (pairs : List (Pair A))) :
      CompanionTrace.minimumMass A H K≤(RootedTargetTrace.actualTrace A R j hp w hw).π S := by
    rw [actualTrace_pi]
    have hh := RootedTrace.trace_minimum A R H K j hj hB hp
      (fun p q => (w p q:ℝ)) (fun p q => by exact_mod_cast hw p q) S
    rw [RootedTrace.trace_pi] at hh
    exact hh
  have hh := (RootedTargetTrace.actualTrace A R j hp w hw).kernel_point_mixing
    (2*observableConstant (Fintype.card (Labels A)) ((A.W:ℝ)^2))
    (CompanionTrace.minimumMass A H K) hK (CompanionTrace.minimumMass_positive A H K)
    hmin (targetTrace_poincare A R j hp w hw hgood) t x y
  rwa [actualTrace_pi] at hh

/-- The exact dyadic trace reaches the required two-warm law at the
explicit doubled schedule, including subprobability incoming laws. -/
theorem restart_warm (A : Instance I J) (R : RootedCompletion.Selection A.T) (H K j : ℕ) (hj : j≤H)
    (hB : (∏ s : SmallCell A,((A.b s.val.1 s.val.2:ℝ)+1))≤(2:ℝ)^K)
    (hp : 0<Fintype.card (Labels A)) (w : Pair A → Pair A → ℚ) (hw : ∀ p q,0<w p q)
    (hgood : GoodMultipliers pairs (weight A R j) (fun p q => (w p q:ℝ)))
    (nu : PlainIndex (pairs : List (Pair A)) → ℝ) (hnu : ∀ S,0≤nu S)
    (hmass : ∑ S,nu S≤1) (y : PlainIndex (pairs : List (Pair A))) :
    ((RootedTargetTrace.actualTrace A R j hp w hw).kernel.power (restartTime A H K)).push nu y≤
      2*law A R j y.val.val := by
  have hy : 0<law A R j y.val.val :=
    div_pos (weight_positive A R j _) (total_positive A R j)
  have hrow (x : PlainIndex (pairs : List (Pair A))) :
      ((RootedTargetTrace.actualTrace A R j hp w hw).kernel.power (restartTime A H K)).P x y≤
        2*law A R j y.val.val := by
    have hh := (le_abs_self _).trans
      ((target_point_mixing A R H K j hj hB hp w hw hgood (restartTime A H K) x y).trans
        (restart_schedule A H K hp))
    apply (div_le_iff₀ hy).mp
    linarith
  calc
    _ ≤ ∑ x,nu x*(2*law A R j y.val.val) :=
      Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hrow x) (hnu x))
    _ = (∑ x,nu x)*(2*law A R j y.val.val) := by rw [Finset.sum_mul]
    _ ≤ _ := by nlinarith

end
end ContingencyTables.RootedTargetMixing

end OAI

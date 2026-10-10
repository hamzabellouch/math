import OAI.Combinatorics.Ryser.Selection.SmallCertificates
import OAI.Combinatorics.Ryser.Selection.Estimates

namespace OAI

open scoped BigOperators

namespace RyserCoveringCounterexample.Selection

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n K : ℕ}

theorem prob_noFeasibleOutside_join_eq_prod (data : Data F n)
    (I : Finset (Fin n)) (T : Finset (Position n K))
    (x : ExposedAssignment (F := F) T) :
    (FiniteLaw.uniform (FreshAssignment (F := F) T)).prob
      (fun y => NoFeasibleOutside data I T (joinAssignments T x y)) =
      ∏ e ∈ freshTargets I T,
        (1 - (FiniteLaw.uniform (Point F)).prob
          (Feasible data T (frozenPool T x) e.val.1)) := by
  classical
  have hP :
      (fun y : FreshAssignment (F := F) T =>
        NoFeasibleOutside data I T (joinAssignments T x y)) =
      (fun y => ∀ e ∈ freshTargets I T,
        ¬Feasible data T (frozenPool T x) e.val.1 (y e)) := by
    funext y
    exact propext (noFeasibleOutside_join_iff data I T x y)
  rw [hP]
  calc
    _ = (FiniteLaw.pi (fun _ : {e : Position n K // e ∉ T} =>
        FiniteLaw.uniform (Point F))).prob
        (fun y => ∀ e ∈ freshTargets I T,
          ¬Feasible data T (frozenPool T x) e.val.1 (y e)) := by
      rw [FiniteLaw.pi_uniform]
    _ = ∏ e ∈ freshTargets I T, (FiniteLaw.uniform (Point F)).prob
        (fun b => ¬Feasible data T (frozenPool T x) e.val.1 b) :=
      prob_pi_forall_mem
        (fun _ : {e : Position n K // e ∉ T} => FiniteLaw.uniform (Point F))
        (freshTargets I T)
        (fun e b => ¬Feasible data T (frozenPool T x) e.val.1 b)
    _ = _ := by
      apply Finset.prod_congr rfl
      intro e he
      exact (FiniteLaw.uniform (Point F)).prob_compl
        (Feasible data T (frozenPool T x) e.val.1)

theorem prob_noFeasibleOutside_join_le_exp_neg_sum (data : Data F n)
    (I : Finset (Fin n)) (T : Finset (Position n K))
    (x : ExposedAssignment (F := F) T) :
    (FiniteLaw.uniform (FreshAssignment (F := F) T)).prob
      (fun y => NoFeasibleOutside data I T (joinAssignments T x y)) ≤
      Real.exp (-(∑ e ∈ freshTargets I T, (FiniteLaw.uniform (Point F)).prob
        (Feasible data T (frozenPool T x) e.val.1))) := by
  rw [prob_noFeasibleOutside_join_eq_prod]
  simpa only [pow_one, Nat.cast_one, one_mul] using
    prod_one_sub_pow_le_exp_neg_sum (freshTargets I T)
      (fun e => (FiniteLaw.uniform (Point F)).prob
        (Feasible data T (frozenPool T x) e.val.1))
      (fun _ => 1) (fun e _ => (FiniteLaw.uniform (Point F)).prob_le_one _)

end RyserCoveringCounterexample.Selection

end OAI

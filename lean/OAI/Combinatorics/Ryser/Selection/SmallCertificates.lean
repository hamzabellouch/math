import OAI.Combinatorics.Ryser.Selection.PoolLaw
import OAI.Combinatorics.Ryser.Selection.Forbidden
import OAI.Combinatorics.Ryser.Selection.IndependentTail

namespace OAI

open scoped BigOperators
namespace RyserCoveringCounterexample.Selection

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n K : ℕ}

def NoFeasibleOutside (data : Data F n) (I : Finset (Fin n))
    (T : Finset (Position n K)) (pool : Pool F n K) : Prop :=
  ∀ e : Position n K, e.1 ∈ I → e ∉ T → ¬Feasible data T pool e.1 (pool e)

def freshTargets (I : Finset (Fin n)) (T : Finset (Position n K)) :
    Finset {e : Position n K // e ∉ T} :=
  Finset.univ.filter fun e => e.val.1 ∈ I

theorem noFeasibleOutside_join_iff (data : Data F n) (I : Finset (Fin n))
    (T : Finset (Position n K)) (x : ExposedAssignment (F := F) T)
    (y : FreshAssignment (F := F) T) :
    NoFeasibleOutside data I T (joinAssignments T x y) ↔
      ∀ e ∈ freshTargets I T, ¬Feasible data T (frozenPool T x) e.val.1 (y e) := by
  constructor
  · intro h e he
    have hi := (Finset.mem_filter.mp he).2
    have hh := h e.val hi e.property
    simpa only [joinAssignments_fresh, feasible_join_iff] using hh
  · intro h e hi he
    have hmem : (⟨e, he⟩ : {e : Position n K // e ∉ T}) ∈ freshTargets I T := by
      simp only [freshTargets, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hi
    have hh := h ⟨e, he⟩ hmem
    have hj : joinAssignments T x y e = y ⟨e, he⟩ :=
      joinAssignments_fresh T x y ⟨e, he⟩
    rw [hj, feasible_join_iff]
    exact hh

theorem prob_noFeasibleOutside_le {D : ℕ} (data : Data F n) (hdata : Bounded D data)
    (I : Finset (Fin n)) (T : Finset (Position n K)) :
    (poolLaw F n K).prob (NoFeasibleOutside data I T) ≤
      ((T.card : ℝ) * ((2 * (D : ℝ) ^ 3) / (Fintype.card F : ℝ))) ^
        (freshTargets I T).card := by
  classical
  refine poolLaw_prob_split_le T (NoFeasibleOutside data I T)
    (((T.card : ℝ) * ((2 * (D : ℝ) ^ 3) / (Fintype.card F : ℝ))) ^
      (freshTargets I T).card) ?_
  intro x
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
        (freshTargets I T) (fun e b => ¬Feasible data T (frozenPool T x) e.val.1 b)
    _ ≤ ∏ _e ∈ freshTargets I T,
        ((T.card : ℝ) * ((2 * (D : ℝ) ^ 3) / (Fintype.card F : ℝ))) := by
      apply Finset.prod_le_prod₀
      · exact fun e _ => (FiniteLaw.uniform (Point F)).prob_nonneg _
      · exact fun e _ => prob_not_feasible_le data hdata T (frozenPool T x) e.val.1
    _ = _ := by simp

end RyserCoveringCounterexample.Selection

end OAI

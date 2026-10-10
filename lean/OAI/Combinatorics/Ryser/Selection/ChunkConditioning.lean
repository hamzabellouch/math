import OAI.Combinatorics.Ryser.Selection.PoolLaw

namespace OAI

noncomputable section

namespace RyserCoveringCounterexample.Selection

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n K : ℕ}

theorem joinAssignments_restrict_exposed (T : Finset (Position n K))
    (x : ExposedAssignment (F := F) T) (y : FreshAssignment (F := F) T) :
    (fun e : {e : Position n K // e ∈ T} => joinAssignments T x y e.val) = x := by
  funext e
  exact joinAssignments_exposed T x y e

theorem feasibleSet_frozenPool_restrict (data : Data F n)
    (T : Finset (Position n K)) (pool : Pool F n K) :
    feasibleSet data T
        (frozenPool T (fun e : {e : Position n K // e ∈ T} => pool e.val)) =
      feasibleSet data T pool := by
  funext i
  apply Finset.ext
  intro b
  rw [mem_feasibleSet, mem_feasibleSet]
  apply feasible_congr
  intro e he
  exact joinAssignments_exposed T (fun e => pool e.val) (fun _ => 0) ⟨e, he⟩

theorem prob_joinAssignments_eq_of_dependsOn_compl (T : Finset (Position n K))
    (Q : Pool F n K → Prop)
    (hQ : ∀ pool pool' : Pool F n K,
      (∀ e, e ∉ T → pool e = pool' e) → (Q pool ↔ Q pool'))
    (x : ExposedAssignment (F := F) T) :
    (FiniteLaw.uniform (FreshAssignment (F := F) T)).prob
        (fun y => Q (joinAssignments T x y)) =
      (poolLaw F n K).prob Q := by
  symm
  rw [poolLaw_prob_split T Q]
  calc
    _ = (FiniteLaw.uniform (ExposedAssignment (F := F) T)).expectation
        (fun _ => (FiniteLaw.uniform (FreshAssignment (F := F) T)).prob
          (fun y => Q (joinAssignments T x y))) := by
      apply congrArg (FiniteLaw.expectation
        (FiniteLaw.uniform (ExposedAssignment (F := F) T)))
      funext x'
      apply congrArg (FiniteLaw.prob
        (FiniteLaw.uniform (FreshAssignment (F := F) T)))
      funext y
      apply propext
      apply hQ
      intro e he
      exact (joinAssignments_fresh T x' y ⟨e, he⟩).trans
        (joinAssignments_fresh T x y ⟨e, he⟩).symm
    _ = _ := FiniteLaw.expectation_const _ _

theorem poolLaw_prob_adaptive_le (T : Finset (Position n K))
    (H : ExposedAssignment (F := F) T → Pool F n K → Prop) (b : ℝ)
    (hcongr : ∀ x : ExposedAssignment (F := F) T,
      ∀ pool pool' : Pool F n K,
      (∀ e, e ∉ T → pool e = pool' e) → (H x pool ↔ H x pool'))
    (hbound : ∀ x : ExposedAssignment (F := F) T,
      (poolLaw F n K).prob (H x) ≤ b) :
    (poolLaw F n K).prob
        (fun pool => H (fun e : {e : Position n K // e ∈ T} => pool e.val) pool) ≤ b := by
  apply poolLaw_prob_split_le T
  intro x
  calc
    _ = (FiniteLaw.uniform (FreshAssignment (F := F) T)).prob
        (fun y => H x (joinAssignments T x y)) := by
      apply congrArg (FiniteLaw.prob
        (FiniteLaw.uniform (FreshAssignment (F := F) T)))
      funext y
      rw [joinAssignments_restrict_exposed]
    _ = (poolLaw F n K).prob (H x) :=
      prob_joinAssignments_eq_of_dependsOn_compl T (H x) (hcongr x) x
    _ ≤ b := hbound x

end RyserCoveringCounterexample.Selection

end

end OAI

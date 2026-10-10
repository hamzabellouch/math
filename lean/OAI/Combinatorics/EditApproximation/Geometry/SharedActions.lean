import OAI.Combinatorics.EditApproximation.Geometry.ActualActionValues
import OAI.Combinatorics.EditApproximation.Geometry.Grid

namespace OAI

/-! Exact connection cancellation for shared-endpoint finite actions. -/

namespace EditApproximation

theorem connectionBudget_ofFn_zero {n : ℕ} (M : ℕ) (states : Fin M → TargetInterval n)
    (start finish : ℕ)
    (hstart : ∀ i : Fin M, i.val = 0 → start = (states i).lo)
    (hnext : ∀ i j : Fin M, j.val = i.val + 1 → (states i).hi = (states j).lo)
    (hend : ∀ i : Fin M, i.val + 1 = M → (states i).hi = finish)
    (hempty : M = 0 → start = finish) :
    connectionBudget start (List.ofFn states) finish = 0 := by
  induction M generalizing start with
  | zero => simp only [List.ofFn_zero, connectionBudget, hempty rfl, Nat.dist_self]
  | succ M ih =>
    rw [List.ofFn_succ, connectionBudget, hstart 0 rfl, Nat.dist_self, zero_add]
    apply ih (fun i => states i.succ) (states 0).hi
    · intro i hi
      exact hnext 0 i.succ (by simp only [Fin.val_zero, Fin.val_succ]; omega)
    · intro i j hij
      exact hnext i.succ j.succ (by simp only [Fin.val_succ]; omega)
    · intro i hi
      exact hend i.succ (by simp only [Fin.val_succ]; omega)
    · intro hM
      exact hend 0 (by simp only [Fin.val_zero]; omega)

theorem endpointActionConnection_zero {n M : ℕ} (hM : 0 < M) (q : TargetInterval n)
    (states : Fin M → TargetInterval n)
    (hstart : (states ⟨0, hM⟩).lo = q.lo)
    (hend : (states ⟨M - 1, by omega⟩).hi = q.hi)
    (hnext : ∀ i j : Fin M, j.val = i.val + 1 → (states i).hi = (states j).lo) :
    endpointActionConnection q states = 0 := by
  apply connectionBudget_ofFn_zero
  · intro i hi
    have heq : i = ⟨0, hM⟩ := Fin.ext hi
    rw [heq]
    exact hstart.symm
  · exact hnext
  · intro i hi
    have heq : i = ⟨M - 1, by omega⟩ := Fin.ext (by change i.val = M - 1; omega)
    rw [heq]
    exact hend
  · omega

theorem round_shared_action {n M g : ℕ} (hM : 0 < M) (q : TargetInterval n)
    (states : Fin M → TargetInterval n)
    (hstart : (states ⟨0, hM⟩).lo = q.lo)
    (hend : (states ⟨M - 1, by omega⟩).hi = q.hi)
    (hnext : ∀ i j : Fin M, j.val = i.val + 1 → (states i).hi = (states j).lo)
    (hqGrid : g ∣ q.lo ∧ g ∣ q.hi) :
    endpointActionConnection q (fun i => roundInterval g (states i)) = 0 := by
  apply endpointActionConnection_zero hM q
  · change gridRound g (states ⟨0, hM⟩).lo = q.lo
    rw [hstart, gridRound_of_dvd hqGrid.1]
  · change gridRound g (states ⟨M - 1, by omega⟩).hi = q.hi
    rw [hend, gridRound_of_dvd hqGrid.2]
  · intro i j hij
    exact roundInterval_shared (states i) (states j) (hnext i j hij)

theorem zero_connection_target_eq {α : Type*} (target : List α) {M : ℕ}
    (q : TargetInterval target.length) (states : Fin M → TargetInterval target.length)
    (hconn : endpointActionConnection q states = 0) :
    targetConcatenation target (List.ofFn states) = substring target q.lo q.hi := by
  have h := target_connection_bound target (List.ofFn states) q
  change EditDistortion.edit _ _ ≤ endpointActionConnection q states at h
  rw [hconn] at h
  exact (EditDistortion.cost_eq_zero_iff (s := true)).mp (Nat.eq_zero_of_le_zero h)

theorem zero_connection_gap_sum {α : Type*} (source target : List α) {M : ℕ}
    (hM : 0 < M) (parent : TargetInterval source.length)
    (q : TargetInterval target.length) (states : Fin M → TargetInterval target.length)
    (hconn : endpointActionConnection q states = 0) :
    (∑ i, stateLengthGap
      (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target (states i)) =
        stateLengthGap (substring source parent.lo parent.hi) target q := by
  let piece := fun i : Fin M =>
    substring source (sourceChild parent i).lo (sourceChild parent i).hi
  have hsource := congrArg List.length (sourceChild_partition source hM parent)
  simp only [List.length_flatten, List.map_ofFn, List.sum_ofFn, Function.comp_def] at hsource
  have htarget := congrArg List.length (zero_connection_target_eq target q states hconn)
  simp only [targetConcatenation, List.length_flatten, List.map_ofFn,
    List.sum_ofFn, Function.comp_def] at htarget
  have hsourceR : (∑ i, ((piece i).length : ℝ)) =
      (substring source parent.lo parent.hi).length := by exact_mod_cast hsource
  have htargetR : (∑ i, ((substring target (states i).lo (states i).hi).length : ℝ)) =
      (substring target q.lo q.hi).length := by exact_mod_cast htarget
  simp only [stateLengthGap_actual, signedLengthGap, Finset.sum_sub_distrib]
  rw [htargetR, hsourceR]

theorem zero_connection_cost_sum_lower {α : Type*} (source target : List α) {M : ℕ}
    (hM : 0 < M) (parent : TargetInterval source.length)
    (q : TargetInterval target.length) (states : Fin M → TargetInterval target.length)
    (hconn : endpointActionConnection q states = 0) :
    (stateEditCost (substring source parent.lo parent.hi) target q : ℝ) ≤
      ∑ i, (stateEditCost
        (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target (states i) : ℝ) := by
  have h := actual_endpoint_action_lower source target hM parent q states 1 le_rfl
    (fun i s => (stateEditCost
      (substring source (sourceChild parent i).lo (sourceChild parent i).hi) target s : ℝ))
    (by intro i; simp only [div_one, le_refl])
    (fun i => stateEditCost_length_lower _ _ _)
  have hlower := (le_max_left _ _).trans h
  simpa only [div_one, endpointActionValue, hconn, Nat.cast_zero, zero_add] using hlower

end EditApproximation

end OAI

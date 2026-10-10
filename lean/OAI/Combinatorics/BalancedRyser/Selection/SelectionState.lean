import OAI.Combinatorics.BalancedRyser.Selection.SelectionProcessLaw

namespace OAI

namespace Balanced.Selection.Process

noncomputable section
attribute [local instance] Classical.propDecidable

variable {I V : Type*} [Fintype I] [Fintype V]

private theorem exists_positive_of_sum_positive {α : Type*} [Fintype α]
    (f : α → ℝ) (h : 0 < ∑ a, f a) : ∃ a, 0 < f a := by
  by_contra hn
  push Not at hn
  exact (not_lt_of_ge (Finset.sum_nonpos (fun a _ => hn a))) h

def StateInvariant (G : Input I V) (S : State I V) : Prop :=
  (∀ v ∈ S.alive, G.slot v ∈ S.remaining) ∧
  (∀ i, S.recorded i = none ↔ i ∈ S.remaining) ∧
  (∀ i v, S.recorded i = some v → G.slot v = i) ∧
  (∀ i j v w, S.recorded i = some v → S.recorded j = some w → i ≠ j → ¬ G.graph.Adj v w) ∧
  (∀ i w, S.recorded i = some w → ∀ v ∈ S.alive, ¬ G.graph.Adj w v)

theorem initialState_invariant (G : Input I V) : StateInvariant G initialState := by
  simp [StateInvariant, initialState]

omit [Fintype I] [Fintype V] in
theorem update_invariant (G : Input I V) (S : State I V) (hS : StateInvariant G S)
    (i : I) (w : V) (_hi : i ∈ S.remaining) (hw : w ∈ domain G S i)
    (flags : V → Bool) : StateInvariant G (update G S i w flags) := by
  have hwalive : w ∈ S.alive := (Finset.mem_filter.mp hw).1
  have hwslot : G.slot w = i := (Finset.mem_filter.mp hw).2
  have halive {v : V} (hv : v ∈ (update G S i w flags).alive) :
      v ∈ S.alive ∧ ¬ G.graph.Adj w v := by
    have hsurv := (Finset.mem_filter.mp hv).1
    have hc := Finset.mem_filter.mp hsurv
    exact ⟨(Finset.mem_filter.mp hc.1).1, hc.2.1⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    have hsurv := (Finset.mem_filter.mp hv).1
    have hneq := (Finset.mem_filter.mp hv).2
    have hcurrent := (Finset.mem_filter.mp hsurv).1
    exact Finset.mem_erase.mpr ⟨hneq, (Finset.mem_filter.mp hcurrent).2⟩
  · intro j
    by_cases hj : j = i
    · subst j
      simp [update]
    · simp [update, hj, hS.2.1 j]
  · intro j v hrec
    by_cases hj : j = i
    · subst j
      have heq : w = v := by simpa only [update, Function.update_self, Option.some.injEq] using hrec
      simpa only [← heq] using hwslot
    · exact hS.2.2.1 j v (by simpa [update, hj] using hrec)
  · intro j k v u hjrec hkrec hjk
    by_cases hj : j = i
    · subst j
      have hk : k ≠ i := Ne.symm hjk
      have hv : w = v := by simpa only [update, Function.update_self, Option.some.injEq] using hjrec
      have hkold : S.recorded k = some u := by simpa [update, hk] using hkrec
      intro hadj
      exact hS.2.2.2.2 k u hkold w hwalive (by simpa only [hv] using hadj.symm)
    · by_cases hk : k = i
      · subst k
        have hu : w = u := by simpa only [update, Function.update_self, Option.some.injEq] using hkrec
        have hjold : S.recorded j = some v := by simpa [update, hj] using hjrec
        simpa only [hu] using hS.2.2.2.2 j v hjold w hwalive
      · exact hS.2.2.2.1 j k v u (by simpa [update, hj] using hjrec)
          (by simpa [update, hk] using hkrec) hjk
  · intro j u hrec v hv
    by_cases hj : j = i
    · subst j
      have hu : w = u := by simpa only [update, Function.update_self, Option.some.injEq] using hrec
      simpa only [hu] using (halive hv).2
    · exact hS.2.2.2.2 j u (by simpa [update, hj] using hrec) v (halive hv).1

theorem positive_stepWeight_exists_update (p : Parameters) (q t : ℕ) (G : Input I V)
    (S S' : State I V)
    (hpos : 0 < stepWeight p q t G S (some S')) :
    ∃ r : Noise I V, r.1 ∈ S.remaining ∧ r.2.1 ∈ domain G S r.1 ∧
      update G S r.1 r.2.1 r.2.2 = S' := by
  by_cases hp : Precheck p q t G S
  · simp only [stepWeight, hp, ite_true] at hpos
    obtain ⟨r, hr⟩ := exists_positive_of_sum_positive _ hpos
    split at hr
    · rename_i hresult
      have hvalid : r.1 ∈ S.remaining ∧ r.2.1 ∈ domain G S r.1 := by
        by_contra h
        simp only [noiseWeight, drawWeight, h, ite_false, zero_mul, lt_self_iff_false] at hr
      have hup : update G S r.1 r.2.1 r.2.2 = S' := by
        unfold performedResult at hresult
        split at hresult
        · exact Option.some.inj hresult
        · contradiction
      exact ⟨r, hvalid.1, hvalid.2, hup⟩
    · exact False.elim (lt_irrefl 0 hr)
  · simp [stepWeight, hp] at hpos

theorem positive_stepWeight_invariant (p : Parameters) (q t : ℕ) (G : Input I V)
    (S S' : State I V) (hS : StateInvariant G S)
    (hpos : 0 < stepWeight p q t G S (some S')) : StateInvariant G S' := by
  obtain ⟨r, hi, hw, hup⟩ := positive_stepWeight_exists_update p q t G S S' hpos
  rw [← hup]
  exact update_invariant G S hS r.1 r.2.1 hi hw r.2.2

theorem positive_historyWeight_invariant (p : Parameters) (q : ℕ) (G : Input I V)
    (t : ℕ) (S : State I V) (hpos : 0 < historyWeight p q G t (some S)) :
    StateInvariant G S := by
  induction t generalizing S with
  | zero =>
    simp only [historyWeight] at hpos
    split at hpos
    · rename_i h
      have heq : S = initialState := Option.some.inj h
      simpa only [heq] using initialState_invariant G
    · exact False.elim (lt_irrefl 0 hpos)
  | succ t ih =>
    simp only [historyWeight] at hpos
    obtain ⟨before, hb⟩ := exists_positive_of_sum_positive _ hpos
    have hweights := (mul_pos_iff.mp hb).resolve_right (by
      intro hneg
      exact (not_lt_of_ge (historyWeight_nonnegative p q G t before)) hneg.1)
    cases before with
    | none => simp [transitionWeight] at hweights
    | some S₀ =>
      exact positive_stepWeight_invariant p q t G S₀ S (ih S₀ hweights.1) hweights.2

theorem positive_stepWeight_card (p : Parameters) (q t : ℕ) (G : Input I V)
    (S S' : State I V) (hpos : 0 < stepWeight p q t G S (some S')) :
    S'.remaining.card + 1 = S.remaining.card := by
  obtain ⟨r, hi, _, hup⟩ := positive_stepWeight_exists_update p q t G S S' hpos
  rw [← hup]
  exact Finset.card_erase_add_one hi

theorem positive_historyWeight_card_add_time (p : Parameters) (q : ℕ) (G : Input I V)
    (t : ℕ) (S : State I V) (hpos : 0 < historyWeight p q G t (some S)) :
    S.remaining.card + t = Fintype.card I := by
  induction t generalizing S with
  | zero =>
    simp only [historyWeight] at hpos
    split at hpos
    · rename_i h
      have heq : S = initialState := Option.some.inj h
      simp [heq, initialState]
    · exact False.elim (lt_irrefl 0 hpos)
  | succ t ih =>
    simp only [historyWeight] at hpos
    obtain ⟨before, hb⟩ := exists_positive_of_sum_positive _ hpos
    have hweights := (mul_pos_iff.mp hb).resolve_right (by
      intro hneg
      exact (not_lt_of_ge (historyWeight_nonnegative p q G t before)) hneg.1)
    cases before with
    | none => simp [transitionWeight] at hweights
    | some S₀ =>
      have hc := positive_stepWeight_card p q t G S₀ S hweights.2
      have ht := ih S₀ hweights.1
      omega

theorem positive_historyWeight_card (p : Parameters) (q : ℕ) (G : Input I V)
    (t : ℕ) (S : State I V) (hpos : 0 < historyWeight p q G t (some S)) :
    S.remaining.card = Fintype.card I - t := by
  have h := positive_historyWeight_card_add_time p q G t S hpos
  omega

theorem sum_snapshotWeight_state (p : Parameters) (q t : ℕ) (G : Input I V)
    (before : Snapshot I V) (out : Option (State I V)) :
    (∑ draw, snapshotWeight p q t G before (out, draw)) =
      transitionWeight p q t G before.1 out := by
  rw [transitionWeight_eq_draw_pushforward]
  apply Finset.sum_congr rfl
  intro draw _
  simp only [snapshotWeight, eq_comm]

theorem positive_snapshotWeight_transition (p : Parameters) (q t : ℕ) (G : Input I V)
    (before out : Snapshot I V) (hp : 0 < snapshotWeight p q t G before out) :
    0 < transitionWeight p q t G before.1 out.1 := by
  rw [← sum_snapshotWeight_state p q t G before out.1]
  apply hp.trans_le
  exact Finset.single_le_sum (fun draw _ =>
    snapshotWeight_nonnegative p q t G before (out.1, draw)) (Finset.mem_univ out.2)

theorem positive_snapshotWeight_invariant (p : Parameters) (q t : ℕ) (G : Input I V)
    (S S' : State I V) (draw draw' : Option (Noise I V))
    (hS : StateInvariant G S)
    (hp : 0 < snapshotWeight p q t G (some S, draw) (some S', draw')) :
    StateInvariant G S' := by
  exact positive_stepWeight_invariant p q t G S S' hS
    (positive_snapshotWeight_transition p q t G _ _ hp)

theorem positive_snapshotWeight_card (p : Parameters) (q t : ℕ) (G : Input I V)
    (S S' : State I V) (draw draw' : Option (Noise I V))
    (hp : 0 < snapshotWeight p q t G (some S, draw) (some S', draw')) :
    S'.remaining.card + 1 = S.remaining.card := by
  exact positive_stepWeight_card p q t G S S'
    (positive_snapshotWeight_transition p q t G _ _ hp)

omit [Fintype I] in

theorem snapshotWeight_none_some (p : Parameters) (q t : ℕ) (G : Input I V)
    (S : State I V) (draw draw' : Option (Noise I V)) :
    snapshotWeight p q t G (none, draw) (some S, draw') = 0 := by
  simp [snapshotWeight, advance]

end
end Balanced.Selection.Process

end OAI

import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Entry
import OAI.Combinatorics.KMedianRecovery.Recovery.LengthPolynomial
import OAI.Combinatorics.KMedianRecovery.Recovery.Removal

namespace OAI

namespace MetricKMedianRecovery.HistoryExecution
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

theorem entry_replay (loc : D → X) (F B Q : Finset X) (v z lam eta : ℝ) (i : X)
    (s : ExecutionState D X) (hopen : s.opened = Q) (hphase : s.phase = z)
    (h : PhaseSequence.Entry loc F B Q v z lam eta i) :
    ∃ s' : ExecutionState D X, AtomicStep loc F v lam eta s s' ∧
      s'.opened = insert i Q ∧ s'.phase = z := by
  rcases h.2 with hfree | ⟨hi,W,hQ,_,tau,hbid,hpay,hdual⟩
  · refine ⟨freeUpdate loc (1-3*v) s i,AtomicStep.free s i,?_,?_⟩
    · simpa only [freeUpdate] using congrArg (insert i) hopen
    · exact hphase
  · refine ⟨regularUpdate loc (1-3*v) s i W tau,?_,?_,?_⟩
    · apply AtomicStep.regular s i W tau hi
      · simpa only [hopen] using hQ
      · simpa only [hphase] using hbid
      · simpa only [hphase] using hpay
      · simpa only [hphase] using hdual
    · simpa only [regularUpdate] using congrArg (insert i) hopen
    · exact hphase

theorem prefix_replay (loc : D → X) (F B Q : Finset X) (v z lam eta : ℝ) (H : List X)
    (h : PhaseSequence.Prefix loc F B v z lam eta Q H)
    (s : ExecutionState D X) (hopen : s.opened = Q) (hphase : s.phase = z) :
    ∃ s' : ExecutionState D X, Relation.ReflTransGen (AtomicStep loc F v lam eta) s s' ∧
      s'.opened = Q ∪ H.toFinset ∧ s'.phase = z := by
  induction h generalizing s with
  | nil Q => exact ⟨s,Relation.ReflTransGen.refl,by simpa using hopen,hphase⟩
  | @cons Q i H hi htail ih =>
    obtain ⟨s1,hstep,hs1,hz1⟩ := entry_replay loc F B Q v z lam eta i s hopen hphase hi
    obtain ⟨s2,hrest,hs2,hz2⟩ := ih s1 hs1 hz1
    refine ⟨s2,hrest.head hstep,?_,hz2⟩
    simpa only [List.toFinset_cons,Finset.insert_union,Finset.union_insert] using hs2

theorem history_replay (loc : D → X) (F B Q : Finset X) (v lam eta : ℝ) (q : ℕ)
    (T : List (List X)) (h : PhaseHistoryTransfer.History loc F B v lam eta q Q T)
    (s : ExecutionState D X) (hopen : s.opened = Q) (hphase : s.phase = (1+v^2)^q) :
    ∃ s' : ExecutionState D X, Relation.ReflTransGen (AtomicStep loc F v lam eta) s s' ∧
      s'.opened = PhaseHistoryTransfer.after Q T ∧ s'.phase = (1+v^2)^(q+T.length) := by
  induction h generalizing s with
  | nil q Q => exact ⟨s,Relation.ReflTransGen.refl,hopen,by simpa using hphase⟩
  | @cons q Q H T hhead htail ih =>
    obtain ⟨s1,hsteps,hs1,hz1⟩ := prefix_replay loc F B Q v ((1+v^2)^q) lam eta H
      hhead.1 s hopen hphase
    let s2 := phaseUpdate loc (1-3*v) (1+v^2) s1
    have hupdate : AtomicStep loc F v lam eta s1 s2 := by
      apply AtomicStep.update
      simpa only [PhaseSequence.Maximal,hs1,hz1] using hhead.2
    have hopen2 : s2.opened = Q ∪ H.toFinset := hs1
    have hphase2 : s2.phase = (1+v^2)^(q+1) := by
      change (1+v^2)*s1.phase = _
      rw [hz1,pow_succ (1+v^2) q,mul_comm]
    obtain ⟨s3,hrest,hs3,hz3⟩ := ih s2 hopen2 hphase2
    refine ⟨s3,(hsteps.tail hupdate).trans hrest,hs3,?_⟩
    simpa only [List.length_cons,Nat.add_right_comm,Nat.add_assoc] using hz3

lemma path_states {Y : Type*} {R : Y → Y → Prop} {a b : Y} (h : Relation.ReflTransGen R a b) :
    ∃ n : ℕ, ∃ state : ℕ → Y, state 0 = a ∧ state n = b ∧
      ∀ k, k < n → R (state k) (state (k+1)) := by
  induction h with
  | refl => exact ⟨0,fun _ => a,rfl,rfl,by omega⟩
  | @tail b c hab hbc ih =>
    obtain ⟨n,state,hzero,hend,hstep⟩ := ih
    let state' : ℕ → Y := fun k => if k ≤ n then state k else c
    refine ⟨n+1,state',by simpa only [state',Nat.zero_le,↓reduceIte] using hzero,?_,?_⟩
    · simp only [state',Nat.not_succ_le_self,↓reduceIte]
    · intro k hk
      by_cases hkn : k < n
      · simpa only [state',ite_eq_left hkn.le,ite_eq_left (Nat.succ_le_of_lt hkn)] using hstep k hkn
      · have he : k = n := by omega
        subst k
        simpa only [state',le_refl,↓reduceIte,Nat.not_succ_le_self,hend] using hbc

theorem valid_execution_of_history (loc : D → X) (F B : Finset X) (v lam eta : ℝ)
    (T : List (List X)) (hfar : ∀ j i, i ∈ F → 1 ≤ dist i (loc j))
    (h : PhaseHistoryTransfer.History loc F B v lam eta 0 ∅ T)
    (hterm : ∀ j, ¬activeAt loc (1-3*v) ((1+v^2)^T.length)
      (PhaseHistoryTransfer.after ∅ T) j) :
    ∃ steps : ℕ, ∃ E : ValidExecution D X steps v lam eta,
      E.location = loc ∧ E.regular = F ∧
      (E.state steps).opened = PhaseHistoryTransfer.after ∅ T ∧
      (E.state steps).phase = (1+v^2)^T.length := by
  obtain ⟨last,hpath,hopen,hphase⟩ := history_replay loc F B ∅ v lam eta 0 T h
    (initialState D X) rfl (by simp [initialState])
  have hphase' : last.phase = (1+v^2)^T.length := by simpa using hphase
  obtain ⟨steps,state,hzero,hend,hsteps⟩ := path_states hpath
  let E : ValidExecution D X steps v lam eta :=
    { location := loc
      regular := F
      far_initially := hfar
      state := state
      initial := hzero
      transition := hsteps
      terminated := by intro j; simpa only [hend,hopen,hphase'] using hterm j }
  exact ⟨steps,E,rfl,rfl,by simpa only [E,hend] using hopen,
    by simpa only [E,hend] using hphase'⟩

end MetricKMedianRecovery.HistoryExecution

namespace MetricKMedianRecovery.CountedHistoryExecution
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

def Step (loc : D → X) (F : Finset X) (v lam eta : ℝ)
    (s s' : ExecutionState D X) : Prop :=
  AtomicStep loc F v lam eta s s' ∧
  ((s.opened ∩ F).card < (s'.opened ∩ F).card →
    CertifiedRegularStep loc F v lam eta s s')

theorem entry_replay (loc : D → X) (F B Q : Finset X) (v z lam eta : ℝ) (i : X)
    (hFB : Disjoint F B) (s : ExecutionState D X) (hopen : s.opened = Q) (hphase : s.phase = z)
    (h : PhaseSequence.Entry loc F B Q v z lam eta i) :
    ∃ s' : ExecutionState D X, Step loc F v lam eta s s' ∧
      s'.opened = insert i Q ∧ s'.phase = z := by
  rcases h.2 with hfree | ⟨hi,W,hQ,_,tau,hbid,hpay,hdual⟩
  · have hiF : i ∉ F := fun hi => Finset.disjoint_left.mp hFB hi hfree
    have he : (insert i Q ∩ F) = Q ∩ F := by
      ext x
      by_cases hx : x = i
      · subst x; simp [hiF]
      · simp [hx]
    refine ⟨freeUpdate loc (1-3*v) s i,⟨AtomicStep.free s i,?_⟩,?_,?_⟩
    · intro hlt
      have hc : ¬(Q ∩ F).card < (Q ∩ F).card := by omega
      exact (hc (by simpa only [freeUpdate,hopen,he] using hlt)).elim
    · simpa only [freeUpdate] using congrArg (insert i) hopen
    · exact hphase
  · have hw : s.opened ⊆ W := by simpa only [hopen] using hQ
    have hb : admissibleBids loc (1-3*v) (1+v^2) v s.phase W i tau := by
      simpa only [hphase] using hbid
    have hp : lam-(Fintype.card D:ℝ)*eta ≤ openingPayment loc (1-3*v) s.phase W i tau := by
      simpa only [hphase] using hpay
    have hd : ∀ i₀ ∈ F, ∀ a, activeAt loc (1-3*v) s.phase W a →
        openingDual loc (1-3*v) s.phase W i₀ tau a ≤ lam := by
      simpa only [hphase] using hdual
    refine ⟨regularUpdate loc (1-3*v) s i W tau,
      ⟨AtomicStep.regular s i W tau hi hw hb hp hd,?_⟩,?_,?_⟩
    · intro _
      exact ⟨i,W,tau,hi,hw,hb,hp,hd,rfl⟩
    · simpa only [regularUpdate] using congrArg (insert i) hopen
    · exact hphase

theorem prefix_replay (loc : D → X) (F B Q : Finset X) (v z lam eta : ℝ) (H : List X)
    (hFB : Disjoint F B) (h : PhaseSequence.Prefix loc F B v z lam eta Q H)
    (s : ExecutionState D X) (hopen : s.opened = Q) (hphase : s.phase = z) :
    ∃ s' : ExecutionState D X, Relation.ReflTransGen (Step loc F v lam eta) s s' ∧
      s'.opened = Q ∪ H.toFinset ∧ s'.phase = z := by
  induction h generalizing s with
  | nil Q => exact ⟨s,Relation.ReflTransGen.refl,by simpa using hopen,hphase⟩
  | @cons Q i H hi htail ih =>
    obtain ⟨s1,hstep,hs1,hz1⟩ := entry_replay loc F B Q v z lam eta i hFB s hopen hphase hi
    obtain ⟨s2,hrest,hs2,hz2⟩ := ih s1 hs1 hz1
    refine ⟨s2,hrest.head hstep,?_,hz2⟩
    simpa only [List.toFinset_cons,Finset.insert_union,Finset.union_insert] using hs2

theorem history_replay (loc : D → X) (F B Q : Finset X) (v lam eta : ℝ) (q : ℕ)
    (T : List (List X)) (hFB : Disjoint F B) (h : PhaseHistoryTransfer.History loc F B v lam eta q Q T)
    (s : ExecutionState D X) (hopen : s.opened = Q) (hphase : s.phase = (1+v^2)^q) :
    ∃ s' : ExecutionState D X, Relation.ReflTransGen (Step loc F v lam eta) s s' ∧
      s'.opened = PhaseHistoryTransfer.after Q T ∧ s'.phase = (1+v^2)^(q+T.length) := by
  induction h generalizing s with
  | nil q Q => exact ⟨s,Relation.ReflTransGen.refl,hopen,by simpa using hphase⟩
  | @cons q Q H T hhead htail ih =>
    obtain ⟨s1,hsteps,hs1,hz1⟩ := prefix_replay loc F B Q v ((1+v^2)^q) lam eta H
      hFB hhead.1 s hopen hphase
    let s2 := phaseUpdate loc (1-3*v) (1+v^2) s1
    have hupdate : Step loc F v lam eta s1 s2 := by
      constructor
      · apply AtomicStep.update
        simpa only [PhaseSequence.Maximal,hs1,hz1] using hhead.2
      · intro hlt
        have he : s2.opened = s1.opened := rfl
        rw [he] at hlt
        exact (Nat.lt_irrefl _ hlt).elim
    have hopen2 : s2.opened = Q ∪ H.toFinset := hs1
    have hphase2 : s2.phase = (1+v^2)^(q+1) := by
      change (1+v^2)*s1.phase = _
      rw [hz1,pow_succ (1+v^2) q,mul_comm]
    obtain ⟨s3,hrest,hs3,hz3⟩ := ih s2 hopen2 hphase2
    refine ⟨s3,(hsteps.tail hupdate).trans hrest,hs3,?_⟩
    simpa only [List.length_cons,Nat.add_right_comm,Nat.add_assoc] using hz3

end MetricKMedianRecovery.CountedHistoryExecution

end OAI

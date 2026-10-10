import Mathlib
import OAI.Combinatorics.KMedianRecovery.Strictness.ValidExecutionFinalDual
import OAI.Combinatorics.KMedianRecovery.Recovery.EntryReplay

namespace OAI

namespace MetricKMedianRecovery.CountedHistoryExecution
variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]

lemma regular_card_bounds (loc : D → X) (F : Finset X) (v lam eta : ℝ)
    (s s' : ExecutionState D X) (h : AtomicStep loc F v lam eta s s') :
    (s.opened ∩ F).card ≤ (s'.opened ∩ F).card ∧
    (s'.opened ∩ F).card ≤ (s.opened ∩ F).card+1 := by
  constructor
  · apply Finset.card_le_card
    intro x hx
    exact Finset.mem_inter.mpr ⟨h.opened_subset (Finset.mem_inter.mp hx).1,
      (Finset.mem_inter.mp hx).2⟩
  · have hi (Q : Finset X) (i : X) : (insert i Q ∩ F).card ≤ (Q ∩ F).card+1 := by
      calc
        (insert i Q ∩ F).card ≤ (insert i (Q ∩ F)).card := by
          apply Finset.card_le_card
          intro x hx
          rcases Finset.mem_inter.mp hx with ⟨hx,hF⟩
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact Finset.mem_insert_self _ _
          · exact Finset.mem_insert_of_mem (Finset.mem_inter.mpr ⟨hx,hF⟩)
        _ ≤ (Q ∩ F).card+1 := Finset.card_insert_le _ _
    cases h with
    | regular i W tau hiF hW hb hp hd => exact hi s.opened i
    | free i => exact hi s.opened i
    | update hm => exact Nat.le_succ _

lemma count_increases (c : ℕ → ℕ) (n : ℕ)
    (hc : ∀ k, k < n → c k ≤ c (k+1) ∧ c (k+1) ≤ c k+1) :
    ((Finset.range n).filter (fun k => c k < c (k+1))).card+c 0 = c n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hind := ih (fun k hk => hc k (by omega))
    have hstep := hc n (by omega)
    have hn : n ∉ (Finset.range n).filter (fun k => c k < c (k+1)) := by simp
    rw [Finset.range_add_one,Finset.filter_insert]
    by_cases hinc : c n < c (n+1)
    · rw [ite_eq_left hinc,Finset.card_insert_of_notMem hn]
      omega
    · rw [ite_eq_right hinc]
      omega

theorem valid_counted_execution (loc : D → X) (F B : Finset X) (v lam eta : ℝ)
    (T : List (List X)) (hFB : Disjoint F B)
    (hfar : ∀ j i, i ∈ F → 1 ≤ dist i (loc j))
    (h : PhaseHistoryTransfer.History loc F B v lam eta 0 ∅ T)
    (hterm : ∀ j, ¬activeAt loc (1-3*v) ((1+v^2)^T.length)
      (PhaseHistoryTransfer.after ∅ T) j) :
    ∃ steps : ℕ, ∃ E : ValidExecution D X steps v lam eta, ∃ paid : Finset ℕ,
      E.location = loc ∧ E.regular = F ∧
      (E.state steps).opened = PhaseHistoryTransfer.after ∅ T ∧
      (E.state steps).phase = (1+v^2)^T.length ∧
      paid ⊆ Finset.range steps ∧
      (∀ n ∈ paid, CertifiedRegularStep E.location E.regular v lam eta
        (E.state n) (E.state (n+1))) ∧
      paid.card = (PhaseHistoryTransfer.after ∅ T ∩ F).card := by
  obtain ⟨last,hpath,hopen,hphase⟩ := history_replay loc F B ∅ v lam eta 0 T hFB h
    (initialState D X) rfl (by simp [initialState])
  have hphase' : last.phase = (1+v^2)^T.length := by simpa using hphase
  obtain ⟨steps,state,hzero,hend,hsteps⟩ := HistoryExecution.path_states hpath
  let E : ValidExecution D X steps v lam eta :=
    { location := loc
      regular := F
      far_initially := hfar
      state := state
      initial := hzero
      transition := fun n hn => (hsteps n hn).1
      terminated := by intro j; simpa only [hend,hopen,hphase'] using hterm j }
  let c : ℕ → ℕ := fun n => ((state n).opened ∩ F).card
  let paid := (Finset.range steps).filter (fun n => c n < c (n+1))
  have hc : ∀ k, k < steps → c k ≤ c (k+1) ∧ c (k+1) ≤ c k+1 := by
    intro k hk
    exact regular_card_bounds loc F v lam eta (state k) (state (k+1)) (hsteps k hk).1
  have hcard := count_increases c steps hc
  have hzeroC : c 0 = 0 := by simp [c,hzero,initialState]
  have hendC : c steps = (PhaseHistoryTransfer.after ∅ T ∩ F).card := by
    simp only [c,hend,hopen]
  refine ⟨steps,E,paid,rfl,rfl,?_,?_,Finset.filter_subset _ _,?_,?_⟩
  · simpa only [E,hend] using hopen
  · simpa only [E,hend] using hphase'
  · intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hn,hinc⟩
    exact (hsteps n (Finset.mem_range.mp hn)).2 hinc
  · simpa only [hzeroC,hendC,Nat.add_zero] using hcard

theorem history_dual_and_payment (loc : D → X) (F B : Finset X) (v lam eta : ℝ)
    (T : List (List X)) (hFB : Disjoint F B)
    (hfar : ∀ j i, i ∈ F → 1 ≤ dist i (loc j))
    (h : PhaseHistoryTransfer.History loc F B v lam eta 0 ∅ T)
    (hterm : ∀ j, ¬activeAt loc (1-3*v) ((1+v^2)^T.length)
      (PhaseHistoryTransfer.after ∅ T) j)
    (hv : 0 < v) (hv1 : v < 1/6) (hlam : 0 < lam) :
    ∃ alpha : D → ℝ,
      (∀ i ∈ F, (∑ j, max (alpha j-2*dist i (loc j)) 0) ≤ lam) ∧
      (1-3*v)*(∑ j, nearestDistance (loc j) (PhaseHistoryTransfer.after ∅ T)) +
        ((PhaseHistoryTransfer.after ∅ T ∩ F).card:ℝ)*(lam-(Fintype.card D:ℝ)*eta) ≤
          ∑ j, alpha j := by
  obtain ⟨steps,E,paid,hloc,hF,hopen,_,hpaid,hcert,hcount⟩ :=
    valid_counted_execution loc F B v lam eta T hFB hfar h hterm
  refine ⟨(E.state steps).budget,?_,?_⟩
  · intro i hi
    have hiE : i ∈ E.regular := by simpa only [hF] using hi
    simpa only [hloc] using valid_execution_final_dual v lam eta E hv hv1 hlam i hiE
  · simpa only [hloc,hopen,hcount] using valid_execution_payment v lam eta E paid hpaid hcert hv1

end MetricKMedianRecovery.CountedHistoryExecution

end OAI

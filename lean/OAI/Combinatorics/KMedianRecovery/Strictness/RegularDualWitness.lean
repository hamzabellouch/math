import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Removal

namespace OAI

namespace MetricKMedianRecovery

lemma final_dual_of_rows {D : Type*} [DecidableEq D]
    (C P : Finset D) (r : D → D → Prop) (alpha d : D → ℝ) (lam : ℝ)
    (hC : C.Nonempty) (hr : ∀ j k, r j k → ¬r k j) (hd : ∀ j, 0 ≤ d j)
    (hrows : ∀ k ∈ C, (∑ j ∈ C, dualRowTerm P r alpha d k j) ≤ lam) :
    (∑ j ∈ C, (alpha j - 2 * d j)) ≤ lam := by
  classical
  have hp := Finset.sum_le_sum (s := C) (fun k _ =>
    Finset.sum_le_sum (s := C) (fun j _ => dualRowTerm_pair P r alpha d hr hd k j))
  have hswap : (∑ x ∈ C, ∑ y ∈ C, dualRowTerm P r alpha d y x) =
      ∑ x ∈ C, ∑ y ∈ C, dualRowTerm P r alpha d x y := Finset.sum_comm
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
    ← Finset.mul_sum] at hp
  rw [hswap] at hp
  have hb := Finset.sum_le_sum (s := C) hrows
  rw [Finset.sum_const, nsmul_eq_mul] at hb
  have hc : 0 < (C.card : ℝ) := by exact_mod_cast hC.card_pos
  nlinarith only [hp, hb, hc]

namespace AtomicStep

variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
  {loc : D → X} {F : Finset X} {v lam eta : ℝ}
  {s s' : ExecutionState D X} (H : AtomicStep loc F v lam eta s s')

include H

lemma preserves_connection_bound (hv1 : v < 1 / 6) (j : D) (f : X)
    (hf : f ∈ s.opened) (hb : s.budget j ≤ (1 - 3 * v) * dist (loc j) f) :
    s'.budget j ≤ (1 - 3 * v) * dist (loc j) f := by
  classical
  have ht : 0 ≤ 1 - 3 * v := by linarith only [hv1]
  by_cases hj : activeAt loc (1 - 3 * v) s.phase s.opened j
  · have hz := (hj f hf).le
    cases H with
    | regular i W tau hi hW hbid hpay hdual =>
      simp only [regularUpdate, hj, ↓reduceIte]
      split_ifs with hw
      · exact (hbid j hw).2.2.1 f (hW hf)
      · exact hz
    | free => simpa only [freeUpdate, hj, ↓reduceIte] using hz
    | update =>
      simpa only [phaseUpdate, hj, ↓reduceIte] using
        clippedAt_le_connection loc (1 - 3 * v) ((1 + v ^ 2) * s.phase) s.opened j f hf ht
  · rw [H.inactive_frozen j hj]
    exact hb

end AtomicStep

structure RegularDualWitness {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
    (loc : D → X) (F : Finset X) (v lam : ℝ) (s s' : ExecutionState D X) where
  facility : X
  witness : Finset X
  bid : D → ℝ
  contains : s.opened ⊆ witness
  admissible : admissibleBids loc (1 - 3 * v) (1 + v ^ 2) v s.phase witness facility bid
  dual : ∀ i ∈ F, ∀ a, activeAt loc (1 - 3 * v) s.phase witness a →
    openingDual loc (1 - 3 * v) s.phase witness i bid a ≤ lam
  updated : s' = regularUpdate loc (1 - 3 * v) s facility witness bid

lemma AtomicStep.witness_cases {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
    {loc : D → X} {F : Finset X} {v lam eta : ℝ} {s s' : ExecutionState D X}
    (H : AtomicStep loc F v lam eta s s') :
    Nonempty (RegularDualWitness loc F v lam s s') ∨
      (∃ i, s' = freeUpdate loc (1 - 3 * v) s i) ∨
      s' = phaseUpdate loc (1 - 3 * v) (1 + v ^ 2) s := by
  cases H with
  | regular i W tau hi hW hbid hpay hdual =>
    exact Or.inl ⟨⟨i, W, tau, hW, hbid, hdual, rfl⟩⟩
  | free i => exact Or.inr (Or.inl ⟨i, rfl⟩)
  | update => exact Or.inr (Or.inr rfl)

namespace ValidExecution

variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
  {steps : ℕ} {v lam eta : ℝ} (E : ValidExecution D X steps v lam eta)

noncomputable def finalBudget (j : D) : ℝ := (E.state steps).budget j

def Contributor (i : X) (j : D) : Prop := 2 * dist i (E.location j) < E.finalBudget j

def precedes (j k : D) : Prop :=
  (E.removal j).val < (E.removal k).val ∨
    ((E.removal j).val = (E.removal k).val ∧ E.finalBudget j < E.finalBudget k)

lemma precedes_asymm (j k : D) (h : E.precedes j k) : ¬E.precedes k j := by
  intro h'
  rcases h with h | ⟨he, h⟩ <;> rcases h' with h' | ⟨he', h'⟩
  · omega
  · omega
  · omega
  · exact (lt_asymm h h')

lemma finalBudget_at_removal (j : D) :
    E.finalBudget j = (E.state ((E.removal j).val + 1)).budget j :=
  E.budget_frozen (Nat.succ_le_of_lt (E.removal j).isLt) le_rfl j (E.removal_inactive j)

lemma finalBudget_le_connection (hv1 : v < 1 / 6) (n : ℕ) (hn : n ≤ steps)
    (j : D) (hj : activeAt E.location (1 - 3 * v) (E.state n).phase (E.state n).opened j)
    (f : X) (hf : f ∈ (E.state n).opened) :
    E.finalBudget j ≤ (1 - 3 * v) * dist (E.location j) f := by
  have hinv : ∀ m, n ≤ m → m ≤ steps →
      (E.state m).budget j ≤ (1 - 3 * v) * dist (E.location j) f := by
    intro m hnm hm
    induction m, hnm using Nat.le_induction with
    | base => rw [E.active_budget hv1 n hn j hj]; exact (hj f hf).le
    | succ m hnm ih =>
      exact (E.transition m (by omega)).preserves_connection_bound hv1 j f
        ((E.opened_mono hnm (by omega)) hf) (ih (by omega))
  exact hinv steps hn le_rfl

def RegularFreezesAt (i : X) (n : ℕ) : Prop :=
  ∃ W : RegularDualWitness E.location E.regular v lam (E.state n) (E.state (n + 1)),
    dist i W.facility ≤ (1 + 3 * v) * (E.state n).phase / 2

lemma freezing_removes_contributor (hv : 0 < v) (hv1 : v < 1 / 6)
    (i : X) (n : ℕ) (hn : n < steps)
    (W : RegularDualWitness E.location E.regular v lam (E.state n) (E.state (n + 1)))
    (hfreeze : dist i W.facility ≤ (1 + 3 * v) * (E.state n).phase / 2)
    (j : D) (hc : E.Contributor i j) : (E.removal j).val ≤ n := by
  by_contra h
  have hbefore : n + 1 ≤ (E.removal j).val := by omega
  have ha := (E.active_iff_before_removal (n + 1) (by omega) j).mpr hbefore
  have hf : W.facility ∈ (E.state (n + 1)).opened := by
    have heq := congrArg ExecutionState.opened W.updated
    rw [heq]; exact Finset.mem_insert_self _ _
  have hbudget := E.finalBudget_le_connection hv1 (n + 1) (by omega) j ha W.facility hf
  have hz : (E.state n).phase < (1 - 3 * v) * dist (E.location j) W.facility := by
    simpa only [W.updated, regularUpdate] using ha W.facility hf
  have hm := mul_lt_mul_of_pos_left hz (show 0 < 1 + 3 * v by linarith only [hv])
  have hd := dist_nonneg (x := E.location j) (y := W.facility)
  have hc1 : (1 - 3 * v) * dist (E.location j) W.facility ≤ dist (E.location j) W.facility := by
    nlinarith only [mul_nonneg hv.le hd]
  have hc2 : (1 + 3 * v) * ((1 - 3 * v) * dist (E.location j) W.facility) ≤
      dist (E.location j) W.facility := by
    nlinarith only [mul_nonneg (sq_nonneg v) hd]
  have htri : dist (E.location j) W.facility ≤ dist i (E.location j) + dist i W.facility := by
    simpa only [dist_comm (E.location j) i] using dist_triangle (E.location j) i W.facility
  unfold Contributor at hc
  linarith only [hbudget, hfreeze, hm, hc1, hc2, htri, hc]

end ValidExecution

lemma dualRowTerm_le_bid {D X : Type*} [DecidableEq D] [PseudoMetricSpace X]
    (loc : D → X) (P : Finset D) (r : D → D → Prop) (alpha : D → ℝ)
    (t z : ℝ) (Q : Finset X) (i : X) (k j : D)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (hkP : k ∉ P) (hz : alpha k ≤ z)
    (hcap : ∀ f ∈ Q, alpha k ≤ t * dist (loc k) f)
    (hfuture : ¬r j k → alpha k ≤ clippedAt loc t z Q j) :
    dualRowTerm P r alpha (fun a => dist i (loc a)) k j ≤
      max (clippedAt loc t z Q j - dist i (loc j)) 0 := by
  classical
  unfold dualRowTerm
  simp only [hkP, false_and, ↓reduceIte]
  by_cases hr : r j k
  · rw [ite_eq_left hr]
    apply le_trans _ (le_max_left _ _)
    by_cases hj : activeAt loc t z Q j
    · rw [clippedAt_of_active loc t z Q j ht hj]
      linarith only [hz, dist_nonneg (x := i) (y := loc j),
        dist_nonneg (x := i) (y := loc k)]
    · rw [clippedAt_of_inactive loc t z Q j ht hj]
      have htri := capped_triangle_row loc t (alpha k) Q i k j ht ht1
        (inactive_nonempty loc t z Q j hj) hcap
      linarith only [htri]
  · rw [ite_eq_right hr, sub_zero]
    exact (sub_le_sub_right (hfuture hr) _).trans (le_max_left _ _)

lemma sum_dualRow_le_bidRow {D X : Type*} [Fintype D] [DecidableEq D] [PseudoMetricSpace X]
    (loc : D → X) (C P : Finset D) (r : D → D → Prop) (alpha : D → ℝ)
    (t z : ℝ) (Q : Finset X) (i : X) (k : D)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (hkP : k ∉ P) (hz : alpha k ≤ z)
    (hcap : ∀ f ∈ Q, alpha k ≤ t * dist (loc k) f)
    (hfuture : ∀ j ∈ C, ¬r j k → alpha k ≤ clippedAt loc t z Q j) :
    (∑ j ∈ C, dualRowTerm P r alpha (fun a => dist i (loc a)) k j) ≤
      bidRow loc t z Q i := by
  classical
  calc
    _ ≤ ∑ j ∈ C, max (clippedAt loc t z Q j - dist i (loc j)) 0 :=
      Finset.sum_le_sum (fun j hj => dualRowTerm_le_bid loc P r alpha t z Q i k j
        ht ht1 hkP hz hcap (hfuture j hj))
    _ ≤ bidRow loc t z Q i :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ C)
        (fun j _ _ => le_max_right _ _)

namespace ValidExecution

variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
  {steps : ℕ} {v lam eta : ℝ} (E : ValidExecution D X steps v lam eta)

lemma unfrozen_regular_budget (hv : 0 < v) (hv1 : v < 1 / 6)
    (i : X) (k : D) (hc : E.Contributor i k)
    (W : RegularDualWitness E.location E.regular v lam
      (E.state (E.removal k)) (E.state ((E.removal k).val + 1)))
    (hnf : ¬E.RegularFreezesAt i (E.removal k)) :
    E.finalBudget k = (E.state (E.removal k)).phase := by
  have hz := (E.phase_pos (E.removal k) (E.removal k).isLt.le).le
  have hnotfreeze : (1 + 3 * v) * (E.state (E.removal k)).phase / 2 <
      dist i W.facility := lt_of_not_ge (fun h => hnf ⟨W, h⟩)
  have hfar : v * (E.state (E.removal k)).phase < dist W.facility (E.location k) := by
    by_contra h
    have hnear := le_of_not_gt h
    have htri : dist i W.facility ≤ dist i (E.location k) + dist W.facility (E.location k) := by
      simpa only [dist_comm (E.location k) W.facility] using dist_triangle i (E.location k) W.facility
    have hvv : v ^ 2 ≤ v := by nlinarith only [hv, hv1]
    have hmul := mul_le_mul_of_nonneg_right hvv hz
    have hcap := E.final_cap k
    change E.finalBudget k ≤ _ at hcap
    unfold Contributor at hc
    nlinarith only [hnear, htri, hmul, hcap, hc, hnotfreeze]
  rw [E.finalBudget_at_removal k, W.updated]
  simp only [regularUpdate, E.removal_active k, ↓reduceIte]
  split_ifs with hw
  · exact (W.admissible k hw).2.2.2 hfar
  · rfl

lemma phase_removal_budget (k : D) (n : ℕ)
    (hn : (E.removal k).val = n)
    (hupdate : E.state (n + 1) = phaseUpdate E.location (1 - 3 * v) (1 + v ^ 2) (E.state n)) :
    E.finalBudget k = clippedAt E.location (1 - 3 * v) ((1 + v ^ 2) * (E.state n).phase)
      (E.state n).opened k := by
  have ha := E.removal_active k
  rw [hn] at ha
  rw [E.finalBudget_at_removal k, hn, hupdate]
  simp only [phaseUpdate, ha, ↓reduceIte]

lemma removal_row [DecidableEq D] (hv : 0 < v) (hv1 : v < 1 / 6) (hlam : 0 < lam)
    (i : X) (hi : i ∈ E.regular) (C : Finset D) (k : D) (hc : E.Contributor i k)
    (hnf : ¬E.RegularFreezesAt i (E.removal k)) :
    (∑ j ∈ C, dualRowTerm ∅ E.precedes E.finalBudget (fun a => dist i (E.location a)) k j) ≤ lam := by
  classical
  have ht : 0 ≤ 1 - 3 * v := by linarith only [hv1]
  have ht1 : 1 - 3 * v ≤ 1 := by linarith only [hv]
  let n := (E.removal k).val
  have hn : n < steps := (E.removal k).isLt
  have hopenrow : E.finalBudget k = (E.state n).phase →
      (∑ j ∈ C, dualRowTerm ∅ E.precedes E.finalBudget (fun a => dist i (E.location a)) k j) ≤ lam := by
    intro hb
    apply le_trans (sum_dualRow_le_bidRow E.location C ∅ E.precedes E.finalBudget
      (1 - 3 * v) (E.state n).phase (E.state n).opened i k ht ht1 (by simp) hb.le
      (fun f hf => hb ▸ (E.removal_active k f hf).le) ?_)
      (E.no_overbid hv hv1 hlam n hn.le i hi)
    intro j _ hnot
    have hnj : n ≤ (E.removal j).val := by
      by_contra hh
      exact hnot (Or.inl (by omega))
    have ha := (E.active_iff_before_removal n hn.le j).mpr hnj
    rw [clippedAt_of_active E.location (1 - 3 * v) (E.state n).phase (E.state n).opened j ht ha, hb]
  rcases (E.transition n hn).witness_cases with hW | hW | heq
  · obtain ⟨W⟩ := hW
    exact hopenrow (E.unfrozen_regular_budget hv hv1 i k hc W hnf)
  · obtain ⟨h, heq⟩ := hW
    apply hopenrow
    have ha : activeAt E.location (1 - 3 * v) (E.state n).phase (E.state n).opened k :=
      E.removal_active k
    rw [E.finalBudget_at_removal k, heq]
    simp only [freeUpdate, ha, ↓reduceIte]
  · have hb := E.phase_removal_budget k n rfl heq
    apply le_trans (sum_dualRow_le_bidRow E.location C ∅ E.precedes E.finalBudget
      (1 - 3 * v) ((1 + v ^ 2) * (E.state n).phase) (E.state n).opened i k ht ht1 (by simp)
      (hb ▸ clippedAt_le_phase E.location (1 - 3 * v) _ (E.state n).opened k)
      (fun f hf => hb ▸ clippedAt_le_connection E.location (1 - 3 * v) _ (E.state n).opened k f hf ht) ?_)
      (by simpa only [heq, phaseUpdate] using E.no_overbid hv hv1 hlam (n + 1) (by omega) i hi)
    intro j _ hnot
    by_cases ha : activeAt E.location (1 - 3 * v) ((1 + v ^ 2) * (E.state n).phase) (E.state n).opened j
    · rw [clippedAt_of_active E.location (1 - 3 * v) _ (E.state n).opened j ht ha]
      rw [hb]
      exact clippedAt_le_phase E.location (1 - 3 * v) _ (E.state n).opened k
    · have hnj : (E.removal j).val = n := by
        have hbefore : ¬(n + 1 ≤ (E.removal j).val) := by
          intro hh
          apply ha
          simpa only [heq, phaseUpdate] using (E.active_iff_before_removal (n + 1) (by omega) j).mpr hh
        have hnge : n ≤ (E.removal j).val := by
          by_contra hh
          exact hnot (Or.inl (by omega))
        omega
      have hjalpha : E.finalBudget k ≤ E.finalBudget j := by
        by_contra hh
        exact hnot (Or.inr ⟨hnj, lt_of_not_ge hh⟩)
      rw [E.phase_removal_budget j n hnj heq] at hjalpha
      exact hjalpha

end ValidExecution

def lastRelation {D : Type*} [DecidableEq D] (P : Finset D) (r : D → D → Prop)
    (j k : D) : Prop := j ∉ P ∧ (k ∈ P ∨ r j k)

lemma lastRelation_asymm {D : Type*} [DecidableEq D] (P : Finset D) (r : D → D → Prop)
    (hr : ∀ j k, r j k → ¬r k j) (j k : D) (h : lastRelation P r j k) :
    ¬lastRelation P r k j := by
  rintro ⟨hk, hj | hkj⟩
  · exact h.1 hj
  · rcases h.2 with hp | hjk
    · exact hk hp
    · exact hr j k hjk hkj

namespace ValidExecution

variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
  {steps : ℕ} {v lam eta : ℝ} (E : ValidExecution D X steps v lam eta)

lemma witness_active_removal (hv : 0 < v) (hv1 : v < 1 / 6)
    (i : X) (n : ℕ) (hn : n < steps)
    (W : RegularDualWitness E.location E.regular v lam (E.state n) (E.state (n + 1)))
    (hfreeze : dist i W.facility ≤ (1 + 3 * v) * (E.state n).phase / 2)
    (j : D) (hc : E.Contributor i j)
    (ha : activeAt E.location (1 - 3 * v) (E.state n).phase W.witness j) :
    (E.removal j).val = n := by
  have hu := E.freezing_removes_contributor hv hv1 i n hn W hfreeze j hc
  have hl := (E.active_iff_before_removal n hn.le j).mp
    (activeAt_of_superset E.location (1 - 3 * v) (E.state n).phase (E.state n).opened W.witness
      W.contains j ha)
  omega

lemma witness_active_budget (n : ℕ)
    (W : RegularDualWitness E.location E.regular v lam (E.state n) (E.state (n + 1)))
    (j : D) (hr : (E.removal j).val = n)
    (ha : activeAt E.location (1 - 3 * v) (E.state n).phase W.witness j) :
    E.finalBudget j = W.bid j := by
  have haq := activeAt_of_superset E.location (1 - 3 * v) (E.state n).phase
    (E.state n).opened W.witness W.contains j ha
  rw [E.finalBudget_at_removal j, hr]
  have heq := congrArg (fun s => s.budget j) W.updated
  simpa only [regularUpdate, haq, ha, ↓reduceIte] using heq

lemma witness_inactive_budget (n : ℕ)
    (W : RegularDualWitness E.location E.regular v lam (E.state n) (E.state (n + 1)))
    (j : D) (hr : (E.removal j).val = n)
    (ha : ¬activeAt E.location (1 - 3 * v) (E.state n).phase W.witness j) :
    E.finalBudget j = (E.state n).phase := by
  have haq := E.removal_active j
  rw [hr] at haq
  rw [E.finalBudget_at_removal j, hr]
  have heq := congrArg (fun s => s.budget j) W.updated
  simpa only [regularUpdate, haq, ha, ↓reduceIte] using heq

lemma contributor_dual_bound [DecidableEq D] (hv : 0 < v) (hv1 : v < 1 / 6) (hlam : 0 < lam)
    (i : X) (hi : i ∈ E.regular) (C : Finset D) (hC : C.Nonempty)
    (hcontributors : ∀ j ∈ C, E.Contributor i j) :
    (∑ j ∈ C, (E.finalBudget j - 2 * dist i (E.location j))) ≤ lam := by
  classical
  have ht : 0 ≤ 1 - 3 * v := by linarith only [hv1]
  have ht1 : 1 - 3 * v ≤ 1 := by linarith only [hv]
  by_cases hex : ∃ n, n < steps ∧ E.RegularFreezesAt i n
  · let n := Nat.find hex
    have hn : n < steps := (Nat.find_spec hex).1
    obtain ⟨W, hfreeze⟩ := (Nat.find_spec hex).2
    let P := C.filter (fun j => activeAt E.location (1 - 3 * v) (E.state n).phase W.witness j)
    have hP : ∀ j, j ∈ P ↔ j ∈ C ∧
        activeAt E.location (1 - 3 * v) (E.state n).phase W.witness j := fun _ => Finset.mem_filter
    have hPrank : ∀ j ∈ P, (E.removal j).val = n := by
      intro j hj
      exact E.witness_active_removal hv hv1 i n hn W hfreeze j
        (hcontributors j ((hP j).mp hj).1) ((hP j).mp hj).2
    have hPbudget : ∀ j ∈ P, E.finalBudget j = W.bid j := by
      intro j hj
      exact E.witness_active_budget n W j (hPrank j hj) ((hP j).mp hj).2
    have hranks : ∀ j ∈ C, (E.removal j).val ≤ n := fun j hj =>
      E.freezing_removes_contributor hv hv1 i n hn W hfreeze j (hcontributors j hj)
    apply final_dual_of_rows C P (lastRelation P E.precedes) E.finalBudget
      (fun j => dist i (E.location j)) lam hC
      (lastRelation_asymm P E.precedes E.precedes_asymm) (fun _ => dist_nonneg)
    intro k hk
    by_cases hkP : k ∈ P
    · have hak := ((hP k).mp hkP).2
      have hdual := W.dual i hi k hak
      apply le_trans _ hdual
      calc
        _ ≤ ∑ j ∈ C, if activeAt E.location (1 - 3 * v) (E.state n).phase W.witness j then
            max (W.bid j - dist i (E.location j)) 0
          else max (W.bid k - 2 * dist i (E.location j) - dist i (E.location k)) 0 := by
          apply Finset.sum_le_sum
          intro j hj
          by_cases hjP : j ∈ P
          · have haj := ((hP j).mp hjP).2
            simp only [dualRowTerm, hkP, hjP, true_and, ↓reduceIte, lastRelation,
              not_true_eq_false, false_and, sub_zero, hPbudget j hjP, haj]
            exact le_max_left _ _
          · have haj : ¬activeAt E.location (1 - 3 * v) (E.state n).phase W.witness j := by
              intro ha; exact hjP ((hP j).mpr ⟨hj, ha⟩)
            simp only [dualRowTerm, hkP, hjP, and_false, ↓reduceIte, lastRelation,
              not_false_eq_true, true_or, and_self, hPbudget k hkP, haj]
            linarith only [le_max_left (W.bid k - 2 * dist i (E.location j) - dist i (E.location k)) 0]
        _ ≤ openingDual E.location (1 - 3 * v) (E.state n).phase W.witness i W.bid k := by
          apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ C)
          intro j _ _
          split_ifs <;> exact le_max_right _ _
    · have hkn : (E.removal k).val ≤ n := hranks k hk
      rcases lt_or_eq_of_le hkn with hkn | hkn
      · have hnotfreeze : ¬E.RegularFreezesAt i (E.removal k) := by
          intro hh
          exact Nat.find_min hex hkn ⟨(E.removal k).isLt, hh⟩
        have hrow := E.removal_row hv hv1 hlam i hi C k (hcontributors k hk) hnotfreeze
        convert hrow using 1
        apply Finset.sum_congr rfl
        intro j hj
        have hrel : lastRelation P E.precedes j k ↔ E.precedes j k := by
          simp only [lastRelation, hkP, false_or]
          constructor
          · exact fun h => h.2
          · intro hjk
            refine ⟨?_, hjk⟩
            intro hjP
            have hjn := hPrank j hjP
            rcases hjk with h | ⟨h, _⟩ <;> omega
        simp only [dualRowTerm, hkP, false_and, Finset.notMem_empty, hrel, ↓reduceIte]
      · have haw : ¬activeAt E.location (1 - 3 * v) (E.state n).phase W.witness k := by
          intro hh; exact hkP ((hP k).mpr ⟨hk, hh⟩)
        have hb := E.witness_inactive_budget n W k hkn haw
        have haq := E.removal_active k
        rw [hkn] at haq
        apply le_trans (sum_dualRow_le_bidRow E.location C P (lastRelation P E.precedes) E.finalBudget
          (1 - 3 * v) (E.state n).phase (E.state n).opened i k ht ht1 hkP hb.le
          (fun f hf => hb ▸ (haq f hf).le) ?_)
          (E.no_overbid hv hv1 hlam n hn.le i hi)
        intro j hj hnot
        have hnj : n ≤ (E.removal j).val := by
          by_contra hh
          have hjn : (E.removal j).val < n := by omega
          have hjP : j ∉ P := by intro h; have he := hPrank j h; omega
          exact hnot ⟨hjP, Or.inr (Or.inl (by omega))⟩
        have haj := (E.active_iff_before_removal n hn.le j).mpr hnj
        rw [clippedAt_of_active E.location (1 - 3 * v) (E.state n).phase (E.state n).opened j ht haj, hb]
  · apply final_dual_of_rows C ∅ E.precedes E.finalBudget (fun j => dist i (E.location j)) lam
      hC E.precedes_asymm (fun _ => dist_nonneg)
    intro k hk
    exact E.removal_row hv hv1 hlam i hi C k (hcontributors k hk)
      (fun h => hex ⟨E.removal k, (E.removal k).isLt, h⟩)

end ValidExecution

end MetricKMedianRecovery

end OAI

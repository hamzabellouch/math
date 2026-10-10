import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.ExecutionState

namespace OAI

namespace MetricKMedianRecovery

namespace AtomicStep

variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
  {loc : D → X} {F : Finset X} {v lam eta : ℝ}
  {s s' : ExecutionState D X} (H : AtomicStep loc F v lam eta s s')

end AtomicStep

namespace ValidExecution

variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
  {steps : ℕ} {v lam eta : ℝ} (E : ValidExecution D X steps v lam eta)

lemma phase_pos (n : ℕ) (hn : n ≤ steps) : 0 < (E.state n).phase := by
  induction n with
  | zero => simp only [E.initial, initialState]; norm_num
  | succ n ih =>
    exact (E.transition n (by omega)).positive_phase (ih (by omega))

lemma opened_mono {a b : ℕ} (hab : a ≤ b) (hb : b ≤ steps) :
    (E.state a).opened ⊆ (E.state b).opened := by
  induction b, hab using Nat.le_induction with
  | base => exact Finset.Subset.refl _
  | succ b hab ih =>
    exact (ih (by omega)).trans ((E.transition b (by omega)).opened_subset)

lemma phase_mono {a b : ℕ} (hab : a ≤ b) (hb : b ≤ steps) :
    (E.state a).phase ≤ (E.state b).phase := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hab ih =>
    exact (ih (by omega)).trans ((E.transition b (by omega)).phase_le (E.phase_pos b (by omega)).le)

lemma active_antitone {a b : ℕ} (hab : a ≤ b) (hb : b ≤ steps) (j : D)
    (hj : activeAt E.location (1 - 3 * v) (E.state b).phase (E.state b).opened j) :
    activeAt E.location (1 - 3 * v) (E.state a).phase (E.state a).opened j := by
  intro f hf
  exact lt_of_le_of_lt (E.phase_mono hab hb) (hj f (E.opened_mono hab hb hf))

lemma inactive_persists {a b : ℕ} (hab : a ≤ b) (hb : b ≤ steps) (j : D)
    (hj : ¬activeAt E.location (1 - 3 * v) (E.state a).phase (E.state a).opened j) :
    ¬activeAt E.location (1 - 3 * v) (E.state b).phase (E.state b).opened j :=
  fun h => hj (E.active_antitone hab hb j h)

lemma budget_frozen {a b : ℕ} (hab : a ≤ b) (hb : b ≤ steps) (j : D)
    (hj : ¬activeAt E.location (1 - 3 * v) (E.state a).phase (E.state a).opened j) :
    (E.state b).budget j = (E.state a).budget j := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih =>
    exact ((E.transition b (by omega)).inactive_frozen j
      (E.inactive_persists hab (by omega) j hj)).trans (ih (by omega))

lemma initial_active (j : D) :
    activeAt E.location (1 - 3 * v) (E.state 0).phase (E.state 0).opened j := by
  rw [E.initial]
  intro f hf
  simp [initialState] at hf

lemma exists_removal (j : D) : ∃ n : ℕ, n < steps ∧
    activeAt E.location (1 - 3 * v) (E.state n).phase (E.state n).opened j ∧
    ¬activeAt E.location (1 - 3 * v) (E.state (n + 1)).phase (E.state (n + 1)).opened j := by
  classical
  have hex : ∃ n : ℕ, n ≤ steps ∧
      ¬activeAt E.location (1 - 3 * v) (E.state n).phase (E.state n).opened j :=
    ⟨steps, le_rfl, E.terminated j⟩
  let b := Nat.find hex
  have hb : b ≤ steps ∧
      ¬activeAt E.location (1 - 3 * v) (E.state b).phase (E.state b).opened j := Nat.find_spec hex
  have hbpos : 0 < b := by
    by_contra h
    have heq : b = 0 := by omega
    exact hb.2 (heq ▸ E.initial_active j)
  refine ⟨b - 1, by omega, ?_, ?_⟩
  · by_contra hnot
    exact Nat.find_min hex (show b - 1 < b by omega) ⟨by omega, hnot⟩
  · simpa only [Nat.sub_add_cancel (show 1 ≤ b by omega)] using hb.2

noncomputable def removal (j : D) : Fin steps :=
  ⟨Classical.choose (E.exists_removal j), (Classical.choose_spec (E.exists_removal j)).1⟩

lemma removal_active (j : D) :
    activeAt E.location (1 - 3 * v) (E.state (E.removal j)).phase
      (E.state (E.removal j)).opened j :=
  (Classical.choose_spec (E.exists_removal j)).2.1

lemma removal_inactive (j : D) :
    ¬activeAt E.location (1 - 3 * v) (E.state ((E.removal j).val + 1)).phase
      (E.state ((E.removal j).val + 1)).opened j :=
  (Classical.choose_spec (E.exists_removal j)).2.2

lemma active_iff_before_removal (n : ℕ) (hn : n ≤ steps) (j : D) :
    activeAt E.location (1 - 3 * v) (E.state n).phase (E.state n).opened j ↔
      n ≤ (E.removal j).val := by
  constructor
  · intro ha
    by_contra h
    exact E.removal_inactive j
      (E.active_antitone (show (E.removal j).val + 1 ≤ n by omega) hn j ha)
  · intro h
    exact E.active_antitone h (Nat.le_of_lt (E.removal j).isLt) j (E.removal_active j)

lemma final_cap (j : D) :
    (E.state steps).budget j ≤ (1 + v ^ 2) * (E.state (E.removal j)).phase := by
  rw [E.budget_frozen (Nat.succ_le_of_lt (E.removal j).isLt) le_rfl j (E.removal_inactive j)]
  exact (E.transition _ (E.removal j).isLt).active_budget_cap
    (E.phase_pos _ (E.removal j).isLt.le).le j (E.removal_active j)

lemma no_overbid (hv : 0 < v) (hv1 : v < 1 / 6) (hlam : 0 < lam)
    (n : ℕ) (hn : n ≤ steps) :
    ∀ i ∈ E.regular,
      bidRow E.location (1 - 3 * v) (E.state n).phase (E.state n).opened i ≤ lam := by
  induction n with
  | zero =>
    intro i hi
    rw [E.initial]
    have heq : bidRow E.location (1 - 3 * v) (initialState D X).phase
        (initialState D X).opened i = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      simp only [initialState, clippedAt, Finset.not_nonempty_empty, ↓reduceIte]
      exact max_eq_right (by linarith only [E.far_initially j i hi])
    rw [heq]
    exact hlam.le
  | succ n ih =>
    exact (E.transition n (by omega)).preserves_no_overbid hv hv1
      (E.phase_pos n (by omega)) hlam (ih (by omega))

end ValidExecution

def CertifiedRegularStep {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
    (loc : D → X) (F : Finset X) (v lam eta : ℝ)
    (s s' : ExecutionState D X) : Prop :=
  ∃ i : X, ∃ W : Finset X, ∃ tau : D → ℝ,
    i ∈ F ∧ s.opened ⊆ W ∧
    admissibleBids loc (1 - 3 * v) (1 + v ^ 2) v s.phase W i tau ∧
    lam - (Fintype.card D : ℝ) * eta ≤ openingPayment loc (1 - 3 * v) s.phase W i tau ∧
    (∀ i₀ ∈ F, ∀ a, activeAt loc (1 - 3 * v) s.phase W a →
      openingDual loc (1 - 3 * v) s.phase W i₀ tau a ≤ lam) ∧
    s' = regularUpdate loc (1 - 3 * v) s i W tau

noncomputable def clientSlack {D X : Type*} [PseudoMetricSpace X]
    (loc : D → X) (t : ℝ) (s : ExecutionState D X) (j : D) : ℝ :=
  s.budget j - clippedAt loc t s.phase s.opened j

noncomputable def totalSlack {D X : Type*} [Fintype D] [PseudoMetricSpace X]
    (loc : D → X) (t : ℝ) (s : ExecutionState D X) : ℝ :=
  ∑ j, clientSlack loc t s j

lemma activeAt_of_superset {D X : Type*} [PseudoMetricSpace X]
    (loc : D → X) (t z : ℝ) (Q W : Finset X) (hQW : Q ⊆ W) (j : D)
    (hj : activeAt loc t z W j) : activeAt loc t z Q j :=
  fun f hf => hj f (hQW hf)

lemma inactive_connection_le_phase {D X : Type*} [PseudoMetricSpace X]
    (loc : D → X) (t z : ℝ) (Q : Finset X) (j : D)
    (ht : 0 ≤ t) (hj : ¬activeAt loc t z Q j) :
    t * nearestDistance (loc j) Q ≤ z :=
  not_lt.mp (fun h => hj ((activeAt_iff loc t z Q j ht
    (inactive_nonempty loc t z Q j hj)).mpr h))

open Classical in
lemma regular_slack_gain {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
    (loc : D → X) (v : ℝ) (s : ExecutionState D X) (i : X) (W : Finset X) (tau : D → ℝ)
    (ht : 0 ≤ 1 - 3 * v) (hW : s.opened ⊆ W)
    (hbid : admissibleBids loc (1 - 3 * v) (1 + v ^ 2) v s.phase W i tau)
    (hcommon : ∀ j, activeAt loc (1 - 3 * v) s.phase s.opened j → s.budget j = s.phase)
    (j : D) :
    max ((if activeAt loc (1 - 3 * v) s.phase W j then tau j
      else (1 - 3 * v) * nearestDistance (loc j) W) - (1 - 3 * v) * dist i (loc j)) 0 ≤
      clientSlack loc (1 - 3 * v) (regularUpdate loc (1 - 3 * v) s i W tau) j -
        clientSlack loc (1 - 3 * v) s j := by
  classical
  let t := 1 - 3 * v
  let c := clippedAt loc t s.phase (insert i s.opened) j
  have hcz : c ≤ s.phase := clippedAt_le_phase loc t s.phase (insert i s.opened) j
  have hci : c ≤ t * dist i (loc j) := by
    simpa only [dist_comm (loc j) i] using
      clippedAt_le_connection loc t s.phase (insert i s.opened) j i (Finset.mem_insert_self _ _) ht
  have hcc : c ≤ clippedAt loc t s.phase s.opened j :=
    clippedAt_antitone_open loc t s.phase s.opened (insert i s.opened) j ht (Finset.subset_insert _ _)
  by_cases hj : activeAt loc t s.phase s.opened j
  · have hbudget := hcommon j hj
    have hclip := clippedAt_of_active loc t s.phase s.opened j ht hj
    by_cases hw : activeAt loc t s.phase W j
    · change max ((if activeAt loc t s.phase W j then tau j else _) - t * dist i (loc j)) 0 ≤ _
      rw [ite_eq_left hw]
      change _ ≤ (if activeAt loc t s.phase s.opened j then
        if activeAt loc t s.phase W j then tau j else s.phase else s.budget j) - c -
        (s.budget j - clippedAt loc t s.phase s.opened j)
      rw [ite_eq_left hj, ite_eq_left hw, hbudget, hclip]
      apply max_le
      · linarith only [hci]
      · linarith only [hcz, (hbid j hw).1]
    · have hcw := inactive_connection_le_phase loc t s.phase W j ht hw
      change max ((if activeAt loc t s.phase W j then tau j else _) - t * dist i (loc j)) 0 ≤ _
      rw [ite_eq_right hw]
      change _ ≤ (if activeAt loc t s.phase s.opened j then
        if activeAt loc t s.phase W j then tau j else s.phase else s.budget j) - c -
        (s.budget j - clippedAt loc t s.phase s.opened j)
      rw [ite_eq_left hj, ite_eq_right hw, hbudget, hclip]
      apply max_le
      · linarith only [hci, hcw]
      · linarith only [hcz]
  · have hw : ¬activeAt loc t s.phase W j := fun h =>
      hj (activeAt_of_superset loc t s.phase s.opened W hW j h)
    have hQ := inactive_nonempty loc t s.phase s.opened j hj
    have hclip := clippedAt_of_inactive loc t s.phase s.opened j ht hj
    have hcw := mul_le_mul_of_nonneg_left (nearestDistance_antitone (loc j) s.opened W hQ hW) ht
    change max ((if activeAt loc t s.phase W j then tau j else _) - t * dist i (loc j)) 0 ≤ _
    rw [ite_eq_right hw]
    change _ ≤ (if activeAt loc t s.phase s.opened j then
      if activeAt loc t s.phase W j then tau j else s.phase else s.budget j) - c -
      (s.budget j - clippedAt loc t s.phase s.opened j)
    rw [ite_eq_right hj, hclip]
    rw [hclip] at hcc
    apply max_le
    · linarith only [hcw, hci]
    · linarith only [hcc]

lemma regular_payment_gain {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
    (loc : D → X) (v : ℝ) (s : ExecutionState D X) (i : X) (W : Finset X) (tau : D → ℝ)
    (ht : 0 ≤ 1 - 3 * v) (hW : s.opened ⊆ W)
    (hbid : admissibleBids loc (1 - 3 * v) (1 + v ^ 2) v s.phase W i tau)
    (hcommon : ∀ j, activeAt loc (1 - 3 * v) s.phase s.opened j → s.budget j = s.phase) :
    openingPayment loc (1 - 3 * v) s.phase W i tau ≤
      totalSlack loc (1 - 3 * v) (regularUpdate loc (1 - 3 * v) s i W tau) -
        totalSlack loc (1 - 3 * v) s := by
  unfold openingPayment totalSlack
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum (fun j _ => regular_slack_gain loc v s i W tau ht hW hbid hcommon j)

namespace AtomicStep

variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
  {loc : D → X} {F : Finset X} {v lam eta : ℝ}
  {s s' : ExecutionState D X} (H : AtomicStep loc F v lam eta s s')

include H

lemma budget_mono (hv1 : v < 1 / 6) (hz : 0 ≤ s.phase)
    (hcommon : ∀ j, activeAt loc (1 - 3 * v) s.phase s.opened j → s.budget j = s.phase)
    (j : D) : s.budget j ≤ s'.budget j := by
  by_cases hj : activeAt loc (1 - 3 * v) s.phase s.opened j
  · rw [hcommon j hj]
    exact H.active_budget_lower hv1 hz j hj
  · exact (H.inactive_frozen j hj).ge

lemma slack_mono (hv1 : v < 1 / 6) (hz : 0 ≤ s.phase)
    (hcommon : ∀ j, activeAt loc (1 - 3 * v) s.phase s.opened j → s.budget j = s.phase)
    (j : D) : clientSlack loc (1 - 3 * v) s j ≤ clientSlack loc (1 - 3 * v) s' j := by
  have ht : 0 ≤ 1 - 3 * v := by linarith only [hv1]
  have hbudget := H.budget_mono hv1 hz hcommon j
  cases H with
  | regular =>
    exact sub_le_sub hbudget (clippedAt_antitone_open loc (1 - 3 * v) s.phase s.opened _ j ht
      (Finset.subset_insert _ _))
  | free =>
    exact sub_le_sub hbudget (clippedAt_antitone_open loc (1 - 3 * v) s.phase s.opened _ j ht
      (Finset.subset_insert _ _))
  | update =>
    by_cases hj : activeAt loc (1 - 3 * v) s.phase s.opened j
    · simp only [clientSlack, phaseUpdate, hj, ↓reduceIte, hcommon j hj,
        clippedAt_of_active loc (1 - 3 * v) s.phase s.opened j ht hj, sub_self, le_refl]
    · have hzy : s.phase ≤ (1 + v ^ 2) * s.phase := by
        nlinarith only [mul_nonneg (sq_nonneg v) hz]
      have hj' := inactive_at_later_phase loc (1 - 3 * v) s.phase ((1 + v ^ 2) * s.phase)
        s.opened j hzy hj
      simp only [clientSlack, phaseUpdate, hj, ↓reduceIte,
        clippedAt_of_inactive loc (1 - 3 * v) s.phase s.opened j ht hj,
        clippedAt_of_inactive loc (1 - 3 * v) ((1 + v ^ 2) * s.phase) s.opened j ht hj', le_refl]

lemma total_slack_mono (hv1 : v < 1 / 6) (hz : 0 ≤ s.phase)
    (hcommon : ∀ j, activeAt loc (1 - 3 * v) s.phase s.opened j → s.budget j = s.phase) :
    totalSlack loc (1 - 3 * v) s ≤ totalSlack loc (1 - 3 * v) s' :=
  Finset.sum_le_sum (fun j _ => H.slack_mono hv1 hz hcommon j)

end AtomicStep

namespace ValidExecution

variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
  {steps : ℕ} {v lam eta : ℝ} (E : ValidExecution D X steps v lam eta)

lemma active_budget (hv1 : v < 1 / 6) (n : ℕ) (hn : n ≤ steps) (j : D)
    (hj : activeAt E.location (1 - 3 * v) (E.state n).phase (E.state n).opened j) :
    (E.state n).budget j = (E.state n).phase := by
  cases n with
  | zero => rw [E.initial]; rfl
  | succ n =>
    exact (E.transition n (by omega)).surviving_budget hv1 (E.phase_pos n (by omega)) j hj

lemma total_slack_mono (hv1 : v < 1 / 6) (n : ℕ) (hn : n < steps) :
    totalSlack E.location (1 - 3 * v) (E.state n) ≤
      totalSlack E.location (1 - 3 * v) (E.state (n + 1)) :=
  (E.transition n hn).total_slack_mono hv1 (E.phase_pos n hn.le).le (E.active_budget hv1 n hn.le)

lemma regular_payment_gain (hv1 : v < 1 / 6) (n : ℕ) (hn : n < steps)
    (H : CertifiedRegularStep E.location E.regular v lam eta (E.state n) (E.state (n + 1))) :
    lam - (Fintype.card D : ℝ) * eta ≤
      totalSlack E.location (1 - 3 * v) (E.state (n + 1)) -
        totalSlack E.location (1 - 3 * v) (E.state n) := by
  obtain ⟨i, W, tau, _, hW, hbid, hpay, _, heq⟩ := H
  rw [heq]
  exact hpay.trans (MetricKMedianRecovery.regular_payment_gain E.location v (E.state n) i W tau
    (by linarith only [hv1]) hW hbid (E.active_budget hv1 n hn.le))

end ValidExecution

theorem valid_execution_payment
    {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
    {steps : ℕ} (v lam eta : ℝ) (E : ValidExecution D X steps v lam eta)
    (paid : Finset ℕ) (hpaid : paid ⊆ Finset.range steps)
    (hregular : ∀ n ∈ paid, CertifiedRegularStep E.location E.regular v lam eta
      (E.state n) (E.state (n + 1)))
    (hv1 : v < 1 / 6) :
    (1 - 3 * v) * (∑ j, nearestDistance (E.location j) (E.state steps).opened) +
      (paid.card : ℝ) * (lam - (Fintype.card D : ℝ) * eta) ≤
      ∑ j, (E.state steps).budget j := by
  classical
  let L := lam - (Fintype.card D : ℝ) * eta
  have hsum : ∀ m ≤ steps, (∑ n ∈ Finset.range m, if n ∈ paid then L else 0) ≤
      totalSlack E.location (1 - 3 * v) (E.state m) := by
    intro m hm
    induction m with
    | zero =>
      rw [E.initial]
      simp [totalSlack, clientSlack, initialState, clippedAt]
    | succ m ih =>
      have hm' : m < steps := by omega
      have hprev := ih hm'.le
      rw [Finset.sum_range_succ]
      by_cases hp : m ∈ paid
      · rw [ite_eq_left hp]
        have hg := E.regular_payment_gain hv1 m hm' (hregular m hp)
        linarith only [hprev, hg]
      · rw [ite_eq_right hp, add_zero]
        exact hprev.trans (E.total_slack_mono hv1 m hm')
  have hfilter : (Finset.range steps).filter (fun n => n ∈ paid) = paid := by
    ext n
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hpaid h, h⟩⟩
  have hpaid_sum : (∑ n ∈ Finset.range steps, if n ∈ paid then L else 0) =
      (paid.card : ℝ) * L := by
    rw [← Finset.sum_filter, hfilter, Finset.sum_const, nsmul_eq_mul]
  have hbound := hsum steps le_rfl
  rw [hpaid_sum] at hbound
  have hfinal : totalSlack E.location (1 - 3 * v) (E.state steps) =
      (∑ j, (E.state steps).budget j) -
        (1 - 3 * v) * (∑ j, nearestDistance (E.location j) (E.state steps).opened) := by
    unfold totalSlack clientSlack
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    exact clippedAt_of_inactive E.location (1 - 3 * v) (E.state steps).phase
      (E.state steps).opened j (by linarith only [hv1]) (E.terminated j)
  rw [hfinal] at hbound
  linarith only [hbound]

noncomputable def dualRowTerm {D : Type*} [DecidableEq D]
    (P : Finset D) (r : D → D → Prop) (alpha d : D → ℝ) (k j : D) : ℝ := by
  classical
  exact (if k ∈ P ∧ j ∈ P then alpha j else alpha k) - d j -
    (if r j k then d j + d k else 0)

lemma dualRowTerm_pair {D : Type*} [DecidableEq D]
    (P : Finset D) (r : D → D → Prop) (alpha d : D → ℝ)
    (hr : ∀ j k, r j k → ¬r k j) (hd : ∀ j, 0 ≤ d j) (k j : D) :
    (alpha k - 2 * d k) + (alpha j - 2 * d j) ≤
      dualRowTerm P r alpha d k j + dualRowTerm P r alpha d j k := by
  classical
  unfold dualRowTerm
  have hsym : (j ∈ P ∧ k ∈ P) ↔ (k ∈ P ∧ j ∈ P) := and_comm
  simp only [hsym]
  by_cases hp : k ∈ P ∧ j ∈ P <;> simp only [hp, true_and, ↓reduceIte]
  all_goals
    by_cases hjk : r j k
    · have hkj := hr j k hjk
      simp only [hjk, hkj, ↓reduceIte]
      linarith only
    · by_cases hkj : r k j
      · simp only [hjk, hkj, ↓reduceIte]
        linarith only
      · simp only [hjk, hkj, ↓reduceIte]
        linarith only [hd j, hd k]

end MetricKMedianRecovery

end OAI

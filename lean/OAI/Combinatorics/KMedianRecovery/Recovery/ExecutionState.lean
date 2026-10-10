import Mathlib
import OAI.Combinatorics.KMedianRecovery.Geometry.NearestDistance

namespace OAI

namespace MetricKMedianRecovery

theorem phase_update_no_overbid
    {D X : Type*} [Fintype D] [PseudoMetricSpace X]
    (loc : D → X) (F Q : Finset X) (v z lam : ℝ)
    (hv : 0 < v) (hvsmall : v < 1 / 6) (hz : 0 < z) (hlam : 0 < lam)
    (hpre : ∀ i ∈ F, bidRow loc (1 - 3 * v) z Q i ≤ lam)
    (hmaximal : ∀ i ∈ F, i ∉ Q →
      ¬etaOpenable loc F Q (1 - 3 * v) (1 + v ^ 2) v z lam 0 i) :
    ∀ i ∈ F, bidRow loc (1 - 3 * v) ((1 + v ^ 2) * z) Q i ≤ lam := by
  classical
  intro i hi
  by_contra hbad
  have hbad' : lam < bidRow loc (1 - 3 * v) ((1 + v ^ 2) * z) Q i := not_le.mp hbad
  have hF : F.Nonempty := ⟨i, hi⟩
  let M : ℝ → ℝ := fun y => F.sup' hF (fun j => bidRow loc (1 - 3 * v) y Q j)
  have hcont : Continuous M :=
    Continuous.finset_sup'_apply hF (fun j _ => continuous_bidRow loc (1 - 3 * v) Q j)
  have hMz : M z ≤ lam := Finset.sup'_le hF _ hpre
  have hMend : lam ≤ M ((1 + v ^ 2) * z) :=
    hbad'.le.trans (Finset.le_sup' (fun j => bidRow loc (1 - 3 * v) ((1 + v ^ 2) * z) Q j) hi)
  have hzK : z ≤ (1 + v ^ 2) * z := by
    nlinarith only [mul_nonneg (sq_nonneg v) hz.le]
  obtain ⟨y, hy, hMy⟩ := intermediate_value_Icc hzK hcont.continuousOn ⟨hMz, hMend⟩
  obtain ⟨j, hj, hjM⟩ := Finset.exists_mem_eq_sup' hF (fun j => bidRow loc (1 - 3 * v) y Q j)
  have hjlam : bidRow loc (1 - 3 * v) y Q j = lam := hjM.symm.trans hMy
  have hrows : ∀ j ∈ F, bidRow loc (1 - 3 * v) y Q j ≤ lam := by
    intro j hj
    have h := Finset.le_sup' (fun j => bidRow loc (1 - 3 * v) y Q j) hj
    exact h.trans_eq hMy
  have hjnot : j ∉ Q := by
    intro hjQ
    have hzero := bidRow_eq_zero_of_open loc (1 - 3 * v) y Q j hjQ
      (by linarith only [hvsmall]) (by linarith only [hv])
    linarith only [hzero, hjlam, hlam]
  exact hmaximal j hj hjnot
    (crossing_openable loc F Q v z y lam j hv hvsmall hz hy.1 hy.2 hjlam hrows)

structure ExecutionState (D X : Type*) where
  opened : Finset X
  phase : ℝ
  budget : D → ℝ

noncomputable def initialState (D X : Type*) : ExecutionState D X :=
  ⟨∅, 1, fun _ => 1⟩

noncomputable def regularUpdate {D X : Type*} [PseudoMetricSpace X] [DecidableEq X]
    (loc : D → X) (t : ℝ) (s : ExecutionState D X) (i : X) (W : Finset X)
    (tau : D → ℝ) : ExecutionState D X := by
  classical
  exact ⟨insert i s.opened, s.phase, fun j =>
    if activeAt loc t s.phase s.opened j then
      if activeAt loc t s.phase W j then tau j else s.phase
    else s.budget j⟩

noncomputable def freeUpdate {D X : Type*} [PseudoMetricSpace X] [DecidableEq X]
    (loc : D → X) (t : ℝ) (s : ExecutionState D X) (i : X) : ExecutionState D X := by
  classical
  exact ⟨insert i s.opened, s.phase, fun j =>
    if activeAt loc t s.phase s.opened j then s.phase else s.budget j⟩

noncomputable def phaseUpdate {D X : Type*} [PseudoMetricSpace X]
    (loc : D → X) (t K : ℝ) (s : ExecutionState D X) : ExecutionState D X := by
  classical
  exact ⟨s.opened, K * s.phase, fun j =>
    if activeAt loc t s.phase s.opened j then
      clippedAt loc t (K * s.phase) s.opened j else s.budget j⟩

inductive AtomicStep {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
    (loc : D → X) (F : Finset X) (v lam eta : ℝ) :
    ExecutionState D X → ExecutionState D X → Prop
  | regular (s : ExecutionState D X) (i : X) (W : Finset X) (tau : D → ℝ)
      (hi : i ∈ F) (hW : s.opened ⊆ W)
      (hbid : admissibleBids loc (1 - 3 * v) (1 + v ^ 2) v s.phase W i tau)
      (hpayment : lam - (Fintype.card D : ℝ) * eta ≤
        openingPayment loc (1 - 3 * v) s.phase W i tau)
      (hdual : ∀ i₀ ∈ F, ∀ a, activeAt loc (1 - 3 * v) s.phase W a →
        openingDual loc (1 - 3 * v) s.phase W i₀ tau a ≤ lam) :
      AtomicStep loc F v lam eta s (regularUpdate loc (1 - 3 * v) s i W tau)
  | free (s : ExecutionState D X) (i : X) :
      AtomicStep loc F v lam eta s (freeUpdate loc (1 - 3 * v) s i)
  | update (s : ExecutionState D X)
      (hmaximal : ∀ i ∈ F, i ∉ s.opened →
        ¬etaOpenable loc F s.opened (1 - 3 * v) (1 + v ^ 2) v s.phase lam 0 i) :
      AtomicStep loc F v lam eta s (phaseUpdate loc (1 - 3 * v) (1 + v ^ 2) s)

structure ValidExecution (D X : Type*) [Fintype D] [PseudoMetricSpace X]
    [DecidableEq X] (steps : ℕ) (v lam eta : ℝ) where
  location : D → X
  regular : Finset X
  far_initially : ∀ j i, i ∈ regular → 1 ≤ dist i (location j)
  state : ℕ → ExecutionState D X
  initial : state 0 = initialState D X
  transition : ∀ n, n < steps → AtomicStep location regular v lam eta (state n) (state (n + 1))
  terminated : ∀ j, ¬activeAt location (1 - 3 * v) (state steps).phase (state steps).opened j

namespace AtomicStep

variable {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
  {loc : D → X} {F : Finset X} {v lam eta : ℝ}
  {s s' : ExecutionState D X} (H : AtomicStep loc F v lam eta s s')

include H

lemma opened_subset : s.opened ⊆ s'.opened := by
  cases H <;> simp only [regularUpdate, freeUpdate, phaseUpdate] <;> simp

lemma phase_le (hz : 0 ≤ s.phase) : s.phase ≤ s'.phase := by
  cases H with
  | regular => exact le_rfl
  | free => exact le_rfl
  | update =>
    change s.phase ≤ (1 + v ^ 2) * s.phase
    nlinarith only [mul_nonneg (sq_nonneg v) hz]

lemma positive_phase (hz : 0 < s.phase) : 0 < s'.phase :=
  hz.trans_le (H.phase_le hz.le)

lemma active_before (hz : 0 ≤ s.phase) (j : D)
    (hj : activeAt loc (1 - 3 * v) s'.phase s'.opened j) :
    activeAt loc (1 - 3 * v) s.phase s.opened j := by
  intro f hf
  exact lt_of_le_of_lt (H.phase_le hz) (hj f (H.opened_subset hf))

lemma inactive_frozen (j : D) (hj : ¬activeAt loc (1 - 3 * v) s.phase s.opened j) :
    s'.budget j = s.budget j := by
  cases H <;> simp only [regularUpdate, freeUpdate, phaseUpdate, hj, ↓reduceIte]

lemma active_budget_cap (hz : 0 ≤ s.phase) (j : D)
    (hj : activeAt loc (1 - 3 * v) s.phase s.opened j) :
    s'.budget j ≤ (1 + v ^ 2) * s.phase := by
  have hzK : s.phase ≤ (1 + v ^ 2) * s.phase := by
    nlinarith only [mul_nonneg (sq_nonneg v) hz]
  cases H with
  | regular i W tau hi hW hbid hpayment hdual =>
    simp only [regularUpdate, hj, ↓reduceIte]
    split_ifs with hw
    · exact (hbid j hw).2.1
    · exact hzK
  | free => simpa only [freeUpdate, hj, ↓reduceIte] using hzK
  | update =>
    simpa only [phaseUpdate, hj, ↓reduceIte] using
      clippedAt_le_phase loc (1 - 3 * v) ((1 + v ^ 2) * s.phase) s.opened j

lemma active_budget_lower (hv1 : v < 1 / 6) (hz : 0 ≤ s.phase)
    (j : D) (hj : activeAt loc (1 - 3 * v) s.phase s.opened j) :
    s.phase ≤ s'.budget j := by
  have ht : 0 ≤ 1 - 3 * v := by linarith only [hv1]
  cases H with
  | regular i W tau hi hW hbid hpayment hdual =>
    simp only [regularUpdate, hj, ↓reduceIte]
    split_ifs with hw
    · exact (hbid j hw).1
    · exact le_rfl
  | free => simp only [freeUpdate, hj, ↓reduceIte, le_refl]
  | update =>
    simp only [phaseUpdate, hj, ↓reduceIte]
    calc
      s.phase = clippedAt loc (1 - 3 * v) s.phase s.opened j :=
        (clippedAt_of_active loc (1 - 3 * v) s.phase s.opened j ht hj).symm
      _ ≤ clippedAt loc (1 - 3 * v) ((1 + v ^ 2) * s.phase) s.opened j := by
        apply clippedAt_mono_phase
        nlinarith only [mul_nonneg (sq_nonneg v) hz]

lemma surviving_budget (hv1 : v < 1 / 6) (hz : 0 < s.phase)
    (j : D) (hj : activeAt loc (1 - 3 * v) s'.phase s'.opened j) :
    s'.budget j = s'.phase := by
  have hjold := H.active_before hz.le j hj
  have ht : 0 ≤ 1 - 3 * v := by linarith only [hv1]
  have htv : (1 - 3 * v) * v < 1 := by
    have hv1' : v < 1 := by linarith only [hv1]
    nlinarith only [hv1', sq_nonneg v]
  cases H with
  | regular i W tau hi hW hbid hpayment hdual =>
    simp only [regularUpdate, hjold, ↓reduceIte]
    split_ifs with hw
    · have hfar : v * s.phase < dist i (loc j) := by
        by_contra hh
        have hd := le_of_not_gt hh
        have hc := hj i (by simp [regularUpdate])
        change s.phase < (1 - 3 * v) * dist (loc j) i at hc
        rw [dist_comm (loc j) i] at hc
        have hmul := mul_le_mul_of_nonneg_left hd ht
        have htvs := mul_lt_mul_of_pos_right htv hz
        nlinarith only [hc, hmul, htvs]
      exact (hbid j hw).2.2.2 hfar
    · rfl
  | free => simp only [freeUpdate, hjold, ↓reduceIte]
  | update =>
    simp only [phaseUpdate, hjold, ↓reduceIte]
    exact clippedAt_of_active loc (1 - 3 * v) ((1 + v ^ 2) * s.phase) s.opened j ht hj

lemma removal_connection_cap (hv1 : v < 1 / 6) (hz : 0 ≤ s.phase)
    (j : D)
    (hj' : ¬activeAt loc (1 - 3 * v) s'.phase s'.opened j) :
    ∃ f ∈ s'.opened, (1 - 3 * v) * dist (loc j) f ≤ (1 + v ^ 2) * s.phase := by
  have ht : 0 ≤ 1 - 3 * v := by linarith only [hv1]
  have hne := inactive_nonempty loc (1 - 3 * v) s'.phase s'.opened j hj'
  have hc : (1 - 3 * v) * nearestDistance (loc j) s'.opened ≤ s'.phase :=
    not_lt.mp (fun hh => hj' ((activeAt_iff loc _ _ _ j ht hne).mpr hh))
  obtain ⟨f, hf, heq⟩ := nearestDistance_attained (loc j) s'.opened hne
  refine ⟨f, hf, ?_⟩
  rw [heq] at hc
  have hphase : s'.phase ≤ (1 + v ^ 2) * s.phase := by
    cases H with
    | regular => change s.phase ≤ _; nlinarith only [mul_nonneg (sq_nonneg v) hz]
    | free => change s.phase ≤ _; nlinarith only [mul_nonneg (sq_nonneg v) hz]
    | update => exact le_rfl
  exact hc.trans hphase

lemma preserves_no_overbid (hv : 0 < v) (hv1 : v < 1 / 6) (hz : 0 < s.phase)
    (hlam : 0 < lam)
    (hpre : ∀ i ∈ F, bidRow loc (1 - 3 * v) s.phase s.opened i ≤ lam) :
    ∀ i ∈ F, bidRow loc (1 - 3 * v) s'.phase s'.opened i ≤ lam := by
  have ht : 0 ≤ 1 - 3 * v := by linarith only [hv1]
  cases H with
  | regular =>
    intro i hi
    exact (bidRow_antitone_open _ _ _ _ _ _ ht (Finset.subset_insert _ _)).trans (hpre i hi)
  | free =>
    intro i hi
    exact (bidRow_antitone_open _ _ _ _ _ _ ht (Finset.subset_insert _ _)).trans (hpre i hi)
  | update hmaximal =>
    exact phase_update_no_overbid loc F s.opened v s.phase lam hv hv1 hz hlam hpre hmaximal

end AtomicStep
end MetricKMedianRecovery

end OAI

import OAI.Probability.Localization.Rewards
import OAI.Probability.Localization.CountableIntegrals
import OAI.Probability.Localization.EntropyChain

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

namespace FiniteEntropy

noncomputable def rewardStep {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n)
    (r : State n → Letter n → ℝ) (N : ℕ) (z : Coordinate n) : ℝ :=
  let s := state P Q (run P Q N z)
  r s (attemptLetter (ProbabilityTheory.cond P s.event) s.cell z)

lemma reward_only_none {n : ℕ} (r : State n → Letter n → ℝ)
    (hr : ∀ s R,r s (some R) = 0) (s : State n) (a : Letter n) :
    r s a = if a = none then r s none else 0 := by
  cases a <;> simp [hr]

lemma integrable_fixed_reward {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n))
    [IsFiniteMeasure P] (r : State n → Letter n → ℝ) (hr : ∀ s R,r s (some R) = 0)
    (s : State n) :
    Integrable (fun z => r s (attemptLetter (ProbabilityTheory.cond P s.event) s.cell z)) P := by
  classical
  have he : (fun z => r s (attemptLetter (ProbabilityTheory.cond P s.event) s.cell z)) =
      {z | attemptLetter (ProbabilityTheory.cond P s.event) s.cell z = none}.indicator (fun _ => r s none) := by
    funext z
    rw [reward_only_none r hr,Set.indicator_apply]
    rfl
  rw [he]
  exact (integrable_const _).indicator ((measurable_attemptLetter hn _ _) (measurableSet_singleton none))

lemma integral_fixed_reward_event {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n))
    [IsFiniteMeasure P] (r : State n → Letter n → ℝ) (hr : ∀ s R,r s (some R) = 0)
    (s : State n) (hmeas : MeasurableSet s.event) (hsub : s.event ⊆ cellSet s.cell)
    (hp : P s.event ≠ 0) :
    (∫ z in s.event,r s (attemptLetter (ProbabilityTheory.cond P s.event) s.cell z) ∂P) =
      (P s.event).toReal * (complementMass P s * r s none) := by
  classical
  let B := residual (ProbabilityTheory.cond P s.event) s.cell
  have hB : MeasurableSet B := measurableSet_residual _ _
  have he : ∀ z ∈ s.event,r s (attemptLetter (ProbabilityTheory.cond P s.event) s.cell z) =
      B.indicator (fun _ => r s none) z := by
    intro z hz
    rw [reward_only_none r hr,Set.indicator_apply]
    have hh : attemptLetter (ProbabilityTheory.cond P s.event) s.cell z = none ↔ z ∈ B :=
      attemptLetter_eq_iff hn _ _ (hsub hz) none
    exact if_congr hh rfl rfl
  rw [setIntegral_congr_fun hmeas he,integral_indicator hB,Measure.restrict_restrict hB,
    Set.inter_comm B s.event,integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul,
    cond_event_mul P hmeas hp]
  exact mul_assoc _ _ _

lemma exists_run_fiber_root {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n)
    (hroot : ∀ᵐ z ∂P,z ∈ cellSet Q) (N : ℕ) (h : Log n)
    (hp : P {z | run P Q N z = h} ≠ 0) :
    ∃ z,z ∈ cellSet Q ∧ run P Q N z = h := by
  have he : ({z | run P Q N z = h} ∩ cellSet Q : Set (Coordinate n)) =ᵐ[P] {z | run P Q N z = h} := by
    filter_upwards [hroot] with z hz
    change (run P Q N z = h ∧ z ∈ cellSet Q) = (run P Q N z = h)
    simp only [hz,and_true]
  have hp' : P ({z | run P Q N z = h} ∩ cellSet Q) ≠ 0 := by
    rw [measure_congr he]; exact hp
  obtain ⟨z,hz⟩ := nonempty_of_measure_ne_zero hp'
  exact ⟨z,hz.2,hz.1⟩

lemma rewardStep_fiber_integrable {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n))
    [IsFiniteMeasure P] (Q : Cell n) (r : State n → Letter n → ℝ)
    (hr : ∀ s R,r s (some R) = 0) (N : ℕ) (h : Log n) :
    IntegrableOn (rewardStep P Q r N) {z | run P Q N z = h} P := by
  apply (integrable_fixed_reward hn P r hr (state P Q h)).integrableOn.congr_fun
    (s := {z | run P Q N z = h})
  · intro z hz
    change run P Q N z = h at hz
    simp only [rewardStep,hz]
  · exact (measurable_run hn P Q N) (measurableSet_singleton h)

lemma rewardStep_fiber_integral {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n))
    [IsFiniteMeasure P] (Q : Cell n) (hroot : ∀ᵐ z ∂P,z ∈ cellSet Q)
    (r : State n → Letter n → ℝ) (hr : ∀ s R,r s (some R) = 0) (N : ℕ) (h : Log n) :
    (∫ z in {z | run P Q N z = h},rewardStep P Q r N z ∂P) =
      (P {z | run P Q N z = h}).toReal * (complementMass P (state P Q h) * r (state P Q h) none) := by
  by_cases hp : P {z | run P Q N z = h} = 0
  · rw [Measure.restrict_eq_zero.mpr hp,hp,integral_zero_measure,ENNReal.toReal_zero,zero_mul]
  obtain ⟨z,hz,hzh⟩ := exists_run_fiber_root P Q hroot N h hp
  have he : {w | run P Q N w = h} =ᵐ[P] (state P Q h).event := by
    simpa only [hzh] using run_fiber_ae_event hn P Q hroot N hz
  have hpe : P (state P Q h).event ≠ 0 := by rwa [← measure_congr he]
  have hm : MeasurableSet {z | run P Q N z = h} := (measurable_run hn P Q N) (measurableSet_singleton h)
  rw [setIntegral_congr_fun hm
    (g := fun z => r (state P Q h) (attemptLetter (ProbabilityTheory.cond P (state P Q h).event) (state P Q h).cell z))
    (fun w hw => by change run P Q N w = h at hw; simp only [rewardStep,hw])]
  rw [Measure.restrict_congr_set he,measure_congr he]
  exact integral_fixed_reward_event hn P r hr _ (state_event_measurable P Q h)
    (state_event_subset_cell P Q h) hpe

lemma integrable_activeIndicator {n : ℕ} (P : Measure (Coordinate n)) [IsFiniteMeasure P]
    (Q : Cell n) (hn : 0 < n) (N : ℕ) : Integrable (activeIndicator P Q N) P := by
  have he : activeIndicator P Q N = {z | (state P Q (run P Q N z)).stopped = false}.indicator (fun _ => (1:ℝ)) := by
    funext z
    simp only [activeIndicator,Set.indicator_apply,Set.mem_ofPred_eq]
    by_cases hs : (state P Q (run P Q N z)).stopped = true
    · simp [hs]
    · simp [Bool.eq_false_iff.mpr hs]
  rw [he]
  exact (integrable_const _).indicator
    (((measurable_of_countable (fun h : Log n => (state P Q h).stopped)).comp
      (measurable_run hn P Q N)) (measurableSet_singleton false))

lemma rewardStep_integral_bound {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n))
    [IsFiniteMeasure P] (Q : Cell n) (hroot : ∀ᵐ z ∂P,z ∈ cellSet Q)
    (r : State n → Letter n → ℝ) (hr0 : ∀ s a,0 ≤ r s a)
    (hr : ∀ s R,r s (some R) = 0) (b : ℝ)
    (hb : ∀ s, complementMass P s * r s none ≤ b*(if s.stopped then 0 else 1)) (N : ℕ) :
    Integrable (rewardStep P Q r N) P ∧
      (∫ z,rewardStep P Q r N z ∂P) ≤ b*(∫ z,activeIndicator P Q N z ∂P) := by
  have hb' (h : Log n) : (∫ z in {z | run P Q N z = h},rewardStep P Q r N z ∂P) ≤
      ∫ z in {z | run P Q N z = h},b*activeIndicator P Q N z ∂P := by
    rw [rewardStep_fiber_integral hn P Q hroot r hr N h]
    change _ ≤ ∫ z in {z | run P Q N z = h},
      (fun h : Log n => b*(if (state P Q h).stopped then 0 else 1)) (run P Q N z) ∂P
    rw [integral_comp_fiber P (run P Q N)
      (fun h : Log n => b*(if (state P Q h).stopped then 0 else 1)) h
      ((measurable_run hn P Q N) (measurableSet_singleton h))]
    exact mul_le_mul_of_nonneg_left (hb _) ENNReal.toReal_nonneg
  have hi := partition_integral_bound P (run P Q N) (measurable_run hn P Q N)
    (fun z => hr0 _ _) (rewardStep_fiber_integrable hn P Q r hr N)
    ((integrable_activeIndicator P Q hn N).const_mul b) hb'
  rw [integral_const_mul] at hi
  exact hi

lemma complementReward_some {n : ℕ} (P : Measure (Coordinate n)) (s : State n) (R : Cell n) :
    complementReward P s (some R) = 0 := by simp [complementReward]

lemma continuingReward_some {n : ℕ} (P : Measure (Coordinate n)) (s : State n) (R : Cell n) :
    continuingReward P s (some R) = 0 := by simp [continuingReward]

lemma complementStep_bound {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n))
    [IsFiniteMeasure P] (Q : Cell n) (hroot : ∀ᵐ z ∂P,z ∈ cellSet Q) (N : ℕ) :
    Integrable (rewardStep P Q (complementReward P) N) P ∧
      (∫ z,rewardStep P Q (complementReward P) N z ∂P) ≤
        (1/Real.exp 1)*(∫ z,activeIndicator P Q N z ∂P) := by
  apply rewardStep_integral_bound hn P Q hroot _ (complementReward_nonneg P) (complementReward_some P)
  intro s
  by_cases hs : s.stopped = true
  · simp [complementReward,hs]
  · simpa [complementReward,hs] using neg_log_mul_le (complementMass_nonneg P s)

lemma continuingStep_bound {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n))
    [IsFiniteMeasure P] (Q : Cell n) (hroot : ∀ᵐ z ∂P,z ∈ cellSet Q) (N : ℕ) :
    Integrable (rewardStep P Q (continuingReward P) N) P ∧
      (∫ z,rewardStep P Q (continuingReward P) N z ∂P) ≤
        (1/2:ℝ)*(∫ z,activeIndicator P Q N z ∂P) := by
  apply rewardStep_integral_bound hn P Q hroot _ (continuingReward_nonneg P) (continuingReward_some P)
  intro s
  by_cases hs : s.stopped = true
  · simp [continuingReward,hs]
  · by_cases hq : complementMass P s < 1/2
    · simpa only [continuingReward,hs,Bool.false_eq_true,ite_false,true_and,ite_eq_left hq,mul_one] using hq.le
    · simp only [continuingReward,hs,Bool.false_eq_true,ite_false,true_and,ite_eq_right hq,mul_zero,mul_one]
      norm_num

end FiniteEntropy

end RepeatedLocalization

end OAI

import OAI.Probability.Localization.ConditionalLaws

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

namespace FiniteEntropy

noncomputable def complementMass {n : ℕ} (P : Measure (Coordinate n)) (s : State n) : ℝ :=
  ((ProbabilityTheory.cond P s.event) (residual (ProbabilityTheory.cond P s.event) s.cell)).toReal

noncomputable def complementReward {n : ℕ} (P : Measure (Coordinate n)) (s : State n) (a : Letter n) : ℝ :=
  if s.stopped then 0 else if a = none then -Real.log (complementMass P s) else 0

noncomputable def continuingReward {n : ℕ} (P : Measure (Coordinate n)) (s : State n) (a : Letter n) : ℝ :=
  if s.stopped then 0 else if a = none ∧ complementMass P s < 1/2 then 1 else 0

noncomputable def accumulate {n : ℕ} (P : Measure (Coordinate n)) (r : State n → Letter n → ℝ) :
    State n → Log n → ℝ
  | _,[] => 0
  | s,a::h => r s a + accumulate P r (update P s a) h

noncomputable def rewardLog {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n)
    (r : State n → Letter n → ℝ) (h : Log n) : ℝ := accumulate P r ⟨Q,cellSet Q,false⟩ h

noncomputable def complementTotal {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (N : ℕ) (z : Coordinate n) : ℝ :=
  rewardLog P Q (complementReward P) (run P Q N z)

noncomputable def continuingTotal {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (N : ℕ) (z : Coordinate n) : ℝ :=
  rewardLog P Q (continuingReward P) (run P Q N z)

noncomputable def truncatedDepth {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (N : ℕ) (z : Coordinate n) : ℕ :=
  (state P Q (run P Q N z)).cell.1-Q.1

noncomputable def truncatedAttempts {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (N : ℕ) (z : Coordinate n) : ℕ :=
  (run P Q N z).length

noncomputable def activeIndicator {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (N : ℕ) (z : Coordinate n) : ℝ :=
  if (state P Q (run P Q N z)).stopped then 0 else 1

lemma accumulate_append {n : ℕ} (P : Measure (Coordinate n)) (r : State n → Letter n → ℝ)
    (s : State n) (h k : Log n) :
    accumulate P r s (h++k) = accumulate P r s h + accumulate P r (h.foldl (update P) s) k := by
  induction h generalizing s with
  | nil => simp [accumulate]
  | cons a h ih => simp only [List.cons_append,accumulate,List.foldl_cons,ih]; ring

lemma rewardLog_append {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n)
    (r : State n → Letter n → ℝ) (h : Log n) (a : Letter n) :
    rewardLog P Q r (h++[a]) = rewardLog P Q r h + r (state P Q h) a := by
  simp only [rewardLog,accumulate_append,accumulate,add_zero,state]

lemma complementMass_nonneg {n : ℕ} (P : Measure (Coordinate n)) (s : State n) :
    0 ≤ complementMass P s := ENNReal.toReal_nonneg

lemma complementMass_le_one {n : ℕ} (P : Measure (Coordinate n)) [IsFiniteMeasure P] (s : State n) :
    complementMass P s ≤ 1 := by
  by_cases hp : P s.event = 0
  · simp [complementMass,ProbabilityTheory.cond_eq_zero_of_meas_eq_zero hp]
  · let := ProbabilityTheory.cond_isProbabilityMeasure (μ := P) hp
    exact (ENNReal.toReal_mono ENNReal.one_ne_top prob_le_one).trans_eq ENNReal.toReal_one

lemma complementReward_nonneg {n : ℕ} (P : Measure (Coordinate n)) [IsFiniteMeasure P]
    (s : State n) (a : Letter n) : 0 ≤ complementReward P s a := by
  unfold complementReward
  split
  · exact le_rfl
  · split
    · exact neg_nonneg.mpr (Real.log_nonpos (complementMass_nonneg P s) (complementMass_le_one P s))
    · exact le_rfl

lemma continuingReward_nonneg {n : ℕ} (P : Measure (Coordinate n)) (s : State n) (a : Letter n) :
    0 ≤ continuingReward P s a := by unfold continuingReward; split_ifs <;> norm_num

lemma accumulate_nonneg {n : ℕ} (P : Measure (Coordinate n)) (r : State n → Letter n → ℝ)
    (hr : ∀ s a,0 ≤ r s a) (s : State n) (h : Log n) : 0 ≤ accumulate P r s h := by
  induction h generalizing s with
  | nil => exact le_rfl
  | cons a h ih => exact add_nonneg (hr s a) (ih _)

lemma rewardLog_nonneg {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n)
    (r : State n → Letter n → ℝ) (hr : ∀ s a,0 ≤ r s a) (h : Log n) : 0 ≤ rewardLog P Q r h :=
  accumulate_nonneg P r hr _ h

lemma neg_log_mul_le {q : ℝ} (hq : 0 ≤ q) : q * (-Real.log q) ≤ 1/Real.exp 1 := by
  rcases hq.eq_or_lt with rfl | hq
  · simp only [Real.log_zero,neg_zero,mul_zero]; positivity
  · have hl := Real.log_le_sub_one_of_pos (div_pos (Real.exp_pos (-1)) hq)
    rw [Real.log_div (Real.exp_ne_zero _) hq.ne',Real.log_exp] at hl
    have hh := mul_le_mul_of_nonneg_left hl hq.le
    have he : q * (Real.exp (-1) / q - 1) = Real.exp (-1)-q := by field_simp
    rw [he,Real.exp_neg,← one_div] at hh
    nlinarith

lemma threshold_pos (n h : ℕ) : 0 < threshold n h := Real.rpow_pos_of_pos (by norm_num) _

lemma log_threshold (n h : ℕ) : Real.log (threshold n h) = -(n:ℝ)*(h:ℝ)/2*Real.log 2 := by
  exact Real.log_rpow (by norm_num) _

lemma positive_event_descendant {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (h : Log n)
    (hp : P (state P Q h).event ≠ 0) : Descendant Q (state P Q h).cell := by
  obtain ⟨z,hz⟩ := nonempty_of_measure_ne_zero hp
  exact state_descendant_of_mem P Q h hz

lemma state_event_append_subset {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (h : Log n) (a : Letter n) :
    (state P Q (h++[a])).event ⊆ (state P Q h).event := by
  rw [state_append]
  unfold update
  split
  · exact Subset.rfl
  · exact Set.inter_subset_left

lemma cond_event_mul {α : Type*} [MeasurableSpace α] (P : Measure α) [IsFiniteMeasure P]
    {E B : Set α} (hE : MeasurableSet E) (hp : P E ≠ 0) :
    (P (E∩B)).toReal = (P E).toReal * ((ProbabilityTheory.cond P E) B).toReal := by
  rw [ProbabilityTheory.cond_apply hE,ENNReal.toReal_mul,ENNReal.toReal_inv]
  have hp' : (P E).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hp,measure_ne_top _ _⟩
  exact (mul_inv_cancel_left₀ hp' _).symm

lemma path_label_surprisal {n : ℕ} (P : Measure (Coordinate n)) [IsProbabilityMeasure P]
    (Q : Cell n) (hroot : P (cellSet Q) = 1) (h : Log n) (hp : P (state P Q h).event ≠ 0) :
    -Real.log (P (state P Q h).event).toReal ≤
      ((n:ℝ)*Real.log 2/2)*((state P Q h).cell.1-Q.1 : ℕ) + rewardLog P Q (complementReward P) h := by
  classical
  induction h using List.reverseRecOn with
  | nil => simp only [state_nil,hroot,ENNReal.toReal_one,Real.log_one,neg_zero,Nat.sub_self,
      Nat.cast_zero,mul_zero,rewardLog,accumulate,add_zero,le_refl]
  | append_singleton h a ih =>
    have hp0 : P (state P Q h).event ≠ 0 := by
      intro he
      exact hp (measure_mono_null (state_event_append_subset P Q h a) he)
    have hih := ih hp0
    have ppos : 0 < (P (state P Q h).event).toReal := ENNReal.toReal_pos hp0 (measure_ne_top _ _)
    have hdesc := positive_event_descendant P Q h hp0
    rw [state_append,rewardLog_append]
    by_cases hs : (state P Q h).stopped = true
    · simpa only [update,hs,ite_true,complementReward,add_zero] using hih
    · cases a with
      | none =>
        have he : (P (update P (state P Q h) none).event).toReal =
            (P (state P Q h).event).toReal * complementMass P (state P Q h) := by
          simp only [update,hs,branch,complementMass]
          exact cond_event_mul P (state_event_measurable P Q h) hp0
        have hepos : 0 < (P (update P (state P Q h) none).event).toReal :=
          ENNReal.toReal_pos (by simpa only [state_append] using hp) (measure_ne_top _ _)
        have hqpos : 0 < complementMass P (state P Q h) := by rw [he] at hepos; nlinarith [complementMass_nonneg P (state P Q h)]
        rw [he,Real.log_mul ppos.ne' hqpos.ne']
        simp only [update,hs,Bool.false_eq_true,ite_false,Option.getD_none,complementReward,ite_true]
        linarith
      | some R =>
        have hR : FirstHeavy (ProbabilityTheory.cond P (state P Q h).event) (state P Q h).cell R := by
          by_contra hR
          simp [state_append,update,hs,branch,hR] at hp
        have he : (P (update P (state P Q h) (some R)).event).toReal =
            (P (state P Q h).event).toReal * ((ProbabilityTheory.cond P (state P Q h).event) (cellSet R)).toReal := by
          simp only [update,hs,branch,ite_eq_left hR]
          exact cond_event_mul P (state_event_measurable P Q h) hp0
        have hmpos := (threshold_pos n (R.1-(state P Q h).cell.1)).trans hR.1.2.2
        have hl := Real.log_le_log (threshold_pos n (R.1-(state P Q h).cell.1)) hR.1.2.2.le
        rw [log_threshold] at hl
        have hdepth : R.1-Q.1 = ((state P Q h).cell.1-Q.1)+(R.1-(state P Q h).cell.1) := by
          have := hdesc.1
          have := hR.1.1.1
          omega
        rw [he,Real.log_mul ppos.ne' hmpos.ne']
        simp only [update,hs,Bool.false_eq_true,ite_false,Option.getD_some,complementReward,reduceCtorEq,add_zero]
        rw [hdepth,Nat.cast_add]
        nlinarith

end FiniteEntropy

end RepeatedLocalization

end OAI

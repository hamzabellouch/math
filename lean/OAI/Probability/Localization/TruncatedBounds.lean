import OAI.Probability.Localization.RewardBounds

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

namespace FiniteEntropy

lemma rewardLog_run_succ {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n)
    (r : State n → Letter n → ℝ) (hr : ∀ s a,s.stopped = true → r s a = 0)
    (N : ℕ) (z : Coordinate n) :
    rewardLog P Q r (run P Q (N+1) z) = rewardLog P Q r (run P Q N z) + rewardStep P Q r N z := by
  by_cases hs : (state P Q (run P Q N z)).stopped = true
  · simp only [run,hs,ite_true,rewardStep,hr _ _ hs,add_zero]
  · simp only [run,hs,Bool.false_eq_true,ite_false,rewardLog_append,rewardStep]

lemma complementTotal_succ {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (N : ℕ) (z : Coordinate n) :
    complementTotal P Q (N+1) z = complementTotal P Q N z + rewardStep P Q (complementReward P) N z :=
  rewardLog_run_succ P Q _ (fun s a hs => by simp [complementReward,hs]) N z

lemma continuingTotal_succ {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (N : ℕ) (z : Coordinate n) :
    continuingTotal P Q (N+1) z = continuingTotal P Q N z + rewardStep P Q (continuingReward P) N z :=
  rewardLog_run_succ P Q _ (fun s a hs => by simp [continuingReward,hs]) N z

lemma truncatedAttempts_succ {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (N : ℕ) (z : Coordinate n) :
    (truncatedAttempts P Q (N+1) z : ℝ) = truncatedAttempts P Q N z + activeIndicator P Q N z := by
  by_cases hs : (state P Q (run P Q N z)).stopped = true
  · simp [truncatedAttempts,activeIndicator,run,hs]
  · simp [truncatedAttempts,activeIndicator,run,hs,List.length_append]

lemma measurable_truncatedAttempts {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) (Q : Cell n) (N : ℕ) :
    Measurable (fun z => (truncatedAttempts P Q N z : ℝ)) :=
  (measurable_of_countable (fun h : Log n => (h.length:ℝ))).comp (measurable_run hn P Q N)

lemma integrable_truncatedAttempts {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n))
    [IsFiniteMeasure P] (Q : Cell n) (N : ℕ) : Integrable (fun z => (truncatedAttempts P Q N z : ℝ)) P := by
  apply Integrable.mono' (integrable_const (N:ℝ)) (measurable_truncatedAttempts hn P Q N).aestronglyMeasurable
  exact ae_of_all _ (fun z => by
    rw [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast run_length_le P Q N z)

lemma truncated_reward_bounds {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n))
    [IsFiniteMeasure P] (Q : Cell n) (hroot : ∀ᵐ z ∂P,z ∈ cellSet Q) (N : ℕ) :
    Integrable (complementTotal P Q N) P ∧ Integrable (continuingTotal P Q N) P ∧
    (∫ z,complementTotal P Q N z ∂P) ≤ (1/Real.exp 1)*(∫ z,(truncatedAttempts P Q N z : ℝ) ∂P) ∧
    (∫ z,continuingTotal P Q N z ∂P) ≤ (1/2:ℝ)*(∫ z,(truncatedAttempts P Q N z : ℝ) ∂P) := by
  induction N with
  | zero =>
    have hJ : complementTotal P Q 0 = fun _ => 0 := rfl
    have hC : continuingTotal P Q 0 = fun _ => 0 := rfl
    simp [hJ,hC,truncatedAttempts,run]
  | succ N ih =>
    have hJ := complementStep_bound hn P Q hroot N
    have hC := continuingStep_bound hn P Q hroot N
    have eqJ : complementTotal P Q (N+1) = complementTotal P Q N + rewardStep P Q (complementReward P) N :=
      funext (complementTotal_succ P Q N)
    have eqC : continuingTotal P Q (N+1) = continuingTotal P Q N + rewardStep P Q (continuingReward P) N :=
      funext (continuingTotal_succ P Q N)
    rw [eqJ,eqC]
    refine ⟨ih.1.add hJ.1,ih.2.1.add hC.1,?_,?_⟩
    · simp only [Pi.add_apply]
      simp_rw [truncatedAttempts_succ]
      rw [integral_add ih.1 hJ.1,integral_add (integrable_truncatedAttempts hn P Q N) (integrable_activeIndicator P Q hn N)]
      nlinarith [ih.2.2.1,hJ.2]
    · simp only [Pi.add_apply]
      simp_rw [truncatedAttempts_succ]
      rw [integral_add ih.2.1 hC.1,integral_add (integrable_truncatedAttempts hn P Q N) (integrable_activeIndicator P Q hn N)]
      nlinarith [ih.2.2.2,hC.2]

lemma truncated_attempts_path {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) (Q : Cell n)
    (N : ℕ) {z : Coordinate n} (hz : z ∈ cellSet Q) :
    (truncatedAttempts P Q N z : ℝ) ≤ truncatedDepth P Q N z + continuingTotal P Q N z +
      (if (state P Q (run P Q N z)).stopped then (1:ℝ) else 0) := by
  induction N with
  | zero => simp [truncatedAttempts,truncatedDepth,continuingTotal,rewardLog,run,state_nil,accumulate]
  | succ N ih =>
    have hzE := run_mem_event P Q N hz
    have hdesc := state_descendant_of_mem P Q (run P Q N z) hzE
    by_cases hs : (state P Q (run P Q N z)).stopped = true
    · simpa only [truncatedAttempts,truncatedDepth,continuingTotal,run,hs,ite_true] using ih
    let s := state P Q (run P Q N z)
    let a := attemptLetter (ProbabilityTheory.cond P s.event) s.cell z
    have hs' : s.stopped = false := Bool.eq_false_iff.mpr hs
    have erun : run P Q (N+1) z = run P Q N z ++ [a] := by simp only [run,hs,Bool.false_eq_true,ite_false]; rfl
    have eqA := truncatedAttempts_succ P Q N z
    have eqC := continuingTotal_succ P Q N z
    have hih : (truncatedAttempts P Q N z : ℝ) ≤ truncatedDepth P Q N z + continuingTotal P Q N z := by
      simpa only [hs,Bool.false_eq_true,ite_false,add_zero] using ih
    rw [eqA,eqC]
    simp only [activeIndicator,hs,Bool.false_eq_true,ite_false,rewardStep]
    change _ ≤ truncatedDepth P Q (N+1) z + (continuingTotal P Q N z + continuingReward P s a) +
      (if (state P Q (run P Q (N+1) z)).stopped then 1 else 0)
    rw [erun,state_append]
    change _ ≤ truncatedDepth P Q (N+1) z + (continuingTotal P Q N z + continuingReward P s a) +
      (if (update P s a).stopped then 1 else 0)
    cases ha : a with
    | none =>
      have eqD : truncatedDepth P Q (N+1) z = truncatedDepth P Q N z := by
        simp only [truncatedDepth,erun,state_append,ha,update,hs,Bool.false_eq_true,ite_false,Option.getD_none]
      rw [eqD]
      have hstop : (update P s none).stopped = decide ((1/2:ℝ) ≤ complementMass P s) := by
        simp [update,hs',branch,complementMass]
      rw [hstop]
      by_cases hq : complementMass P s < 1/2
      · have hq' : ¬(1/2:ℝ) ≤ complementMass P s := not_le.mpr hq
        simp only [continuingReward,hs',Bool.false_eq_true,ite_false,true_and,ite_eq_left hq,
          decide_eq_true_eq,ite_eq_right hq',add_zero]
        linarith
      · have hq' : (1/2:ℝ) ≤ complementMass P s := le_of_not_gt hq
        simp only [continuingReward,hs',Bool.false_eq_true,ite_false,true_and,ite_eq_right hq,
          decide_eq_true_eq,ite_eq_left hq',add_zero]
        linarith
    | some R =>
      have hR : FirstHeavy (ProbabilityTheory.cond P s.event) s.cell R :=
        ((attemptLetter_some_iff hn _ _ R z).mp ha).1
      have eqD : truncatedDepth P Q (N+1) z = truncatedDepth P Q N z + (R.1-s.cell.1) := by
        simp only [truncatedDepth,erun,state_append,ha,update,hs,Bool.false_eq_true,ite_false,Option.getD_some]
        have hbase : Q.1 ≤ s.cell.1 := hdesc.1
        have hnext : s.cell.1 ≤ R.1 := hR.1.1.1
        change R.1-Q.1 = s.cell.1-Q.1+(R.1-s.cell.1)
        omega
      rw [eqD,Nat.cast_add]
      simp only [update,hs',Bool.false_eq_true,ite_false,reduceCtorEq,continuingReward,false_and,add_zero]
      have hd : (1:ℝ) ≤ (R.1-s.cell.1 : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hR.1.2.1
      linarith

end FiniteEntropy

end RepeatedLocalization

end OAI

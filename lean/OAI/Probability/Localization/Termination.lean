import OAI.Probability.Localization.EntropyBudget

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

namespace FiniteEntropy

open Filter
open scoped Topology

lemma exists_fiber_good {α ι : Type*} [MeasurableSpace α] (P : Measure α) (L : α → ι)
    (Good : α → Prop) (hgood : ∀ᵐ z ∂P,Good z) (i : ι) (hp : P {z | L z = i} ≠ 0) :
    ∃ z,L z = i ∧ Good z := by
  classical
  by_contra h
  have ha : ∀ᵐ z ∂P,L z ≠ i := hgood.mono (fun z hz he => h ⟨z,he,hz⟩)
  exact hp (by simpa only [not_not] using (ae_iff.mp ha))

lemma ae_fiber_positive {α ι : Type*} [MeasurableSpace α] [Countable ι] (P : Measure α) (L : α → ι) :
    ∀ᵐ z ∂P,P {w | L w = L z} ≠ 0 := by
  classical
  have h (i : ι) : ∀ᵐ z ∂P,L z = i → P {w | L w = i} ≠ 0 := by
    by_cases hp : P {w | L w = i} = 0
    · have ha : ∀ᵐ z ∂P,L z ≠ i := ae_iff.mpr (by simpa only [not_not] using hp)
      exact ha.mono (fun z hz he => (hz he).elim)
    · exact ae_of_all _ (fun _ _ => hp)
  filter_upwards [ae_all_iff.mpr h] with z hz
  exact hz (L z) rfl

lemma frozen_nonnegative_bound {α : Type*} [MeasurableSpace α] (P : Measure α)
    (f : ℕ → α → ℝ) (F : α → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ N,Integrable (f N) P) (hf0 : ∀ N z,0 ≤ f N z)
    (hF : AEStronglyMeasurable F P) (hF0 : ∀ z,0 ≤ F z)
    (hfreeze : ∀ᵐ z ∂P,∃ N,∀ M,N ≤ M → f M z = F z)
    (hbound : ∀ N,(∫ z,f N z ∂P) ≤ B) :
    Integrable F P ∧ (∫ z,F z ∂P) ≤ B := by
  have he : (fun z => ENNReal.ofReal (F z)) =ᵐ[P]
      (fun z => liminf (fun N => ENNReal.ofReal (f N z)) atTop) := by
    filter_upwards [hfreeze] with z hz
    obtain ⟨N,hN⟩ := hz
    have ht : Tendsto (fun M => ENNReal.ofReal (f M z)) atTop (𝓝 (ENNReal.ofReal (F z))) :=
      tendsto_const_nhds.congr' (eventually_atTop.mpr ⟨N,fun M hM => congrArg ENNReal.ofReal (hN M hM).symm⟩)
    exact ht.liminf_eq.symm
  have hb : (∫⁻ z,ENNReal.ofReal (F z) ∂P) ≤ ENNReal.ofReal B := by
    rw [lintegral_congr_ae he]
    apply (lintegral_liminf_le' (fun N => (hf N).aemeasurable.ennreal_ofReal)).trans
    apply liminf_le_of_frequently_le'
    apply Filter.Eventually.frequently
    exact Filter.Eventually.of_forall (fun N => by
      rw [← ofReal_integral_eq_lintegral_ofReal (hf N) (ae_of_all _ (hf0 N))]
      exact ENNReal.ofReal_le_ofReal (hbound N))
  have hi : Integrable F P := ⟨hF,(hasFiniteIntegral_iff_ofReal (ae_of_all _ hF0)).mpr
    (hb.trans_lt ENNReal.ofReal_lt_top)⟩
  refine ⟨hi,?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hF0)] at hb
  exact (ENNReal.ofReal_le_ofReal_iff hB).mp hb

lemma truncatedDepth_mono {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) (Q : Cell n)
    {z : Coordinate n} (hz : z ∈ cellSet Q) : Monotone (fun N => truncatedDepth P Q N z) := by
  classical
  apply monotone_nat_of_le_succ
  intro N
  by_cases hs : (state P Q (run P Q N z)).stopped = true
  · simp only [truncatedDepth,run,hs,ite_true,le_refl]
  let s := state P Q (run P Q N z)
  let a := attemptLetter (ProbabilityTheory.cond P s.event) s.cell z
  have erun : run P Q (N+1) z = run P Q N z ++ [a] := by simp only [run,hs,Bool.false_eq_true,ite_false]; rfl
  simp only [truncatedDepth,erun,state_append,update,hs,Bool.false_eq_true,ite_false]
  cases ha : a with
  | none => simp only [Option.getD_none,le_refl]
  | some R =>
    have hcell := state_event_subset_cell P Q _ (run_mem_event P Q N hz)
    have hbranch : z ∈ branch (ProbabilityTheory.cond P s.event) s.cell (some R) :=
      (attemptLetter_eq_iff hn _ _ hcell (some R)).mp ha
    have hR : FirstHeavy (ProbabilityTheory.cond P s.event) s.cell R := by
      by_contra hR
      simp only [branch,ite_eq_right hR,Set.mem_empty_iff_false] at hbranch
    exact Nat.sub_le_sub_right hR.1.1.1 Q.1

lemma run_eventually_terminal {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n)
    {z : Coordinate n} (ht : Terminates P Q z) :
    ∀ M,attempts P Q z ≤ M → run P Q M z = terminalLog P Q z := by
  intro M hM
  exact run_of_stopped_le P Q z hM (attempts_spec P Q ht)

lemma budget_nonneg {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) :
    0 ≤ (InformationTheory.klDiv P (uniformCell Q)).toReal + 2/Real.exp 1 := by positivity

lemma truncated_uniform_attempts {n : ℕ} (hn : 32 ≤ n) (P : Measure (Coordinate n)) [IsProbabilityMeasure P]
    (Q : Cell n) (hac : P ≪ uniformCell Q) (hK : InformationTheory.klDiv P (uniformCell Q) ≠ ∞) (N : ℕ) :
    (∫ z,(truncatedAttempts P Q N z:ℝ) ∂P) ≤
      2*(1+((InformationTheory.klDiv P (uniformCell Q)).toReal + 2/Real.exp 1)/(entropySlope n/2)) := by
  have hn0 : 0 < n := by omega
  have hB := truncated_final_budget hn P Q hac hK N
  rw [integral_add (truncated_KL_integrable hn0 P Q hac hK N)
    ((truncated_depth_integrable hn0 P Q hac hK N).const_mul _),integral_const_mul] at hB
  have hk0 : 0 ≤ ∫ z,(historyKL P Q (run P Q N z)).toReal ∂P := integral_nonneg (fun _ => ENNReal.toReal_nonneg)
  have hd : (∫ z,(truncatedDepth P Q N z:ℝ) ∂P) ≤
      ((InformationTheory.klDiv P (uniformCell Q)).toReal + 2/Real.exp 1)/(entropySlope n/2) := by
    rw [le_div_iff₀ (div_pos (entropySlope_pos hn0) (by norm_num))]
    nlinarith
  exact (truncated_attempts_integral hn0 P Q hac hK N).trans (by linarith)

lemma almost_sure_termination {n : ℕ} (hn : 32 ≤ n) (P : Measure (Coordinate n)) [IsProbabilityMeasure P]
    (Q : Cell n) (hac : P ≪ uniformCell Q) (hK : InformationTheory.klDiv P (uniformCell Q) ≠ ∞) :
    ∀ᵐ z ∂P,Terminates P Q z := by
  have hn0 : 0 < n := by omega
  let E := {z | ¬Terminates P Q z}
  have hE : MeasurableSet E := (measurableSet_terminates hn0 P Q).compl
  apply ae_iff.mpr
  change P E = 0
  by_contra hp
  have hp0 : 0 < (P E).toReal := ENNReal.toReal_pos hp (measure_ne_top _ _)
  let B := 2*(1+((InformationTheory.klDiv P (uniformCell Q)).toReal + 2/Real.exp 1)/(entropySlope n/2))
  obtain ⟨N,hN⟩ := exists_nat_gt (B/(P E).toReal)
  have hconst : ∀ z ∈ E,(truncatedAttempts P Q N z:ℝ) = N := by
    intro z hz
    have ha : (state P Q (run P Q N z)).stopped = false := by
      apply Bool.eq_false_iff.mpr
      intro hs
      exact hz ⟨N,hs⟩
    exact congrArg (fun k : ℕ => (k:ℝ)) (run_length_of_active P Q N z ha)
  have hi := setIntegral_le_integral (s := E) (integrable_truncatedAttempts hn0 P Q N)
    (ae_of_all _ (fun _ => Nat.cast_nonneg _))
  rw [setIntegral_congr_fun hE hconst,integral_const] at hi
  simp only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul] at hi
  have hb := truncated_uniform_attempts hn P Q hac hK N
  change _ ≤ B at hb
  have hN' := (div_lt_iff₀ hp0).mp hN
  nlinarith

lemma history_regular_of_stopped {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) [IsFiniteMeasure P]
    (Q : Cell n) (h : Log n) (hp : P (state P Q h).event ≠ 0) (hs : (state P Q h).stopped = true) :
    Regular (ProbabilityTheory.cond P (state P Q h).event) (state P Q h).cell := by
  induction h using List.reverseRecOn with
  | nil => simp only [state_nil,Bool.false_eq_true] at hs
  | append_singleton h a ih =>
    have hp0 : P (state P Q h).event ≠ 0 := by
      intro he
      exact hp (measure_mono_null (state_event_append_subset P Q h a) he)
    by_cases hs0 : (state P Q h).stopped = true
    · simp only [state_append,update,hs0,ite_true] at hs ⊢
      exact ih hp0 hs0
    let := ProbabilityTheory.cond_isProbabilityMeasure (μ := P) hp0
    cases a with
    | some R => simp [state_append,update,hs0] at hs
    | none =>
      have hq : (1/2:ℝ) ≤ ((ProbabilityTheory.cond P (state P Q h).event)
          (residual (ProbabilityTheory.cond P (state P Q h).event) (state P Q h).cell)).toReal := by
        simpa [state_append,update,hs0,branch] using hs
      have hr := stopped_regular hn (ProbabilityTheory.cond P (state P Q h).event) (state P Q h).cell hq
      rw [ProbabilityTheory.cond_cond_eq_cond_inter' (state_event_measurable P Q h)
        (measurableSet_residual _ _) (measure_ne_top _ _)] at hr
      simpa [state_append,update,hs0,branch] using hr

lemma terminal_regular {n : ℕ} (hn : 32 ≤ n) (P : Measure (Coordinate n)) [IsProbabilityMeasure P]
    (Q : Cell n) (hac : P ≪ uniformCell Q) (hK : InformationTheory.klDiv P (uniformCell Q) ≠ ∞)
    (h : Log n) (hp : P {z | terminalLog P Q z = h} ≠ 0) :
    Descendant Q (terminalCell P Q h) ∧ Regular (terminalLaw P Q h) (terminalCell P Q h) ∧
      InformationTheory.klDiv (terminalLaw P Q h) (uniformCell (terminalCell P Q h)) ≠ ∞ := by
  have hn0 : 0 < n := by omega
  have hroot := ae_mem_cell_of_ac hac
  have hterm := almost_sure_termination hn P Q hac hK
  obtain ⟨z,hzh,hz,ht⟩ := exists_fiber_good P (terminalLog P Q)
    (fun z => z ∈ cellSet Q ∧ Terminates P Q z) (hroot.and hterm) h hp
  have he : {w | terminalLog P Q w = h} =ᵐ[P] (state P Q h).event := by
    simpa only [hzh] using terminal_fiber_ae_event hn0 P Q hroot hz ht
  have hp' : P (state P Q h).event ≠ 0 := by rwa [← measure_congr he]
  have hstop : (state P Q h).stopped = true := by
    rw [← hzh]
    exact attempts_spec P Q ht
  have hLaw : terminalLaw P Q h = ProbabilityTheory.cond P (state P Q h).event := cond_congr_ae P he
  refine ⟨positive_event_descendant P Q h hp',?_,?_⟩
  · rw [hLaw]
    exact history_regular_of_stopped hn0 P Q h hp' hstop
  · rw [hLaw]
    exact (historyKL_ne_top_budget hn0 P Q hac hK h hp').1

end FiniteEntropy

end RepeatedLocalization

end OAI

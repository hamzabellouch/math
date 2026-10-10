import OAI.Probability.Localization.FirstHeavy

namespace OAI

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RepeatedLocalization

namespace FiniteEntropy

instance letterMeasurableSpace (n : ℕ) : MeasurableSpace (Letter n) := ⊤

lemma state_nil {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) :
    state P Q [] = ⟨Q,cellSet Q,false⟩ := rfl

lemma state_append {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (h : Log n) (a : Letter n) :
    state P Q (h++[a]) = update P (state P Q h) a := by
  simp only [state,List.foldl_append,List.foldl_cons,List.foldl_nil]

lemma attemptLetter_none_iff {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (z : Coordinate n) :
    attemptLetter P Q z = none ↔ ¬ ∃ R : Cell n,FirstHeavy P Q R ∧ z ∈ cellSet R := by
  classical
  by_cases h : ∃ R : Cell n,FirstHeavy P Q R ∧ z ∈ cellSet R
  · rw [attemptLetter,dite_eq_left h]
    simp only [reduceCtorEq,h,not_true_eq_false]
  · rw [attemptLetter,dite_eq_right h]
    simp only [h,not_false_eq_true]

lemma attemptLetter_some_iff {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) (Q R : Cell n)
    (z : Coordinate n) : attemptLetter P Q z = some R ↔ FirstHeavy P Q R ∧ z ∈ cellSet R := by
  classical
  constructor
  · intro he
    have hex : ∃ E : Cell n,FirstHeavy P Q E ∧ z ∈ cellSet E := by
      by_contra h
      rw [(attemptLetter_none_iff P Q z).mpr h] at he
      contradiction
    have hc : hex.choose = R := by
      simpa only [attemptLetter,dite_eq_left hex,Option.some.injEq] using he
    exact hc ▸ hex.choose_spec
  · rintro ⟨hR,hzR⟩
    exact (attemptLetter_eq_iff hn P Q (hR.1.1.2 hzR) (some R)).mpr (by simp only [branch,ite_eq_left hR]; exact hzR)

lemma measurableSet_firstHeavy_union {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) :
    MeasurableSet (⋃ R : {R : Cell n // FirstHeavy P Q R},cellSet R.val) :=
  MeasurableSet.iUnion fun R => measurableSet_cellSet R.val

lemma measurable_attemptLetter {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) (Q : Cell n) :
    Measurable (attemptLetter P Q) := by
  classical
  apply measurable_to_countable'
  intro a
  change MeasurableSet {z | attemptLetter P Q z = a}
  cases a with
  | none =>
    have he : {z | attemptLetter P Q z = none} =
        (⋃ R : {R : Cell n // FirstHeavy P Q R},cellSet R.val)ᶜ := by
      ext z
      simp only [Set.mem_ofPred_eq,attemptLetter_none_iff,Set.mem_compl_iff,Set.mem_iUnion]
      apply not_congr
      exact ⟨fun ⟨R,hR,hzR⟩ => ⟨⟨R,hR⟩,hzR⟩,fun ⟨R,hzR⟩ => ⟨R.val,R.property,hzR⟩⟩
    rw [he]
    exact (measurableSet_firstHeavy_union P Q).compl
  | some R =>
    have he : {z | attemptLetter P Q z = some R} = {z | FirstHeavy P Q R ∧ z ∈ cellSet R} := by
      ext z
      exact attemptLetter_some_iff hn P Q R z
    rw [he]
    by_cases hR : FirstHeavy P Q R
    · convert measurableSet_cellSet R using 1
      ext z; simp only [Set.mem_ofPred_eq,hR,true_and]
    · simp only [hR,false_and,Set.ofPred_false,MeasurableSet.empty]

lemma state_event_measurable {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (h : Log n) :
    MeasurableSet (state P Q h).event := by
  induction h using List.reverseRecOn with
  | nil => exact measurableSet_cellSet Q
  | append_singleton h a ih =>
    rw [state_append]
    unfold update
    split
    · exact ih
    · exact ih.inter (measurableSet_branch _ _ _)

lemma state_event_subset_initial {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (h : Log n) :
    (state P Q h).event ⊆ cellSet Q := by
  induction h using List.reverseRecOn with
  | nil => exact Subset.rfl
  | append_singleton h a ih =>
    rw [state_append]
    unfold update
    split
    · exact ih
    · exact Set.inter_subset_left.trans ih

lemma state_event_subset_cell {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (h : Log n) :
    (state P Q h).event ⊆ cellSet (state P Q h).cell := by
  classical
  induction h using List.reverseRecOn with
  | nil => exact Subset.rfl
  | append_singleton h a ih =>
    rw [state_append]
    unfold update
    split
    · exact ih
    · cases a with
      | none => exact Set.inter_subset_left.trans ih
      | some R =>
        simp only [Option.getD_some]
        intro z hz
        by_cases hR : FirstHeavy (ProbabilityTheory.cond P (state P Q h).event) (state P Q h).cell R
        · simpa only [branch,ite_eq_left hR] using hz.2
        · simpa only [branch,ite_eq_right hR,Set.mem_empty_iff_false] using hz.2

lemma state_descendant_of_mem {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n)
    (h : Log n) {z : Coordinate n} (hz : z ∈ (state P Q h).event) :
    Descendant Q (state P Q h).cell := by
  classical
  induction h using List.reverseRecOn with
  | nil => exact Descendant.refl Q
  | append_singleton h a ih =>
    rw [state_append] at hz ⊢
    unfold update at hz ⊢
    by_cases hs : (state P Q h).stopped = true
    · simp only [hs,ite_true] at hz ⊢
      exact ih hz
    · simp only [hs] at hz ⊢
      cases a with
      | none => exact ih hz.1
      | some R =>
        have hR : FirstHeavy (ProbabilityTheory.cond P (state P Q h).event) (state P Q h).cell R := by
          by_contra hR
          simpa only [branch,ite_eq_right hR,Set.mem_empty_iff_false] using hz.2
        exact (ih hz.1).trans hR.1.1

lemma measurable_run {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) (Q : Cell n) (N : ℕ) :
    Measurable (run P Q N) := by
  classical
  induction N with
  | zero => exact measurable_const
  | succ N ih =>
    have hf (h : Log n) : Measurable (fun z => if (state P Q h).stopped then h else
        h++[attemptLetter (ProbabilityTheory.cond P (state P Q h).event) (state P Q h).cell z]) := by
      split
      · exact measurable_const
      · exact (measurable_of_countable (fun a : Letter n => h++[a])).comp (measurable_attemptLetter hn _ _)
    let f : Log n × Coordinate n → Log n := fun hz =>
      if (state P Q hz.1).stopped then hz.1 else hz.1++
        [attemptLetter (ProbabilityTheory.cond P (state P Q hz.1).event) (state P Q hz.1).cell hz.2]
    exact (measurable_from_prod_countable_right (f := f) hf).comp (ih.prodMk measurable_id)

lemma run_length_le {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (N : ℕ) (z : Coordinate n) :
    (run P Q N z).length ≤ N := by
  induction N with
  | zero => simp [run]
  | succ N ih =>
    simp only [run]
    split
    · exact ih.trans (Nat.le_succ N)
    · simpa only [List.length_append,List.length_singleton] using Nat.add_le_add_right ih 1

lemma run_length_of_active {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (N : ℕ)
    (z : Coordinate n) (ha : (state P Q (run P Q N z)).stopped = false) :
    (run P Q N z).length = N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    have hprev : (state P Q (run P Q N z)).stopped = false := by
      cases he : (state P Q (run P Q N z)).stopped
      · rfl
      · simp only [run,he,ite_true] at ha
        exact ha
    simp only [run,hprev,Bool.false_eq_true,ite_false,List.length_append,List.length_singleton]
    rw [ih hprev]

lemma run_mem_event {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (N : ℕ)
    {z : Coordinate n} (hz : z ∈ cellSet Q) : z ∈ (state P Q (run P Q N z)).event := by
  induction N with
  | zero => exact hz
  | succ N ih =>
    simp only [run]
    split
    · exact ih
    · rw [state_append]
      unfold update
      split
      · exact ih
      · exact ⟨ih,attemptLetter_mem_branch _ _ (state_event_subset_cell _ _ _ ih)⟩

lemma run_eq_iff_mem {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) (Q : Cell n)
    (N : ℕ) {z w : Coordinate n} (hz : z ∈ cellSet Q) (hw : w ∈ cellSet Q) :
    run P Q N w = run P Q N z ↔ w ∈ (state P Q (run P Q N z)).event := by
  classical
  induction N generalizing z w with
  | zero => simpa only [run,state_nil,true_iff] using hw
  | succ N ih =>
    cases hzstop : (state P Q (run P Q N z)).stopped with
    | false =>
      cases hwstop : (state P Q (run P Q N w)).stopped with
      | false =>
        simp only [run,hzstop,hwstop,Bool.false_eq_true,ite_false,state_append,update,
          List.append_singleton_inj]
        constructor
        · rintro ⟨hh,ha⟩
          refine ⟨(ih hz hw).mp hh,?_⟩
          have hwm := run_mem_event P Q N hw
          rw [hh] at hwm
          apply (attemptLetter_eq_iff hn _ _ (state_event_subset_cell _ _ _ hwm) _).mp
          simpa only [hh] using ha
        · rintro ⟨hwm,hwa⟩
          have hh := (ih hz hw).mpr hwm
          refine ⟨hh,?_⟩
          rw [hh]
          exact (attemptLetter_eq_iff hn _ _ (state_event_subset_cell _ _ _ hwm) _).mpr hwa
      | true =>
        simp only [run,hzstop,hwstop,Bool.false_eq_true,ite_false,ite_true,state_append,update]
        constructor
        · intro he
          have hl := congrArg List.length he
          rw [List.length_append,List.length_singleton,run_length_of_active P Q N z hzstop] at hl
          have := run_length_le P Q N w
          omega
        · intro hm
          have hh := (ih hz hw).mpr hm.1
          rw [hh,hzstop] at hwstop
          contradiction
    | true =>
      cases hwstop : (state P Q (run P Q N w)).stopped with
      | false =>
        simp only [run,hzstop,hwstop,Bool.false_eq_true,ite_false,ite_true]
        constructor
        · intro he
          have hl := congrArg List.length he
          rw [List.length_append,List.length_singleton,run_length_of_active P Q N w hwstop] at hl
          have := run_length_le P Q N z
          omega
        · intro hm
          have hh := (ih hz hw).mpr hm
          rw [hh,hzstop] at hwstop
          contradiction
      | true => simpa only [run,hzstop,hwstop,ite_true] using ih hz hw

lemma run_fiber_inter_initial {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) (Q : Cell n)
    (N : ℕ) {z : Coordinate n} (hz : z ∈ cellSet Q) :
    cellSet Q ∩ {w | run P Q N w = run P Q N z} = (state P Q (run P Q N z)).event := by
  ext w
  constructor
  · rintro ⟨hw,he⟩
    exact (run_eq_iff_mem hn P Q N hz hw).mp he
  · intro hm
    have hw := state_event_subset_initial _ _ _ hm
    exact ⟨hw,(run_eq_iff_mem hn P Q N hz hw).mpr hm⟩

lemma run_succ_of_stopped {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (N : ℕ)
    (z : Coordinate n) (h : (state P Q (run P Q N z)).stopped = true) :
    run P Q (N+1) z = run P Q N z := by simp only [run,h,ite_true]

lemma run_add_of_stopped {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) (N M : ℕ)
    (z : Coordinate n) (h : (state P Q (run P Q N z)).stopped = true) :
    run P Q (N+M) z = run P Q N z := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Nat.add_succ,run_succ_of_stopped P Q (N+M) z (by rw [ih]; exact h),ih]

lemma run_of_stopped_le {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) {N M : ℕ}
    (z : Coordinate n) (hNM : N ≤ M) (h : (state P Q (run P Q N z)).stopped = true) :
    run P Q M z = run P Q N z := by
  obtain ⟨M,rfl⟩ := Nat.exists_eq_add_of_le hNM
  exact run_add_of_stopped P Q N M z h

lemma attempts_spec {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) {z : Coordinate n}
    (hz : Terminates P Q z) : (state P Q (terminalLog P Q z)).stopped = true := by
  simpa only [terminalLog,attempts,dite_eq_left hz] using Nat.find_spec hz

lemma attempts_min {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) {z : Coordinate n}
    (hz : Terminates P Q z) {N : ℕ} (hN : N < attempts P Q z) :
    (state P Q (run P Q N z)).stopped = false := by
  have hm : ¬ (state P Q (run P Q N z)).stopped = true := Nat.find_min hz (by
    simpa only [attempts,dite_eq_left hz] using hN)
  simpa using hm

lemma attempts_pos {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) {z : Coordinate n}
    (hz : Terminates P Q z) : 0 < attempts P Q z := by
  by_contra h
  have he : attempts P Q z = 0 := by omega
  have hs := attempts_spec P Q hz
  simp [terminalLog,he,run,state_nil] at hs

lemma terminalLog_length {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n) {z : Coordinate n}
    (hz : Terminates P Q z) : (terminalLog P Q z).length = attempts P Q z := by
  obtain ⟨N,hN⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt (attempts_pos P Q hz))
  have hn : (state P Q (run P Q N z)).stopped = false := attempts_min P Q hz (by omega)
  simp only [terminalLog,hN,run,hn,Bool.false_eq_true,ite_false,List.length_append,List.length_singleton]
  rw [run_length_of_active P Q N z hn]

lemma terminalLog_of_stopped {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n)
    {N : ℕ} {z : Coordinate n} (h : (state P Q (run P Q N z)).stopped = true) :
    terminalLog P Q z = run P Q N z := by
  have ht : Terminates P Q z := ⟨N,h⟩
  have hle : attempts P Q z ≤ N := by
    simpa only [attempts,dite_eq_left ht] using Nat.find_min' ht h
  exact (run_of_stopped_le P Q z hle (attempts_spec P Q ht)).symm

lemma measurableSet_stopped {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) (Q : Cell n) (N : ℕ) :
    MeasurableSet {z | (state P Q (run P Q N z)).stopped = true} :=
  ((measurable_of_countable (fun h : Log n => (state P Q h).stopped)).comp
    (measurable_run hn P Q N)) (measurableSet_singleton true)

lemma measurableSet_terminates {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) (Q : Cell n) :
    MeasurableSet {z | Terminates P Q z} := by
  have he : {z | Terminates P Q z} = ⋃ N : ℕ,{z | (state P Q (run P Q N z)).stopped = true} := by
    ext z; simp only [Terminates,Set.mem_ofPred_eq,Set.mem_iUnion]
  rw [he]
  exact MeasurableSet.iUnion (measurableSet_stopped hn P Q)

lemma measurable_attempts {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) (Q : Cell n) :
    Measurable (attempts P Q) := by
  classical
  have hex (z : Coordinate n) : ∃ N : ℕ,(state P Q (run P Q N z)).stopped = true ∨ ¬ Terminates P Q z := by
    by_cases h : Terminates P Q z
    · obtain ⟨N,hN⟩ := h
      exact ⟨N,Or.inl hN⟩
    · exact ⟨0,Or.inr h⟩
  have he (z : Coordinate n) : attempts P Q z = Nat.find (hex z) := by
    by_cases h : Terminates P Q z
    · simp only [attempts,dite_eq_left h]
      apply le_antisymm
      · exact Nat.find_min' h ((Nat.find_spec (hex z)).resolve_right (not_not.mpr h))
      · exact Nat.find_min' (hex z) (Or.inl (Nat.find_spec h))
    · simp only [attempts,dite_eq_right h]
      exact (Nat.eq_zero_of_le_zero (Nat.find_min' (hex z) (show
        (state P Q (run P Q 0 z)).stopped = true ∨ ¬ Terminates P Q z from Or.inr h))).symm
  have hm : Measurable (fun z => Nat.find (hex z)) := Measurable.find (f := fun N (_ : Coordinate n) => N) (p := fun N z =>
      (state P Q (run P Q N z)).stopped = true ∨ ¬ Terminates P Q z)
    (fun N => measurable_const) (fun N => (measurableSet_stopped hn P Q N).union
      (measurableSet_terminates hn P Q).compl) hex
  convert hm using 1
  funext z
  exact he z

lemma measurable_terminalLog {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) (Q : Cell n) :
    Measurable (terminalLog P Q) := by
  have hm : Measurable (fun Nz : ℕ × Coordinate n => run P Q Nz.1 Nz.2) :=
    measurable_from_prod_countable_right (measurable_run hn P Q)
  exact hm.comp ((measurable_attempts hn P Q).prodMk measurable_id)

lemma terminates_of_terminal_stopped {n : ℕ} (P : Measure (Coordinate n)) (Q : Cell n)
    {z : Coordinate n} (hs : (state P Q (terminalLog P Q z)).stopped = true) : Terminates P Q z :=
  ⟨attempts P Q z,hs⟩

lemma terminalLog_fiber_inter_initial {n : ℕ} (hn : 0 < n) (P : Measure (Coordinate n)) (Q : Cell n)
    {z : Coordinate n} (hz : z ∈ cellSet Q) (ht : Terminates P Q z) :
    cellSet Q ∩ {w | terminalLog P Q w = terminalLog P Q z} =
      (state P Q (terminalLog P Q z)).event := by
  ext w
  constructor
  · rintro ⟨hw,he⟩
    change terminalLog P Q w = terminalLog P Q z at he
    have htw : Terminates P Q w := terminates_of_terminal_stopped P Q (by rw [he]; exact attempts_spec P Q ht)
    have hlen : attempts P Q w = attempts P Q z := by
      rw [← terminalLog_length P Q htw,← terminalLog_length P Q ht,he]
    apply (run_eq_iff_mem hn P Q (attempts P Q z) hz hw).mp
    simpa only [terminalLog,hlen] using he
  · intro hm
    have hw := state_event_subset_initial _ _ _ hm
    have he := (run_eq_iff_mem hn P Q (attempts P Q z) hz hw).mpr hm
    refine ⟨hw,?_⟩
    have hs : (state P Q (run P Q (attempts P Q z) w)).stopped = true := by
      rw [he]; exact attempts_spec P Q ht
    exact (terminalLog_of_stopped P Q hs).trans he

end FiniteEntropy

end RepeatedLocalization

end OAI

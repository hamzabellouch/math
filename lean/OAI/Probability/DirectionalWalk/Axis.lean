import OAI.Probability.DirectionalWalk.DirectionalReduction

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

def axisDirection {d : ℕ} (e : Step d) : Fin d → ℝ :=
  Pi.single e.1 (if e.2 then 1 else -1)

def axisHeight {d : ℕ} (e : Step d) (x : Site d) : ℤ :=
  if e.2 then x e.1 else -(x e.1)

lemma height_axisDirection {d : ℕ} (e : Step d) (x : Site d) :
    height (axisDirection e) x = (axisHeight e x : ℝ) := by
  rcases e with ⟨i,b⟩
  cases b <;> simp [height,axisDirection,axisHeight,Pi.single_apply]

lemma axisHeight_zero {d : ℕ} (e : Step d) : axisHeight e 0 = 0 := by
  simp [axisHeight]

lemma axisDirection_ne_zero {d : ℕ} (e : Step d) : axisDirection e ≠ 0 := by
  intro hh
  have h := congr_fun hh e.1
  rcases e with ⟨i,b⟩
  cases b <;> simp [axisDirection] at h

lemma axisDirection_normalized {d : ℕ} (e : Step d) :
    (∀ i, |axisDirection e i| ≤ 1) ∧ ∃ i, |axisDirection e i| = 1 := by
  classical
  constructor
  · intro i
    simp only [axisDirection, Pi.single_apply]
    split_ifs <;> norm_num
  · refine ⟨e.1, ?_⟩
    simp only [axisDirection, Pi.single_eq_same]
    cases e.2 <;> norm_num

lemma axisHeight_add {d : ℕ} (e : Step d) (x y : Site d) :
    axisHeight e (x+y) = axisHeight e x + axisHeight e y := by
  rcases e with ⟨i,b⟩
  cases b <;> simp [axisHeight,add_comm]

lemma axisHeight_step_le {d : ℕ} (e f : Step d) : axisHeight e (stepVector f) ≤ 1 := by
  rcases e with ⟨i,b⟩
  rcases f with ⟨j,c⟩
  cases b <;> cases c <;> simp [axisHeight,stepVector] <;> split_ifs <;> omega

lemma axisHeight_step_ge {d : ℕ} (e f : Step d) : -1 ≤ axisHeight e (stepVector f) := by
  rcases e with ⟨i,b⟩
  rcases f with ⟨j,c⟩
  cases b <;> cases c <;> simp [axisHeight,stepVector] <;> split_ifs <;> omega

lemma axisHeight_nn_le {d : ℕ} (e : Step d) (X : Path d) (hX : nearestNeighbour X) (n : ℕ) :
    axisHeight e (X (n+1)) ≤ axisHeight e (X n) + 1 := by
  obtain ⟨f,hf⟩ := hX n
  rw [hf,axisHeight_add]
  exact add_le_add le_rfl (axisHeight_step_le e f)

lemma axis_recordCount_witness {d : ℕ} (e : Step d) (X : Path d)
    (h0 : axisHeight e (X 0) = 0) (n : ℕ) :
    ∃ j ≤ n, (recordCount (axisDirection e) X n : ℤ) ≤ axisHeight e (X j) := by
  classical
  induction n with
  | zero => exact ⟨0,le_rfl,by simp [recordCount_zero,h0]⟩
  | succ n ih =>
    obtain ⟨j,hj,hcount⟩ := ih
    rw [recordCount_succ]
    by_cases hr : strictRecord (axisDirection e) X (n+1)
    · rw [ite_eq_left hr, Nat.cast_add, Nat.cast_one]
      refine ⟨n+1,le_rfl,?_⟩
      have hh := hr.2 j (by omega)
      simp only [height_axisDirection,Int.cast_lt] at hh
      omega
    · rw [ite_eq_right hr,add_zero]
      exact ⟨j,by omega,hcount⟩

lemma axis_record_height {d : ℕ} (e : Step d) (X : Path d) (n : ℕ)
    (h0 : X 0 = 0) (hX : ∀ i < n, axisHeight e (X (i+1)) ≤ axisHeight e (X i)+1)
    (hr : n = 0 ∨ strictRecord (axisDirection e) X n) :
    axisHeight e (X n) = (recordCount (axisDirection e) X n : ℤ) := by
  have hz : axisHeight e (X 0) = 0 := by rw [h0,axisHeight_zero]
  apply le_antisymm
  · have hs : ∀ i < n, height (axisDirection e) (X (i+1)) ≤ height (axisDirection e) (X i)+1 := by
      intro i hi
      simp only [height_axisDirection]
      exact_mod_cast hX i hi
    have hh := height_le_recordCount (axisDirection e) X n (by rw [h0,height_zero]) hs n le_rfl
    rw [height_axisDirection] at hh
    exact_mod_cast hh
  · obtain ⟨j,hj,hjc⟩ := axis_recordCount_witness e X hz n
    apply hjc.trans
    rcases hr with rfl | hr
    · have : j = 0 := by omega
      simp [this]
    · by_cases he : j = n
      · rw [he]
      · have hh := hr.2 j (by omega)
        simp only [height_axisDirection,Int.cast_lt] at hh
        exact hh.le

lemma integer_first_crossing (f : ℕ → ℤ) (n : ℕ) (a : ℤ)
    (hf : ∀ i < n, f (i+1) ≤ f i+1) (h0 : f 0 ≤ a) (hn : a ≤ f n) :
    ∃ j ≤ n, f j = a ∧ ∀ i < j, f i < a := by
  have hex : ∃ k, a ≤ f k := ⟨n,hn⟩
  let j := Nat.find hex
  have hj : a ≤ f j := Nat.find_spec hex
  have hjn : j ≤ n := Nat.find_min' hex hn
  have hmin : ∀ i < j, f i < a := by
    intro i hi
    exact lt_of_not_ge (Nat.find_min hex hi)
  refine ⟨j,hjn,?_,hmin⟩
  apply le_antisymm _ hj
  by_cases hz : j = 0
  · simpa [hz] using h0
  · have hbelow := hmin (j-1) (by omega)
    have hstep := hf (j-1) (by omega)
    have he : j-1+1 = j := by omega
    rw [he] at hstep
    omega

def reachAxis {d : ℕ} (e : Step d) (H : ℕ) : Set (Path d) :=
  {X | ∃ n, axisHeight e (X n) = H ∧ ∀ i ≤ n, 0 ≤ axisHeight e (X i)}

lemma measurableSet_reachAxis {d : ℕ} (e : Step d) (H : ℕ) : MeasurableSet (reachAxis e H) := by
  simp only [reachAxis,Set.ofPred_exists,Set.ofPred_and,Set.ofPred_forall]
  refine MeasurableSet.iUnion (fun n => (measurableSet_eq_fun
    ((measurable_of_countable (axisHeight e)).comp (measurable_pi_apply n)) measurable_const).inter ?_)
  exact MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun _ =>
    measurableSet_le measurable_const ((measurable_of_countable (axisHeight e)).comp (measurable_pi_apply i))))

lemma reachRecord_eq_reachAxis {d : ℕ} (e : Step d) (X : Path d)
    (h0 : X 0 = 0) (hX : nearestNeighbour X) (H : ℕ) :
    X ∈ reachRecord (axisDirection e) H ↔ X ∈ reachAxis e H := by
  constructor
  · intro hh
    obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hh
    refine ⟨n,?_,?_⟩
    · rw [axis_record_height e X n h0 (fun i _ => axisHeight_nn_le e X hX i) hn.1,hn.2.1]
    · intro i hi
      have hh := hn.2.2 i hi
      rw [height_axisDirection] at hh
      exact_mod_cast hh
  · rintro ⟨n,hn,hbelow⟩
    obtain ⟨j,hjn,hj,hmin⟩ := integer_first_crossing (fun i => axisHeight e (X i)) n H
      (fun i _ => axisHeight_nn_le e X hX i) (by simp [h0,axisHeight_zero]) hn.ge
    have hr : j = 0 ∨ strictRecord (axisDirection e) X j := by
      by_cases hz : j = 0
      · exact Or.inl hz
      · refine Or.inr ⟨by omega,fun i hi => ?_⟩
        simp only [height_axisDirection]
        exact_mod_cast (show axisHeight e (X i) < axisHeight e (X j) by rw [hj];exact hmin i hi)
    refine Set.mem_iUnion.mpr ⟨j,hr,?_,?_⟩
    · have hc := axis_record_height e X j h0 (fun i _ => axisHeight_nn_le e X hX i) hr
      rw [hj] at hc
      exact_mod_cast hc.symm
    · intro i hi
      rw [height_axisDirection]
      exact_mod_cast hbelow i (hi.trans hjn)

lemma reachAxis_antitone {d : ℕ} (e : Step d) (X : Path d)
    (h0 : X 0 = 0) (hX : nearestNeighbour X) {m n : ℕ} (hmn : m ≤ n) :
    X ∈ reachAxis e n → X ∈ reachAxis e m := by
  rintro ⟨k,hk,hbelow⟩
  obtain ⟨j,hjk,hj,_⟩ := integer_first_crossing (fun i => axisHeight e (X i)) k m
    (fun i _ => axisHeight_nn_le e X hX i) (by simp [h0,axisHeight_zero])
    (by rw [hk];exact_mod_cast hmn)
  exact ⟨j,hj,fun i hi => hbelow i (hi.trans hjk)⟩

lemma last_record_cut_partition {d : ℕ} (v : Fin d → ℝ) (X : Path d)
    (h0 : X 0 = 0) (hD : X ∈ nonBacktracking v) (N : ℕ) :
    X ∈ ⋃ j ∈ Finset.range (N+1), recordTailEvent v j (noCutBeforeRecord v (N-j)) := by
  classical
  let s := (Finset.range (N+1)).filter (fun j => ∃ n, recordPrefix v j X n ∧
    relativeTail n X ∈ nonBacktracking v)
  have h0s : 0 ∈ s := by
    refine Finset.mem_filter.mpr ⟨by simp,0,⟨Or.inl rfl, recordCount_zero v X,?_⟩,?_⟩
    · intro i hi
      have : i = 0 := by omega
      rw [this,h0,height_zero]
    · intro k
      simpa [relativeTail_apply,height_sub,h0,height_zero] using hD k
  let j := s.max' ⟨0,h0s⟩
  have hjs := s.max'_mem ⟨0,h0s⟩
  obtain ⟨hj, n, hpre, htail⟩ := Finset.mem_filter.mp hjs
  have hjN : j ≤ N := by have := Finset.mem_range.mp hj; omega
  refine Set.mem_iUnion.mpr ⟨j,Set.mem_iUnion.mpr ⟨hj,Set.mem_iUnion.mpr ⟨n,hpre,?_,htail⟩⟩⟩
  intro m hm
  have hmpos := hm.1.1
  have hcut : trueCut v X (n+m) := (trueCut_relativeTail v X hpre.1 hm.1.1).mp hm
  have hcount := recordCount_relativeTail v X hpre.1 m
  rw [hpre.2.1] at hcount
  by_contra hlt
  have hk : recordCount v X (n+m) ≤ N := by omega
  have hk_mem : recordCount v X (n+m) ∈ s := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),n+m,?_,?_⟩
    · exact ⟨Or.inr hcut.1,rfl,fun i _ => hD i⟩
    · exact (relativeTail_nonBacktracking_iff v X (n+m)).mpr hcut.2
  have hle := s.le_max' (recordCount v X (n+m)) hk_mem
  have hgt := recordCount_strict v X (show n < n+m by omega) hcut.1
  rw [hpre.2.1] at hgt
  exact (not_lt_of_ge hle) hgt

lemma record_tail_sum_eq_one {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (v : Fin d → ℝ) (hp : 0 < annealed μ 0 (nonBacktracking v)) (N : ℕ) :
    ∑ j ∈ Finset.range (N+1), annealed μ 0 (reachRecord v j) *
      conditioned μ v (noCutBeforeRecord v (N-j)) = 1 := by
  let := conditioned_probability μ v hp
  calc
    _ = ∑ j ∈ Finset.range (N+1), conditioned μ v
        (recordTailEvent v j (noCutBeforeRecord v (N-j))) := by
      apply Finset.sum_congr rfl
      intro j _
      exact (recordTail_factorization μ v j (measurableSet_noCutBeforeRecord v (N-j))).symm
    _ = conditioned μ v (⋃ j ∈ Finset.range (N+1),
        recordTailEvent v j (noCutBeforeRecord v (N-j))) := by
      symm
      exact measure_biUnion_finset (recordTailEvent_disjoint v N)
        (fun j _ => measurableSet_recordTailEvent v j (measurableSet_noCutBeforeRecord v (N-j)))
    _ = 1 := by
      apply (mem_ae_iff_prob_eq_one (MeasurableSet.biUnion (Finset.countable_toSet _)
        (fun j _ => measurableSet_recordTailEvent v j (measurableSet_noCutBeforeRecord v (N-j))))).mp
      have h0 := (cond_absolutelyContinuous (s := nonBacktracking v) (μ := annealed μ 0)).ae_le
        (ae_start_and_nearestNeighbour μ 0)
      have hD : ∀ᵐ X ∂conditioned μ v, X ∈ nonBacktracking v :=
        ae_cond_mem (measurableSet_nonBacktracking v)
      filter_upwards [h0,hD] with X hX hXD
      exact last_record_cut_partition v X hX.1 hXD N

noncomputable def axisReachProb {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (e : Step d) (H : ℕ) : ℝ≥0∞ := annealed μ 0 (reachAxis e H)

lemma axisReachProb_eq_record {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (e : Step d) (H : ℕ) : axisReachProb μ e H = annealed μ 0 (reachRecord (axisDirection e) H) := by
  apply measure_congr
  filter_upwards [ae_start_and_nearestNeighbour μ 0] with X hX
  exact propext (reachRecord_eq_reachAxis e X hX.1 hX.2 H).symm

lemma axisReachProb_antitone {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (e : Step d) : Antitone (axisReachProb μ e) := by
  intro m n hmn
  apply measure_mono_ae
  filter_upwards [ae_start_and_nearestNeighbour μ 0] with X hX
  exact reachAxis_antitone e X hX.1 hX.2 hmn

lemma axisReachProb_lower {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d) (H : ℕ) :
    annealed μ 0 (nonBacktracking (axisDirection e)) ≤ axisReachProb μ e H := by
  rw [axisReachProb_eq_record]
  exact reachRecord_mass_ge μ hell (axisDirection e) (axisDirection_ne_zero e) H

lemma axisReachProb_zero {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (e : Step d) : axisReachProb μ e 0 = 1 := by
  apply (mem_ae_iff_prob_eq_one (measurableSet_reachAxis e 0)).mp
  filter_upwards [ae_start_and_nearestNeighbour μ 0] with X hX
  refine ⟨0,by rw [hX.1,axisHeight_zero]; rfl,?_⟩
  intro i hi
  have : i = 0 := by omega
  simp [this,hX.1,axisHeight_zero]

noncomputable def axisWidthTail {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (e : Step d) (H : ℕ) : ℝ≥0∞ :=
  slabLaw μ (axisDirection e) {γ | H < slabRecords (axisDirection e) γ}

lemma axis_renewal_tail_identity {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d)
    (hp : 0 < annealed μ 0 (nonBacktracking (axisDirection e))) (N : ℕ) :
    ∑ j ∈ Finset.range (N+1), axisReachProb μ e j * axisWidthTail μ e (N-j) = 1 := by
  simp_rw [axisReachProb_eq_record,axisWidthTail,
    slabRecords_tail μ hell (axisDirection e) (axisDirection_ne_zero e) hp]
  exact record_tail_sum_eq_one μ (axisDirection e) hp N

lemma slabRecords_pos {d : ℕ} (v : Fin d → ℝ) (γ : Word d) (hγ : RegenerationWord v γ) :
    0 < slabRecords v γ := by
  have hr : strictRecord v (wordPath γ) γ.1 :=
    ⟨hγ.1,fun j hj => (hγ.2.2.2.1 j hj).2⟩
  have hh := recordCount_strict v (wordPath γ) hγ.1 hr
  simpa only [recordCount_zero, slabRecords] using hh

lemma axis_slabWidth_eq_records {d : ℕ} (e : Step d) (γ : Word d)
    (hγ : RegenerationWord (axisDirection e) γ) :
    slabWidth (axisDirection e) γ = (slabRecords (axisDirection e) γ : ℝ) := by
  have hh := axis_record_height e (wordPath γ) γ.1 hγ.2.1 (fun j hj => by
    obtain ⟨f,hf⟩ := hγ.2.2.1 j hj
    rw [hf,axisHeight_add]
    exact add_le_add le_rfl (axisHeight_step_le e f))
    (Or.inr ⟨hγ.1,fun j hj => (hγ.2.2.2.1 j hj).2⟩)
  change height (axisDirection e) (wordPath γ γ.1) = _
  rw [height_axisDirection]
  exact_mod_cast hh

lemma axisWidthTail_zero {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d)
    (hp : 0 < annealed μ 0 (nonBacktracking (axisDirection e))) : axisWidthTail μ e 0 = 1 := by
  let := slabLaw_probability μ (axisDirection e) hp
  apply (mem_ae_iff_prob_eq_one (measurableSet_lt measurable_const (measurable_of_countable _))).mp
  filter_upwards [ae_slabLaw_regeneration μ hell (axisDirection e) (axisDirection_ne_zero e) hp] with γ hγ
  exact slabRecords_pos (axisDirection e) γ hγ

lemma axisWidthTail_antitone {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (e : Step d) : Antitone (axisWidthTail μ e) := by
  intro m n hmn
  exact measure_mono (fun _ hn => hmn.trans_lt hn)

lemma renewal_step_bound (u F : ℕ → ℝ) (hu : Antitone u) (hF : ∀ n, 0 ≤ F n)
    (hu0 : u 0 = 1) (hF0 : F 0 = 1)
    (hid : ∀ n, ∑ j ∈ Finset.range (n+1), u j * F (n-j) = 1) (n : ℕ) :
    u n - u (n+1) ≤ F (n+1) := by
  have hid' := hid (n+1)
  rw [Finset.sum_range_succ'] at hid'
  simp only [Nat.succ_sub_succ_eq_sub,hu0,one_mul,Nat.sub_zero] at hid'
  have heq : ∑ j ∈ Finset.range (n+1), (u j-u (j+1))*F (n-j) = F (n+1) := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib,hid n]
    linarith
  have hle := Finset.single_le_sum (s := Finset.range (n+1))
    (f := fun j => (u j-u (j+1))*F (n-j))
    (fun j _ => mul_nonneg (sub_nonneg.mpr (hu (Nat.le_succ j))) (hF (n-j)))
    (show n ∈ Finset.range (n+1) by simp)
  simpa only [Nat.sub_self,hF0,mul_one,heq] using hle

lemma renewal_interval_bound (u F : ℕ → ℝ) (hu : Antitone u) (hF : Antitone F)
    (hstep : ∀ n, u n-u (n+1) ≤ F (n+1)) {n m : ℕ} (hnm : n ≤ m) :
    0 ≤ u n-u m ∧ u n-u m ≤ (m-n)*F n := by
  refine ⟨sub_nonneg.mpr (hu hnm),?_⟩
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hnm
  simp only [Nat.cast_add, add_sub_cancel_left]
  induction k with
  | zero => simp
  | succ k ih =>
    have ih := ih (by omega)
    have hs := (hstep (n+k)).trans (hF (show n ≤ n+k+1 by omega))
    have he : n+(k+1) = n+k+1 := by omega
    rw [he,Nat.cast_add,Nat.cast_one]
    nlinarith

lemma axis_renewal_identity_real {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d)
    (hp : 0 < annealed μ 0 (nonBacktracking (axisDirection e))) (N : ℕ) :
    ∑ j ∈ Finset.range (N+1), (axisReachProb μ e j).toReal *
      (axisWidthTail μ e (N-j)).toReal = 1 := by
  let := slabLaw_probability μ (axisDirection e) hp
  have h := congrArg ENNReal.toReal (axis_renewal_tail_identity μ hell e hp N)
  rw [ENNReal.toReal_sum (f := fun j => axisReachProb μ e j * axisWidthTail μ e (N-j))
    (fun j _ => ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _))] at h
  simpa only [ENNReal.toReal_mul,ENNReal.toReal_one] using h

lemma axis_renewal_tail_bound {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d)
    (hp : 0 < annealed μ 0 (nonBacktracking (axisDirection e))) {n m : ℕ} (hnm : n ≤ m) :
    0 ≤ (axisReachProb μ e n).toReal-(axisReachProb μ e m).toReal ∧
      (axisReachProb μ e n).toReal-(axisReachProb μ e m).toReal ≤
        (m-n)*(axisWidthTail μ e n).toReal := by
  let := slabLaw_probability μ (axisDirection e) hp
  have hu : Antitone (fun n => (axisReachProb μ e n).toReal) :=
    fun _ _ h => ENNReal.toReal_mono (measure_ne_top _ _) (axisReachProb_antitone μ e h)
  have hF : Antitone (fun n => (axisWidthTail μ e n).toReal) :=
    fun _ _ h => ENNReal.toReal_mono (measure_ne_top _ _) (axisWidthTail_antitone μ e h)
  apply renewal_interval_bound _ _ hu hF _ hnm
  intro k
  apply renewal_step_bound _ _ hu (fun _ => ENNReal.toReal_nonneg) _ _
    (axis_renewal_identity_real μ hell e hp) k
  · rw [axisReachProb_zero,ENNReal.toReal_one]
  · rw [axisWidthTail_zero μ hell e hp,ENNReal.toReal_one]

lemma summable_axisWidthTail {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d)
    (hp : 0 < annealed μ 0 (nonBacktracking (axisDirection e))) :
    Summable (fun n => (axisWidthTail μ e n).toReal) := by
  apply ENNReal.summable_toReal
  change (∑' n, slabLaw μ (axisDirection e) {γ | n < slabRecords (axisDirection e) γ}) ≠ ⊤
  rw [← lintegral_nat_tail _ _ (measurable_of_countable _)]
  exact ((lintegral_slabRecords_le μ hell (axisDirection e) (axisDirection_ne_zero e) hp).trans_lt
    (ENNReal.inv_lt_top.mpr hp)).ne

lemma summable_dyadic_axisWidthTail {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d)
    (hp : 0 < annealed μ 0 (nonBacktracking (axisDirection e))) :
    Summable (fun l => (2:ℝ)^l*(axisWidthTail μ e (2^l)).toReal) := by
  let := slabLaw_probability μ (axisDirection e) hp
  apply (summable_condensed_iff_of_nonneg (fun _ => ENNReal.toReal_nonneg) (fun _ _ _ h =>
    ENNReal.toReal_mono (measure_ne_top _ _) (axisWidthTail_antitone μ e h))).mpr
  exact summable_axisWidthTail μ hell e hp

lemma iterated_cutSuffix_eq_relativeTail {d : ℕ} (v : Fin d → ℝ) (X : Path d)
    (h0 : X 0 = 0) (k : ℕ) : (cutSuffix v)^[k] X = relativeTail (slabTime v X k) X := by
  funext n
  exact iterated_cutSuffix v X h0 k n

lemma slabTime_boundary {d : ℕ} (v : Fin d → ℝ) (X : Path d) (hX : GoodSlabPath v X)
    (k : ℕ) : slabTime v X k = 0 ∨ trueCut v X (slabTime v X k) := by
  induction k with
  | zero => exact Or.inl (slabTime_zero v X)
  | succ k ih =>
    right
    have hp : 0 < firstCutTime v ((cutSuffix v)^[k] X) := (hX.2 k).1
    have hc := ((firstCutTime_eq_pos_iff v ((cutSuffix v)^[k] X) hp).mp rfl).1
    have hc' : trueCut v (relativeTail (slabTime v X k) X) (slabs v X k).1 := by
      rw [← iterated_cutSuffix_eq_relativeTail v X hX.1 k]
      exact hc
    rw [slabTime_succ]
    exact (trueCut_relativeTail v X (ih.imp_right And.left) hp).mp hc'

lemma trueCut_eq_slabTime {d : ℕ} (v : Fin d → ℝ) (X : Path d) (hX : GoodSlabPath v X)
    {n : ℕ} (hn : trueCut v X n) : ∃ k, slabTime v X k = n := by
  obtain ⟨k,hkn,hnk⟩ := slab_location v X hX n
  refine ⟨k,?_⟩
  by_contra hne
  have hlt : slabTime v X k < n := lt_of_le_of_ne hkn hne
  have hc : trueCut v (relativeTail (slabTime v X k) X) (n-slabTime v X k) := by
    apply (trueCut_relativeTail v X ((slabTime_boundary v X hX k).imp_right And.left)
      (Nat.sub_pos_of_lt hlt)).mpr
    simpa only [Nat.add_sub_of_le hkn] using hn
  rw [← iterated_cutSuffix_eq_relativeTail v X hX.1 k] at hc
  have hp : 0 < firstCutTime v ((cutSuffix v)^[k] X) := (hX.2 k).1
  have hm := ((firstCutTime_eq_pos_iff v ((cutSuffix v)^[k] X) hp).mp rfl).2
  apply hm (n-slabTime v X k) _ hc
  rw [slabTime_succ] at hnk
  change n-slabTime v X k < (slabs v X k).1
  omega

lemma recordCount_slabTime {d : ℕ} (v : Fin d → ℝ) (X : Path d) (hX : GoodSlabPath v X)
    (k : ℕ) : recordCount v X (slabTime v X k) =
      ∑ i ∈ Finset.range k, slabRecords v (slabs v X i) := by
  induction k with
  | zero => simp [slabTime_zero,recordCount_zero]
  | succ k ih =>
    rw [slabTime_succ,recordCount_relativeTail v X
      ((slabTime_boundary v X hX k).imp_right And.left),ih,Finset.sum_range_succ]
    congr 1
    rw [← iterated_cutSuffix_eq_relativeTail v X hX.1 k]
    exact (slabRecords_firstWord v ((cutSuffix v)^[k] X)).symm

def tapeCut {d : ℕ} (v : Fin d → ℝ) (H : ℕ) : Set (ℕ → Word d) :=
  {Z | ∃ k, ∑ i ∈ Finset.range k, slabRecords v (Z i) = H}

lemma measurableSet_tapeCut {d : ℕ} (v : Fin d → ℝ) (H : ℕ) :
    MeasurableSet (tapeCut v H) := by
  simp only [tapeCut,Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro k
  exact measurableSet_eq_fun (Finset.measurable_sum _ (fun i _ =>
    (measurable_of_countable (slabRecords v)).comp (measurable_pi_apply i))) measurable_const

lemma tapeCut_iff_recordTailEvent {d : ℕ} (v : Fin d → ℝ) (X : Path d)
    (hX : GoodSlabPath v X) (H : ℕ) :
    slabs v X ∈ tapeCut v H ↔ X ∈ recordTailEvent v H Set.univ := by
  have hD : X ∈ nonBacktracking v := fun t => goodSlabPath_height_nonneg v X hX t
  constructor
  · rintro ⟨k,hk⟩
    have hb := slabTime_boundary v X hX k
    refine Set.mem_iUnion.mpr ⟨slabTime v X k,⟨hb.imp_right And.left,?_,fun i _ => hD i⟩,
      Set.mem_univ _,?_⟩
    · rw [recordCount_slabTime v X hX k,hk]
    · rcases hb with hz | hc
      · intro i
        simpa [relativeTail_apply,hz,hX.1,height_sub,height_zero] using hD i
      · exact (relativeTail_nonBacktracking_iff v X _).mpr hc.2
  · intro ht
    obtain ⟨n,hn,_,hD'⟩ := Set.mem_iUnion.mp ht
    have hncut : n = 0 ∨ trueCut v X n := hn.1.imp_right
      (fun hr => ⟨hr,(relativeTail_nonBacktracking_iff v X n).mp hD'⟩)
    have hk : ∃ k, slabTime v X k = n := by
      rcases hncut with hz | hc
      · exact ⟨0,(slabTime_zero v X).trans hz.symm⟩
      · exact trueCut_eq_slabTime v X hX hc
    obtain ⟨k,rfl⟩ := hk
    refine ⟨k,?_⟩
    rw [← recordCount_slabTime v X hX k]
    exact hn.2.1

lemma tapeCut_mass {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) (H : ℕ) :
    Measure.infinitePi (fun _ : ℕ => slabLaw μ v) (tapeCut v H) =
      annealed μ 0 (reachRecord v H) := by
  let := conditioned_probability μ v hp
  rw [← slabs_map_eq_infinitePi μ hell v hv hp,
    Measure.map_apply (measurable_slabs v) (measurableSet_tapeCut v H)]
  have he : conditioned μ v (slabs v ⁻¹' tapeCut v H) =
      conditioned μ v (recordTailEvent v H Set.univ) := by
    apply measure_congr
    filter_upwards [ae_goodSlabPath μ hell v hv hp] with X hX
    exact propext (tapeCut_iff_recordTailEvent v X hX H)
  rw [he,recordTail_factorization μ v H MeasurableSet.univ,measure_univ,mul_one]

lemma axis_tapeCut_mass {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d)
    (hp : 0 < annealed μ 0 (nonBacktracking (axisDirection e))) (H : ℕ) :
    Measure.infinitePi (fun _ : ℕ => slabLaw μ (axisDirection e)) (tapeCut (axisDirection e) H) =
      axisReachProb μ e H := by
  rw [tapeCut_mass μ hell _ (axisDirection_ne_zero e) hp,axisReachProb_eq_record]

end DirectionalZeroOne

end OAI

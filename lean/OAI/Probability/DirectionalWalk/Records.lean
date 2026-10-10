import OAI.Probability.DirectionalWalk.Slabs

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

lemma height_sub {d : ℕ} (v : Fin d → ℝ) (x y : Site d) :
    height v (x-y) = height v x - height v y := by
  rw [sub_eq_add_neg,height_add,height_neg,sub_eq_add_neg]

noncomputable def recordCount {d : ℕ} (v : Fin d → ℝ) (X : Path d) (n : ℕ) : ℕ :=
  (Finset.range (n+1)).filter (strictRecord v X) |>.card

lemma recordCount_zero {d : ℕ} (v : Fin d → ℝ) (X : Path d) : recordCount v X 0 = 0 := by
  classical
  simp [recordCount,strictRecord]

lemma recordCount_succ {d : ℕ} (v : Fin d → ℝ) (X : Path d) (n : ℕ) :
    recordCount v X (n+1) = recordCount v X n + if strictRecord v X (n+1) then 1 else 0 := by
  classical
  rw [recordCount,Finset.range_add_one,Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem]
    · rfl
    · simp
  · rfl

lemma recordCount_mono {d : ℕ} (v : Fin d → ℝ) (X : Path d) : Monotone (recordCount v X) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [recordCount_succ]
  exact Nat.le_add_right _ _

lemma recordCount_prefix {d : ℕ} (v : Fin d → ℝ) {X Y : Path d} {n : ℕ}
    (h : Y ∈ pathCylinder n X) : recordCount v Y n = recordCount v X n := by
  classical
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro i hi
  have hin : i ≤ n := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hi
  constructor <;> intro hr
  · exact strictRecord_prefix v hr (fun j hj => (h j (hj.trans hin)).symm)
  · exact strictRecord_prefix v hr (fun j hj => h j (hj.trans hin))

lemma measurable_recordCount {d : ℕ} (v : Fin d → ℝ) (n : ℕ) :
    Measurable (fun X : Path d => recordCount v X n) := by
  classical
  induction n with
  | zero => simpa only [recordCount_zero] using (measurable_const : Measurable (fun _ : Path d => (0 : ℕ)))
  | succ n ih =>
    simp_rw [recordCount_succ]
    exact ih.add (Measurable.ite (measurableSet_strictRecord v (n+1)) measurable_const measurable_const)

lemma recordCount_strict {d : ℕ} (v : Fin d → ℝ) (X : Path d) {m n : ℕ}
    (hmn : m < n) (hn : strictRecord v X n) : recordCount v X m < recordCount v X n := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn.1)
  rw [recordCount_succ,ite_eq_left hn]
  exact Nat.lt_succ_of_le (recordCount_mono v X (by omega))

lemma recordCount_boundary_unique {d : ℕ} (v : Fin d → ℝ) (X : Path d) {m n : ℕ}
    (hm : m = 0 ∨ strictRecord v X m) (hn : n = 0 ∨ strictRecord v X n)
    (he : recordCount v X m = recordCount v X n) : m = n := by
  rcases lt_trichotomy m n with h|h|h
  · have hnr : strictRecord v X n := hn.resolve_left (by omega)
    exact False.elim ((ne_of_lt (recordCount_strict v X h hnr)) he)
  · exact h
  · have hmr : strictRecord v X m := hm.resolve_left (by omega)
    exact False.elim ((ne_of_lt (recordCount_strict v X h hmr)) he.symm)

lemma unbounded_recordCount {d : ℕ} (v : Fin d → ℝ) (X : Path d)
    (hu : ¬∃ b : ℝ, ∀ n, height v (X n) ≤ b) : ∀ j, ∃ n, j ≤ recordCount v X n := by
  intro j
  induction j with
  | zero => exact ⟨0,Nat.zero_le _⟩
  | succ j ih =>
    obtain ⟨m,hm⟩ := ih
    obtain ⟨n,hmn,hn⟩ := unbounded_has_later_strictRecord v X hu m
    exact ⟨n,Nat.succ_le_of_lt (hm.trans_lt (recordCount_strict v X hmn hn))⟩

lemma exists_record_index {d : ℕ} (v : Fin d → ℝ) (X : Path d)
    (hu : ¬∃ b : ℝ, ∀ n, height v (X n) ≤ b) (j : ℕ) :
    ∃ n, (n = 0 ∨ strictRecord v X n) ∧ recordCount v X n = j := by
  classical
  by_cases hj : j = 0
  · exact ⟨0,Or.inl rfl,by rw [recordCount_zero,hj]⟩
  have hex := unbounded_recordCount v X hu j
  let n := Nat.find hex
  have hn : j ≤ recordCount v X n := Nat.find_spec hex
  have hn0 : 0 < n := by
    by_contra h
    have he : n = 0 := by omega
    rw [he,recordCount_zero] at hn
    omega
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn0)
  have hprev : recordCount v X k < j := Nat.lt_of_not_ge (Nat.find_min hex (by omega : k < n))
  rw [hk,recordCount_succ] at hn
  split_ifs at hn with hr
  · exact ⟨n,Or.inr (by simpa only [hk] using hr),by rw [hk,recordCount_succ,ite_eq_left hr]; omega⟩
  · omega

def relativeTail {d : ℕ} (n : ℕ) (X : Path d) : Path d :=
  shiftPath (-(X n)) (tailPath n X)

lemma relativeTail_apply {d : ℕ} (n : ℕ) (X : Path d) (k : ℕ) :
    relativeTail n X k = X (n+k) - X n := rfl

lemma relativeTail_zero {d : ℕ} (n : ℕ) (X : Path d) : relativeTail n X 0 = 0 := by
  simp [relativeTail_apply]

lemma measurable_relativeTail {d : ℕ} (n : ℕ) : Measurable (relativeTail (d := d) n) := by
  apply Measurable.of_eval
  intro k
  change Measurable (fun X : Path d => X (n+k) - X n)
  exact (measurable_pi_apply (n+k)).sub (measurable_pi_apply n)

lemma strictRecord_relativeTail {d : ℕ} (v : Fin d → ℝ) (X : Path d) {n : ℕ}
    (hn : n = 0 ∨ strictRecord v X n) {k : ℕ} (hk : 0 < k) :
    strictRecord v (relativeTail n X) k ↔ strictRecord v X (n+k) := by
  change (0 < k ∧ ∀ i < k, height v (X (n+i) - X n) < height v (X (n+k) - X n)) ↔ _
  simp_rw [height_sub]
  constructor
  · rintro ⟨_,hr⟩
    refine ⟨by omega,fun i hi => ?_⟩
    by_cases hin : n ≤ i
    · have hh := hr (i-n) (by omega)
      rw [Nat.add_sub_of_le hin] at hh
      linarith
    · have hh := hr 0 hk
      rw [Nat.add_zero] at hh
      have hi' : i < n := by omega
      have hnr := hn.resolve_left (by omega)
      exact (hnr.2 i hi').trans (by linarith)
  · intro hr
    refine ⟨hk,fun i hi => ?_⟩
    have hh := hr.2 (n+i) (by omega)
    linarith

lemma trueCut_relativeTail {d : ℕ} (v : Fin d → ℝ) (X : Path d) {n : ℕ}
    (hn : n = 0 ∨ strictRecord v X n) {k : ℕ} (hk : 0 < k) :
    trueCut v (relativeTail n X) k ↔ trueCut v X (n+k) := by
  rw [trueCut,trueCut,strictRecord_relativeTail v X hn hk]
  simp only [relativeTail_apply,height_sub,Nat.add_assoc,sub_le_sub_iff_right]

lemma recordCount_relativeTail {d : ℕ} (v : Fin d → ℝ) (X : Path d) {n : ℕ}
    (hn : n = 0 ∨ strictRecord v X n) (k : ℕ) :
    recordCount v X (n+k) = recordCount v X n + recordCount v (relativeTail n X) k := by
  classical
  induction k with
  | zero => simp [recordCount_zero]
  | succ k ih =>
    rw [Nat.add_succ,recordCount_succ,recordCount_succ,ih,
      strictRecord_relativeTail v X hn (Nat.succ_pos k),Nat.add_assoc]
    simp only [Nat.succ_eq_add_one,Nat.add_assoc]

def noCutBeforeRecord {d : ℕ} (v : Fin d → ℝ) (r : ℕ) : Set (Path d) :=
  {X | ∀ n, trueCut v X n → r < recordCount v X n}

lemma measurableSet_noCutBeforeRecord {d : ℕ} (v : Fin d → ℝ) (r : ℕ) :
    MeasurableSet (noCutBeforeRecord v r) := by
  simp only [noCutBeforeRecord,Set.ofPred_forall,imp_iff_not_or,Set.ofPred_or]
  exact MeasurableSet.iInter (fun n => (measurableSet_trueCut v n).compl.union
    (measurableSet_lt measurable_const (measurable_recordCount v n)))

lemma noCutBeforeRecord_iff {d : ℕ} (v : Fin d → ℝ) (X : Path d)
    (hc : ∃ n, trueCut v X n) (r : ℕ) : X ∈ noCutBeforeRecord v r ↔
      r < recordCount v X (firstCutTime v X) := by
  obtain ⟨hcut,hmin⟩ := firstCutTime_spec v X hc
  constructor
  · intro h; exact h _ hcut
  · intro h n hn
    have ht : firstCutTime v X ≤ n := by
      by_contra hx
      exact hmin n (by omega) hn
    exact h.trans_le (recordCount_mono v X ht)

def recordPrefix {d : ℕ} (v : Fin d → ℝ) (j : ℕ) (X : Path d) (n : ℕ) : Prop :=
  (n = 0 ∨ strictRecord v X n) ∧ recordCount v X n = j ∧
    ∀ i ≤ n, 0 ≤ height v (X i)

lemma recordPrefix_prefix {d : ℕ} (v : Fin d → ℝ) (j : ℕ) {X Y : Path d} {n : ℕ}
    (hX : recordPrefix v j X n) (hY : Y ∈ pathCylinder n X) : recordPrefix v j Y n := by
  refine ⟨hX.1.imp id (fun hr => strictRecord_prefix v hr hY),?_,fun i hi => ?_⟩
  · rw [recordCount_prefix v hY];exact hX.2.1
  · rw [hY i hi];exact hX.2.2 i hi

lemma recordPrefix_unique {d : ℕ} (v : Fin d → ℝ) (j : ℕ) (X : Path d) {m n : ℕ}
    (hm : recordPrefix v j X m) (hn : recordPrefix v j X n) : m = n :=
  recordCount_boundary_unique v X hm.1 hn.1 (hm.2.1.trans hn.2.1.symm)

lemma measurableSet_recordPrefix {d : ℕ} (v : Fin d → ℝ) (j n : ℕ) :
    MeasurableSet {X : Path d | recordPrefix v j X n} := by
  simp only [recordPrefix,Set.ofPred_and,Set.ofPred_or,Set.ofPred_forall]
  refine ((MeasurableSet.const _).union (measurableSet_strictRecord v n)).inter
    (((measurableSet_singleton j).preimage (measurable_recordCount v n)).inter ?_)
  exact MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun _ =>
    measurableSet_le measurable_const ((measurable_of_countable (height v)).comp (measurable_pi_apply i))))

lemma relativeTail_nonBacktracking_iff {d : ℕ} (v : Fin d → ℝ) (X : Path d) (n : ℕ) :
    relativeTail n X ∈ nonBacktracking v ↔ ∀ k, height v (X n) ≤ height v (X (n+k)) := by
  simp only [nonBacktracking,neverBelow,Set.mem_ofPred_eq,relativeTail_apply,height_sub,sub_nonneg]

lemma recordPrefix_tail_subset_nonBacktracking {d : ℕ} (v : Fin d → ℝ) (j n : ℕ)
    (X : Path d) (hpre : recordPrefix v j X n) (hD : relativeTail n X ∈ nonBacktracking v) :
    X ∈ nonBacktracking v := by
  intro k
  by_cases hk : k ≤ n
  · exact hpre.2.2 k hk
  · have hh := (relativeTail_nonBacktracking_iff v X n).mp hD (k-n)
    rw [Nat.add_sub_of_le (by omega : n ≤ k)] at hh
    exact (hpre.2.2 n le_rfl).trans hh

lemma relativeTail_cylinder {d : ℕ} (n : ℕ) (X γ : Path d)
    (h : X ∈ pathCylinder n γ) : relativeTail n X = shiftPath (-(γ n)) (tailPath n X) := by
  rw [relativeTail,h n le_rfl]

lemma conditioned_recordCylinder {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (v : Fin d → ℝ) (j n : ℕ) (γ : Path d) (hγ : recordPrefix v j γ n)
    {E : Set (Path d)} (hE : MeasurableSet E) :
    conditioned μ v (pathCylinder n γ ∩ relativeTail n ⁻¹' (E ∩ nonBacktracking v)) =
      annealed μ 0 (pathCylinder n γ) * conditioned μ v E := by
  have hsub : pathCylinder n γ ∩ relativeTail n ⁻¹' (E ∩ nonBacktracking v) ⊆ nonBacktracking v := by
    rintro X ⟨hX,hY⟩
    exact recordPrefix_tail_subset_nonBacktracking v j n X (recordPrefix_prefix v j hγ hX) hY.2
  have heq : pathCylinder n γ ∩ relativeTail n ⁻¹' (E ∩ nonBacktracking v) =
      pathCylinder n γ ∩ tailPath n ⁻¹' (shiftPath (-(γ n)) ⁻¹' (E ∩ nonBacktracking v)) := by
    ext X
    constructor <;> rintro ⟨hX,hY⟩ <;> refine ⟨hX,?_⟩
    · simpa only [Set.mem_preimage,relativeTail_cylinder n X γ hX] using hY
    · simpa only [Set.mem_preimage,relativeTail_cylinder n X γ hX] using hY
  change (annealed μ 0)[_|nonBacktracking v] = _
  rw [cond_apply (measurableSet_nonBacktracking v),Set.inter_eq_right.mpr hsub,heq,
    annealed_record_relative_tail μ v 0 n γ (fun i hi => ?_) hE]
  · unfold conditioned
    rw [cond_apply (measurableSet_nonBacktracking v),Set.inter_comm (nonBacktracking v) E]
    ac_rfl
  · exact (hγ.1.resolve_left (by omega)).2 i hi

lemma conditioned_recordPrefix {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (v : Fin d → ℝ) (j n : ℕ) {E : Set (Path d)} (hE : MeasurableSet E) :
    conditioned μ v ({X | recordPrefix v j X n} ∩ relativeTail n ⁻¹' (E ∩ nonBacktracking v)) =
      annealed μ 0 {X | recordPrefix v j X n} * conditioned μ v E := by
  let B : Set (Path d) := {X | recordPrefix v j X n}
  have hB := measurableSet_recordPrefix v j n
  have hF := (measurable_relativeTail n) (hE.inter (measurableSet_nonBacktracking v))
  rw [measure_eq_tsum_fibres (conditioned μ v) (frestrictLe n) (measurable_frestrictLe n) (hB.inter hF),
    measure_eq_tsum_fibres (annealed μ 0) (frestrictLe n) (measurable_frestrictLe n) hB,
    ← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro a
  let γ := extendPrefix n a
  have hcyl : {X : Path d | frestrictLe n X = a} = pathCylinder n γ := by
    rw [pathCylinder_eq_fiber,restrict_extendPrefix]
    rfl
  rw [hcyl]
  by_cases hγ : recordPrefix v j γ n
  · have hsub : pathCylinder n γ ⊆ B := fun _ h => recordPrefix_prefix v j hγ h
    have heq : pathCylinder n γ ∩ ({X | recordPrefix v j X n} ∩ relativeTail n ⁻¹' (E ∩ nonBacktracking v)) =
        pathCylinder n γ ∩ relativeTail n ⁻¹' (E ∩ nonBacktracking v) := by
      rw [← Set.inter_assoc,Set.inter_eq_left.mpr hsub]
    rw [heq,Set.inter_eq_left.mpr hsub]
    exact conditioned_recordCylinder μ v j n γ hγ hE
  · have hdis : pathCylinder n γ ∩ B = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro X ⟨hX,hB'⟩
      exact hγ (recordPrefix_prefix v j hB' (fun i hi => (hX i hi).symm))
    rw [← Set.inter_assoc,hdis,Set.empty_inter,measure_empty,measure_empty,zero_mul]

def reachRecord {d : ℕ} (v : Fin d → ℝ) (j : ℕ) : Set (Path d) :=
  ⋃ n, {X | recordPrefix v j X n}

def recordTailEvent {d : ℕ} (v : Fin d → ℝ) (j : ℕ) (E : Set (Path d)) : Set (Path d) :=
  ⋃ n, {X | recordPrefix v j X n} ∩ relativeTail n ⁻¹' (E ∩ nonBacktracking v)

lemma measurableSet_reachRecord {d : ℕ} (v : Fin d → ℝ) (j : ℕ) :
    MeasurableSet (reachRecord v j) := MeasurableSet.iUnion (fun n => measurableSet_recordPrefix v j n)

lemma measurableSet_recordTailEvent {d : ℕ} (v : Fin d → ℝ) (j : ℕ)
    {E : Set (Path d)} (hE : MeasurableSet E) : MeasurableSet (recordTailEvent v j E) :=
  MeasurableSet.iUnion (fun n => (measurableSet_recordPrefix v j n).inter
    ((measurable_relativeTail n) (hE.inter (measurableSet_nonBacktracking v))))

lemma recordPrefix_disjoint {d : ℕ} (v : Fin d → ℝ) (j : ℕ) :
    Pairwise (fun m n => Disjoint {X : Path d | recordPrefix v j X m}
      {X : Path d | recordPrefix v j X n}) := by
  intro m n hmn
  apply Set.disjoint_left.mpr
  intro X hm hn
  exact hmn (recordPrefix_unique v j X hm hn)

lemma recordTail_factorization {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (v : Fin d → ℝ) (j : ℕ) {E : Set (Path d)} (hE : MeasurableSet E) :
    conditioned μ v (recordTailEvent v j E) = annealed μ 0 (reachRecord v j) * conditioned μ v E := by
  rw [recordTailEvent,measure_iUnion (fun m n hmn =>
    (recordPrefix_disjoint v j hmn).mono Set.inter_subset_left Set.inter_subset_left)
      (fun n => (measurableSet_recordPrefix v j n).inter
        ((measurable_relativeTail n) (hE.inter (measurableSet_nonBacktracking v))))]
  simp_rw [conditioned_recordPrefix μ v j _ hE,ENNReal.tsum_mul_right]
  rw [reachRecord,measure_iUnion (recordPrefix_disjoint v j) (measurableSet_recordPrefix v j)]

lemma reachRecord_mass_ge {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0) (j : ℕ) :
    annealed μ 0 (nonBacktracking v) ≤ annealed μ 0 (reachRecord v j) := by
  apply measure_mono_ae
  filter_upwards [finite_supremum μ hell 0 v hv] with X hfin hD
  have hu : ¬∃ b : ℝ, ∀ n, height v (X n) ≤ b := by
    intro hb
    obtain ⟨n,hn⟩ := eventually_atTop.mp ((hfin hb).eventually (eventually_lt_atBot (-1)))
    have hh := hD n
    have := hn n le_rfl
    linarith
  obtain ⟨n,hn,hj⟩ := exists_record_index v X hu j
  exact Set.mem_iUnion.mpr ⟨n,hn,hj,fun i _ => hD i⟩

lemma recordTailEvent_disjoint {d : ℕ} (v : Fin d → ℝ) (N : ℕ) :
    (Finset.range (N+1) : Set ℕ).Pairwise (fun j k =>
      Disjoint (recordTailEvent v j (noCutBeforeRecord v (N-j)))
        (recordTailEvent v k (noCutBeforeRecord v (N-k)))) := by
  intro j hj k hk hjk
  simp only [Finset.mem_coe,Finset.mem_range] at hj hk
  wlog hlt : j < k generalizing j k
  · exact (this hjk.symm hk hj (by omega)).symm
  apply Set.disjoint_left.mpr
  intro X hX hY
  obtain ⟨m,hm,hM⟩ := Set.mem_iUnion.mp hX
  obtain ⟨n,hn,hN⟩ := Set.mem_iUnion.mp hY
  have hmn : m < n := by
    by_contra h
    have hcount := recordCount_mono v X (show n ≤ m by omega)
    rw [hm.2.1,hn.2.1] at hcount
    omega
  have hnpos : 0 < n := by omega
  have hncut : trueCut v X n := ⟨hn.1.resolve_left (Nat.ne_of_gt hnpos),
    (relativeTail_nonBacktracking_iff v X n).mp hN.2⟩
  have hsuf : trueCut v (relativeTail m X) (n-m) := by
    apply (trueCut_relativeTail v X hm.1 (by omega)).mpr
    simpa only [Nat.add_sub_of_le hmn.le] using hncut
  have hcontra := hM.1 (n-m) hsuf
  have hcount := recordCount_relativeTail v X hm.1 (n-m)
  rw [Nat.add_sub_of_le hmn.le,hm.2.1,hn.2.1] at hcount
  omega

lemma record_tail_sum_bound {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (v : Fin d → ℝ) (hv : v ≠ 0)
    (hp : 0 < annealed μ 0 (nonBacktracking v)) (N : ℕ) :
    annealed μ 0 (nonBacktracking v) *
      ∑ j ∈ Finset.range (N+1), conditioned μ v (noCutBeforeRecord v (N-j)) ≤ 1 := by
  let := conditioned_probability μ v hp
  calc
    _ = ∑ j ∈ Finset.range (N+1), annealed μ 0 (nonBacktracking v) *
        conditioned μ v (noCutBeforeRecord v (N-j)) := Finset.mul_sum ..
    _ ≤ ∑ j ∈ Finset.range (N+1), conditioned μ v
        (recordTailEvent v j (noCutBeforeRecord v (N-j))) := by
      apply Finset.sum_le_sum
      intro j _
      rw [recordTail_factorization μ v j (measurableSet_noCutBeforeRecord v (N-j))]
      exact mul_le_mul' (reachRecord_mass_ge μ hell v hv j) le_rfl
    _ = conditioned μ v (⋃ j ∈ Finset.range (N+1),
        recordTailEvent v j (noCutBeforeRecord v (N-j))) := by
      symm
      exact measure_biUnion_finset (recordTailEvent_disjoint v N)
        (fun j _ => measurableSet_recordTailEvent v j (measurableSet_noCutBeforeRecord v (N-j)))
    _ ≤ 1 := prob_le_one

lemma lintegral_nat_tail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f : Ω → ℕ) (hf : Measurable f) :
    (∫⁻ x, (f x : ℝ≥0∞) ∂P) = ∑' j : ℕ, P {x | j < f x} := by
  classical
  have hA (j : ℕ) : MeasurableSet {x | j < f x} := measurableSet_lt measurable_const hf
  have hexp (x : Ω) : (f x : ℝ≥0∞) = ∑' j : ℕ, ({x | j < f x}.indicator (fun _ => (1 : ℝ≥0∞))) x := by
    rw [tsum_eq_sum (s := Finset.range (f x))]
    · symm
      calc
        _ = ∑ _j ∈ Finset.range (f x), (1 : ℝ≥0∞) := by
          apply Finset.sum_congr rfl
          intro j hj
          simp only [Set.indicator_apply, Set.mem_ofPred_eq, ite_eq_left (Finset.mem_range.mp hj)]
        _ = _ := by simp
    · intro j hj
      simp only [Finset.mem_range, not_lt] at hj
      simp [Set.indicator_of_notMem, not_lt.mpr hj]
  simp_rw [hexp,lintegral_tsum (fun j => (measurable_const.indicator (hA j)).aemeasurable)]
  apply tsum_congr
  intro j
  simp [lintegral_indicator (hA j)]

end DirectionalZeroOne

end OAI

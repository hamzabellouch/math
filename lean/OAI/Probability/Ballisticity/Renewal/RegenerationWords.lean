import Mathlib
import OAI.Probability.Ballisticity.Estimates.FirstWordEvent

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma identDistrib_iterated_symbol {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (F : α → β) (T : α → α)
    (hF : Measurable F) (hT : MeasurePreserving T μ μ) (n : ℕ) :
    IdentDistrib (fun x => F (T^[n] x)) F μ μ := by
  refine ⟨(hF.comp (hT.iterate n).measurable).aemeasurable, hF.aemeasurable, ?_⟩
  change μ.map (F ∘ T^[n]) = μ.map F
  rw [← Measure.map_map hF (hT.iterate n).measurable, (hT.iterate n).map_eq]

noncomputable def regenerationWords {d : ℕ} (ℓ : Vector d) (X : Path d) (n : ℕ) :
    List (Direction d) := firstWord ℓ ((renewSuffix ℓ)^[n] X)

lemma measurable_regenerationWord {d : ℕ} (ℓ : Vector d) (n : ℕ) :
    Measurable (fun X : Path d => regenerationWords ℓ X n) :=
  (measurable_firstWord ℓ).comp ((measurable_renewSuffix ℓ).iterate n)

lemma regenerationWords_independent {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) :
    iIndepFun (fun n X => regenerationWords ℓ X n) (conditionedLaw ν ℓ) := by
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ
    (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
  exact independent_iterated_symbols _ _ _ (measurable_firstWord ℓ)
    (renewSuffix_preserves_conditioned ν ℓ htrans) (firstWord_indep_renewSuffix ν ℓ htrans)

lemma regenerationWords_identDistrib {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) (n : ℕ) :
    IdentDistrib (fun X => regenerationWords ℓ X n) (firstWord ℓ)
      (conditionedLaw ν ℓ) (conditionedLaw ν ℓ) :=
  identDistrib_iterated_symbol _ _ _ (measurable_firstWord ℓ)
    (renewSuffix_preserves_conditioned ν ℓ htrans) n

lemma firstWordEvent_self {d : ℕ} (ℓ : Vector d) (X : Path d)
    (hX : ∃ w, X ∈ FirstWordEvent ℓ w) : X ∈ FirstWordEvent ℓ (firstWord ℓ X) := by
  classical
  simpa only [firstWord, dite_eq_left hX] using hX.choose_spec

noncomputable def regenerationTimes {d : ℕ} (ℓ : Vector d) (X : Path d) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, (regenerationWords ℓ X i).length

@[simp] lemma regenerationTimes_zero {d : ℕ} (ℓ : Vector d) (X : Path d) :
    regenerationTimes ℓ X 0 = 0 := by simp [regenerationTimes]

lemma regenerationTimes_succ {d : ℕ} (ℓ : Vector d) (X : Path d) (n : ℕ) :
    regenerationTimes ℓ X (n + 1) = regenerationTimes ℓ X n +
      (regenerationWords ℓ X n).length := by simp [regenerationTimes, Finset.sum_range_succ]

lemma measurable_regenerationTime {d : ℕ} (ℓ : Vector d) (n : ℕ) :
    Measurable (fun X : Path d => regenerationTimes ℓ X n) := by
  exact Finset.measurable_fun_sum _ fun i _ =>
    (measurable_of_countable List.length).comp (measurable_regenerationWord ℓ i)

lemma iterate_renewSuffix_eq {d : ℕ} (ℓ : Vector d) (X : Path d) (h0 : X 0 = 0) (n j : ℕ) :
    ((renewSuffix ℓ)^[n] X) j = X (regenerationTimes ℓ X n + j) -
      X (regenerationTimes ℓ X n) := by
  induction n generalizing j with
  | zero => simp [h0]
  | succ n ih =>
    rw [Function.iterate_succ_apply', renewSuffix, ih, ih, regenerationTimes_succ]
    change X (regenerationTimes ℓ X n + ((regenerationWords ℓ X n).length + j)) -
      X (regenerationTimes ℓ X n) - (X (regenerationTimes ℓ X n +
      (regenerationWords ℓ X n).length) - X (regenerationTimes ℓ X n)) = _
    rw [Nat.add_assoc]
    abel

lemma strictRecord_suffix_iff {d : ℕ} (ℓ : Vector d) (X : Path d) {n j : ℕ}
    (hn : StrictRecord ℓ X n) (hj : 0 < j) :
    StrictRecord ℓ (fun k => X (n + k) - X n) j ↔ StrictRecord ℓ X (n + j) := by
  simp only [StrictRecord, dot_realPosition_sub, sub_lt_sub_iff_right]
  constructor
  · intro h k hk
    by_cases hkn : k < n
    · exact (hn k hkn).trans (by simpa using h 0 hj)
    · have hle : n ≤ k := by omega
      simpa only [Nat.add_sub_of_le hle] using h (k - n) (by omega)
  · intro h k hk
    exact h (n + k) (by omega)

lemma trueRecord_suffix_iff {d : ℕ} (ℓ : Vector d) (X : Path d) {n j : ℕ}
    (hn : StrictRecord ℓ X n) (hj : 0 < j) :
    TrueRecord ℓ (fun k => X (n + k) - X n) j ↔ TrueRecord ℓ X (n + j) := by
  simp only [TrueRecord, strictRecord_suffix_iff ℓ X hn hj, FutureNoDrop,
    Set.mem_ofPred_eq, dot_realPosition_sub, sub_le_sub_iff_right, Nat.add_assoc]

lemma conditioned_all_firstWords {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) :
    ∀ᵐ X ∂conditionedLaw ν ℓ, ∀ n, ((renewSuffix ℓ)^[n] X) ∈
      FirstWordEvent ℓ (regenerationWords ℓ X n) := by
  apply ae_all_iff.mpr
  intro n
  have h := ((renewSuffix_preserves_conditioned ν ℓ htrans).iterate n).quasiMeasurePreserving.ae
    (conditioned_firstWord_exists ν ℓ htrans)
  filter_upwards [h] with X hX
  exact firstWordEvent_self ℓ _ hX

lemma regenerationTimes_strictMono {d : ℕ} (ℓ : Vector d) (X : Path d)
    (hX : ∀ n, ((renewSuffix ℓ)^[n] X) ∈ FirstWordEvent ℓ (regenerationWords ℓ X n)) :
    StrictMono (regenerationTimes ℓ X) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [regenerationTimes_succ]
  exact Nat.lt_add_of_pos_right (hX n).2.2.1

lemma regenerationTimes_true {d : ℕ} (ℓ : Vector d) (X : Path d) (h0 : X 0 = 0)
    (hX : ∀ n, ((renewSuffix ℓ)^[n] X) ∈ FirstWordEvent ℓ (regenerationWords ℓ X n)) :
    ∀ n, TrueRecord ℓ X (regenerationTimes ℓ X n) := by
  intro n
  induction n with
  | zero =>
    refine ⟨fun j hj => by simp at hj, ?_⟩
    have hD := (hX 0).1
    change X ∈ NoDrop ℓ 0 at hD
    change ∀ j, dot (realPosition (X 0)) ℓ ≤ dot (realPosition (X (0 + j))) ℓ
    simpa only [Nat.zero_add, h0, NoDrop, Set.mem_ofPred_eq] using hD
  | succ n ih =>
    have ht := (hX n).2.2.2.1
    have hj := (hX n).2.2.1
    rw [show (renewSuffix ℓ)^[n] X = _ from funext (iterate_renewSuffix_eq ℓ X h0 n)] at ht
    rw [regenerationTimes_succ]
    exact (trueRecord_suffix_iff ℓ X ih.1 hj).mp ht

lemma regenerationTimes_no_true_between {d : ℕ} (ℓ : Vector d) (X : Path d) (h0 : X 0 = 0)
    (hX : ∀ n, ((renewSuffix ℓ)^[n] X) ∈ FirstWordEvent ℓ (regenerationWords ℓ X n))
    (n j : ℕ) (hj : regenerationTimes ℓ X n < j) (hj' : j < regenerationTimes ℓ X (n+1)) :
    ¬ TrueRecord ℓ X j := by
  intro ht
  have hn := regenerationTimes_true ℓ X h0 hX n
  have hs := (trueRecord_suffix_iff ℓ X hn.1 (show 0 < j - regenerationTimes ℓ X n by omega)).mpr
    (show TrueRecord ℓ X (regenerationTimes ℓ X n + (j - regenerationTimes ℓ X n)) by
      simpa only [Nat.add_sub_of_le hj.le] using ht)
  have he : (fun k => X (regenerationTimes ℓ X n + k) - X (regenerationTimes ℓ X n)) =
      (renewSuffix ℓ)^[n] X := funext fun k => (iterate_renewSuffix_eq ℓ X h0 n k).symm
  rw [he] at hs
  exact (hX n).2.2.2.2 _ (by omega)
    (by rw [regenerationTimes_succ] at hj'; omega) hs

open scoped Classical in
noncomputable def recordCount {d : ℕ} (ℓ : Vector d) (X : Path d) (n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range n, if StrictRecord ℓ X (j + 1) then 1 else 0

noncomputable def wordRecordCount {d : ℕ} (ℓ : Vector d) (w : List (Direction d)) : ℕ :=
  recordCount ℓ (wordPath 0 w) w.length

lemma recordCount_congr_prefix {d : ℕ} (ℓ : Vector d) {X Y : Path d} {n : ℕ}
    (hXY : ∀ j ≤ n, X j = Y j) : recordCount ℓ X n = recordCount ℓ Y n := by
  classical
  apply Finset.sum_congr rfl
  intro j hj
  rw [strictRecord_congr_prefix ℓ (by simpa using Finset.mem_range.mp hj) hXY]

lemma recordCount_add {d : ℕ} (ℓ : Vector d) (X : Path d) {n : ℕ}
    (hn : StrictRecord ℓ X n) (m : ℕ) :
    recordCount ℓ X (n + m) = recordCount ℓ X n +
      recordCount ℓ (fun j => X (n + j) - X n) m := by
  classical
  rw [recordCount, Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  simp only [Nat.add_assoc, strictRecord_suffix_iff ℓ X hn (Nat.succ_pos j)]

lemma recordCount_regenerationTimes {d : ℕ} (ℓ : Vector d) (X : Path d) (h0 : X 0 = 0)
    (hX : ∀ n, ((renewSuffix ℓ)^[n] X) ∈ FirstWordEvent ℓ (regenerationWords ℓ X n)) (n : ℕ) :
    recordCount ℓ X (regenerationTimes ℓ X n) =
      ∑ j ∈ Finset.range n, wordRecordCount ℓ (regenerationWords ℓ X j) := by
  induction n with
  | zero => simp [recordCount]
  | succ n ih =>
    rw [regenerationTimes_succ, recordCount_add ℓ X
      (regenerationTimes_true ℓ X h0 hX n).1, ih, Finset.sum_range_succ]
    congr 1
    have he := recordCount_congr_prefix ℓ (hX n).2.1
    rw [show (renewSuffix ℓ)^[n] X = _ from funext (iterate_renewSuffix_eq ℓ X h0 n)] at he
    exact he

lemma wordRecordCount_positive {d : ℕ} (ℓ : Vector d) (w : List (Direction d))
    (hw : AdmissibleTrueWord ℓ w) : 0 < wordRecordCount ℓ w := by
  classical
  have hn := hw.1
  have hr : StrictRecord ℓ (wordPath 0 w) w.length := fun j hj => (hw.2.1 j hj).2
  have he : w.length - 1 + 1 = w.length := by omega
  have hterm : (if StrictRecord ℓ (wordPath 0 w) (w.length - 1 + 1) then 1 else 0 : ℕ) = 1 := by
    rw [he, ite_eq_left hr]
  have hle := Finset.single_le_sum (f := fun j =>
    (if StrictRecord ℓ (wordPath 0 w) (j+1) then 1 else 0 : ℕ))
    (fun j _ => Nat.zero_le _) (Finset.mem_range.mpr (show w.length - 1 < w.length by omega))
  rw [hterm] at hle
  exact hle

@[simp] lemma recordCount_zero {d : ℕ} (ℓ : Vector d) (X : Path d) :
    recordCount ℓ X 0 = 0 := by simp [recordCount]

open scoped Classical in
lemma recordCount_succ {d : ℕ} (ℓ : Vector d) (X : Path d) (n : ℕ) :
    recordCount ℓ X (n + 1) = recordCount ℓ X n +
      if StrictRecord ℓ X (n + 1) then 1 else 0 := by
  classical
  exact Finset.sum_range_succ (fun j => if StrictRecord ℓ X (j + 1) then 1 else 0) n

lemma recordCount_mono {d : ℕ} (ℓ : Vector d) (X : Path d) :
    Monotone (recordCount ℓ X) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [recordCount_succ]
  exact Nat.le_add_right _ _

lemma recordCount_lt_of_strictRecord {d : ℕ} (ℓ : Vector d) (X : Path d) {m n : ℕ}
    (hmn : m < n) (hn : StrictRecord ℓ X n) : recordCount ℓ X m < recordCount ℓ X n := by
  classical
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show n ≠ 0 by omega)
  rw [recordCount_succ, ite_eq_left hn]
  exact Nat.lt_succ_of_le (recordCount_mono ℓ X (by omega))

lemma recordCount_unbounded {d : ℕ} (ℓ : Vector d) (X : Path d)
    (hX : Tendsto (fun n => dot (realPosition (X n)) ℓ) atTop atTop) :
    ∀ r, ∃ n, r ≤ recordCount ℓ X n := by
  intro r
  induction r with
  | zero => exact ⟨0, Nat.zero_le _⟩
  | succ r ih =>
    obtain ⟨n, hn⟩ := ih
    obtain ⟨m, hnm, hm⟩ := exists_strictRecord_gt ℓ X hX n
    exact ⟨m, Nat.succ_le_of_lt (hn.trans_lt (recordCount_lt_of_strictRecord ℓ X hnm hm))⟩

lemma exists_record_at_index {d : ℕ} (ℓ : Vector d) (X : Path d)
    (hX : Tendsto (fun n => dot (realPosition (X n)) ℓ) atTop atTop) {r : ℕ} (hr : 0 < r) :
    ∃ n, 0 < n ∧ StrictRecord ℓ X n ∧ recordCount ℓ X n = r := by
  classical
  let n := Nat.find (recordCount_unbounded ℓ X hX r)
  have hn : r ≤ recordCount ℓ X n := Nat.find_spec (recordCount_unbounded ℓ X hX r)
  have hn0 : 0 < n := by
    by_contra h
    have he : n = 0 := by omega
    simp only [he, recordCount_zero] at hn
    omega
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn0)
  have hklt : recordCount ℓ X k < r := Nat.lt_of_not_ge
    (Nat.find_min (recordCount_unbounded ℓ X hX r) (by omega))
  have hrec : StrictRecord ℓ X n := by
    by_contra hrec
    rw [hk, recordCount_succ, ite_eq_right (by simpa only [hk, Nat.succ_eq_add_one] using hrec), Nat.add_zero] at hn
    omega
  refine ⟨n, hn0, hrec, ?_⟩
  rw [hk, recordCount_succ, ite_eq_left (by simpa only [hk, Nat.succ_eq_add_one] using hrec)]
  rw [hk, recordCount_succ, ite_eq_left (by simpa only [hk, Nat.succ_eq_add_one] using hrec)] at hn
  omega

lemma measurable_recordCount {d : ℕ} (ℓ : Vector d) (n : ℕ) :
    Measurable (fun X : Path d => recordCount ℓ X n) := by
  classical
  apply Finset.measurable_fun_sum
  intro j _
  exact Measurable.ite (measurableSet_strictRecord ℓ (j+1)) measurable_const measurable_const

def RecordIndexPrefix {d : ℕ} (ℓ : Vector d) (r n : ℕ) : Set (Path d) :=
  {X | 0 < n ∧ StrictRecord ℓ X n ∧ recordCount ℓ X n = r ∧
    ∀ j ≤ n, dot (realPosition (0 : Lattice d)) ℓ ≤ dot (realPosition (X j)) ℓ}

lemma recordIndexPrefix_prefix {d : ℕ} (ℓ : Vector d) (r n : ℕ) :
    PrefixDetermined n (RecordIndexPrefix ℓ r n) := by
  intro X Y hXY
  have hr := strictRecord_congr_prefix ℓ (le_refl n) hXY
  have hc := recordCount_congr_prefix ℓ hXY
  simp only [RecordIndexPrefix, Set.mem_ofPred_eq, hr, hc]
  have hh : (∀ j ≤ n, dot (realPosition (0 : Lattice d)) ℓ ≤ dot (realPosition (X j)) ℓ) ↔
      (∀ j ≤ n, dot (realPosition (0 : Lattice d)) ℓ ≤ dot (realPosition (Y j)) ℓ) :=
    forall_congr' fun j => forall_congr' fun hj => by rw [hXY j hj]
  rw [hh]

lemma measurableSet_recordIndexPrefix {d : ℕ} (ℓ : Vector d) (r n : ℕ) :
    MeasurableSet (RecordIndexPrefix ℓ r n) := by
  simp only [RecordIndexPrefix, Set.ofPred_and, Set.ofPred_forall]
  exact (MeasurableSet.const _).inter ((measurableSet_strictRecord ℓ n).inter
    ((measurableSet_eq_fun (measurable_recordCount ℓ n) measurable_const).inter
      (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
        measurableSet_le measurable_const
          ((measurable_of_countable (f := fun x : Lattice d => dot (realPosition x) ℓ)).comp
            (measurable_pi_apply j)))))

lemma recordIndexPrefix_disjoint {d : ℕ} (ℓ : Vector d) (r : ℕ) :
    Pairwise (fun m n => Disjoint (RecordIndexPrefix ℓ r m) (RecordIndexPrefix ℓ r n)) := by
  intro m n hmn
  apply Set.disjoint_left.mpr
  intro X hm hn
  rcases lt_or_gt_of_ne hmn with h | h
  · have := recordCount_lt_of_strictRecord ℓ X h hn.2.1
    rw [hm.2.2.1, hn.2.2.1] at this
    exact (lt_irrefl _) this
  · have := recordCount_lt_of_strictRecord ℓ X h hm.2.1
    rw [hm.2.2.1, hn.2.2.1] at this
    exact (lt_irrefl _) this

lemma recordIndexPrefix_noDrop {d : ℕ} (ℓ : Vector d) (r n : ℕ) :
    RecordIndexPrefix ℓ r n ∩ FutureNoDrop ℓ n ⊆ NoDrop ℓ 0 := by
  intro X ⟨hX, hD⟩ j
  by_cases hj : j ≤ n
  · exact hX.2.2.2 j hj
  · have hnj : n ≤ j := by omega
    have h := hD (j - n)
    change dot (realPosition (X n)) ℓ ≤ dot (realPosition (X (n + (j-n)))) ℓ at h
    rw [Nat.add_sub_of_le hnj] at h
    exact (hX.2.2.2 n le_rfl).trans h

lemma conditioned_recordIndexPrefix_true {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0) (r n : ℕ) :
    conditionedLaw ν ℓ (RecordIndexPrefix ℓ r n ∩ FutureNoDrop ℓ n) =
      annealedLaw ν (RecordIndexPrefix ℓ r n) := by
  by_cases hn : 0 < n
  · rw [conditionedLaw, Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply ((measurableSet_recordIndexPrefix ℓ r n).inter
        (measurableSet_futureNoDrop ℓ n)),
      Set.inter_eq_left.mpr (recordIndexPrefix_noDrop ℓ r n),
      annealed_record_event_noDrop ν ℓ n hn _ (recordIndexPrefix_prefix ℓ r n)
        (fun X hX => hX.2.1), mul_comm _ (annealedLaw ν _ * _),
      mul_assoc, ENNReal.mul_inv_cancel hp (measure_ne_top _ _), mul_one]
  · have he : RecordIndexPrefix ℓ r n = ∅ := Set.eq_empty_iff_forall_notMem.mpr
      (fun X hX => hn hX.1)
    simp only [he, Set.empty_inter, measure_empty]

lemma conditioned_true_at_index_lower {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) {r : ℕ} (hr : 0 < r) :
    annealedLaw ν (NoDrop ℓ 0) ≤ conditionedLaw ν ℓ
      {X | ∃ n, 0 < n ∧ TrueRecord ℓ X n ∧ recordCount ℓ X n = r} := by
  have hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  have hsub : NoDrop ℓ 0 ≤ᵐ[annealedLaw ν] ⋃ n, RecordIndexPrefix ℓ r n := by
    filter_upwards [htrans] with X hX hD
    obtain ⟨n, hn, hrec, hcount⟩ := exists_record_at_index ℓ X hX hr
    exact Set.mem_iUnion.mpr ⟨n, hn, hrec, hcount, fun j _ => hD j⟩
  calc
    annealedLaw ν (NoDrop ℓ 0) ≤ annealedLaw ν (⋃ n, RecordIndexPrefix ℓ r n) := measure_mono_ae hsub
    _ = ∑' n, annealedLaw ν (RecordIndexPrefix ℓ r n) :=
      measure_iUnion (recordIndexPrefix_disjoint ℓ r) (measurableSet_recordIndexPrefix ℓ r)
    _ = ∑' n, conditionedLaw ν ℓ (RecordIndexPrefix ℓ r n ∩ FutureNoDrop ℓ n) := by
      simp_rw [conditioned_recordIndexPrefix_true ν ℓ hp]
    _ = conditionedLaw ν ℓ (⋃ n, RecordIndexPrefix ℓ r n ∩ FutureNoDrop ℓ n) := by
      symm
      exact measure_iUnion (fun m n hmn => (recordIndexPrefix_disjoint ℓ r hmn).mono
        Set.inter_subset_left Set.inter_subset_left) (fun n =>
        (measurableSet_recordIndexPrefix ℓ r n).inter (measurableSet_futureNoDrop ℓ n))
    _ ≤ _ := measure_mono (by
      rintro X ⟨s, ⟨n, rfl⟩, hX, hD⟩
      exact ⟨n, hX.1, ⟨hX.2.1, hD⟩, hX.2.2.1⟩)

lemma renewal_truncated_sum_le (s : ℕ → ℕ) (H K n : ℕ) :
    (∑ i ∈ Finset.range n, if (∑ j ∈ Finset.range i, s j) ≤ H then min (s i) K else 0) ≤ H + K := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    by_cases hn : (∑ j ∈ Finset.range n, s j) ≤ H
    · rw [ite_eq_left hn]
      apply (Nat.add_le_add ?_ (min_le_right _ _)).trans (Nat.add_le_add_right hn K)
      apply Finset.sum_le_sum
      intro i _
      split_ifs
      · exact min_le_left _ _
      · exact Nat.zero_le _
    · simpa only [ite_eq_right hn, Nat.add_zero] using ih

lemma renewal_wald_bound {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (S : ℕ → α → ℕ) (hS : ∀ i, Measurable (S i)) (hind : iIndepFun S μ)
    (hident : ∀ i, IdentDistrib (S i) (S 0) μ μ) (H K : ℕ) :
    (∑ i ∈ Finset.range (H+1), μ.real {x | (∑ j ∈ Finset.range i, S j x) ≤ H}) *
      (∫ x, ((min (S 0 x) K : ℕ) : ℝ) ∂μ) ≤ (H : ℝ) + K := by
  classical
  let F : ℕ → α → ℝ := fun i x => if (∑ j ∈ Finset.range i, S j x) ≤ H then
    ((min (S i x) K : ℕ) : ℝ) else 0
  have hFmeas (i : ℕ) : Measurable (F i) :=
    Measurable.ite (measurableSet_le (Finset.measurable_fun_sum _ (fun j _ => hS j)) measurable_const)
      ((measurable_of_countable (f := fun n : ℕ => (n : ℝ))).comp ((hS i).min measurable_const)) measurable_const
  have hFint (i : ℕ) : Integrable (F i) μ :=
    integrable_of_nonneg_bound μ (hFmeas i) (B := K) fun x => by
      dsimp [F]
      split_ifs
      · exact ⟨Nat.cast_nonneg _, by exact_mod_cast min_le_right (S i x) K⟩
      · exact ⟨le_rfl, Nat.cast_nonneg _⟩
  have hbound : (∫ x, ∑ i ∈ Finset.range (H+1), F i x ∂μ) ≤ (H : ℝ) + K := by
    calc
      _ ≤ ∫ _ : α, (H : ℝ) + K ∂μ := integral_mono
        (integrable_finsetSum _ (fun i _ => hFint i)) (integrable_const _) fun x => by
          have hh := renewal_truncated_sum_le (fun i => S i x) H K (H+1)
          have he : (∑ i ∈ Finset.range (H+1), F i x) =
              ((∑ i ∈ Finset.range (H+1), if (∑ j ∈ Finset.range i, S j x) ≤ H
                then min (S i x) K else 0 : ℕ) : ℝ) := by
            simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, F, Nat.cast_min]
          rw [he]
          simpa only [Nat.cast_add] using (Nat.cast_le (α := ℝ)).mpr hh
      _ = _ := by simp
  have hfactor (i : ℕ) : (∫ x, F i x ∂μ) =
      μ.real {x | (∑ j ∈ Finset.range i, S j x) ≤ H} *
        ∫ x, ((min (S 0 x) K : ℕ) : ℝ) ∂μ := by
    let A : ℕ → ℝ := fun t => if t ≤ H then 1 else 0
    let B : ℕ → ℝ := fun t => ((min t K : ℕ) : ℝ)
    have hsummeas : Measurable (fun x => ∑ j ∈ Finset.range i, S j x) :=
      Finset.measurable_fun_sum _ (fun j _ => hS j)
    have hi := (hind.indepFun_finsetSum_of_notMem hS (Finset.notMem_range_self (n := i))).comp
      (measurable_of_countable A) (measurable_of_countable B)
    have hi' : IndepFun (fun x => A (∑ j ∈ Finset.range i, S j x)) (fun x => B (S i x)) μ := by
      have heq : (∑ j ∈ Finset.range i, S j) = (fun x => ∑ j ∈ Finset.range i, S j x) := by
        funext x
        simp only [Finset.sum_apply]
      rw [heq] at hi
      exact hi
    have he : F i = fun x => A (∑ j ∈ Finset.range i, S j x) * B (S i x) := by
      funext x
      simp only [F, A, B]
      split_ifs <;> simp
    rw [he, hi'.integral_fun_mul_eq_mul_integral
      ((measurable_of_countable A).comp hsummeas).aestronglyMeasurable
      ((measurable_of_countable B).comp (hS i)).aestronglyMeasurable]
    have hA : (fun x => A (∑ j ∈ Finset.range i, S j x)) =
        {x | (∑ j ∈ Finset.range i, S j x) ≤ H}.indicator (fun _ => (1 : ℝ)) := by
      funext x
      simp only [A, Set.indicator_apply, Set.mem_ofPred_eq]
    rw [hA, integral_indicator_const (1 : ℝ) (measurableSet_le hsummeas measurable_const)]
    simp only [smul_eq_mul, mul_one]
    exact congrArg (fun y => μ.real {x | (∑ j ∈ Finset.range i, S j x) ≤ H} * y)
      ((hident i).comp (measurable_of_countable B)).integral_eq
  rw [integral_finsetSum _ (fun i _ => hFint i)] at hbound
  simp_rw [hfactor] at hbound
  simpa only [Finset.sum_mul] using hbound

end DirectionalTransience
end
end

end OAI

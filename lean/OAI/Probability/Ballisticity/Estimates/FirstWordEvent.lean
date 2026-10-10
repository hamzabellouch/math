import Mathlib
import OAI.Probability.Ballisticity.Estimates.StrictRecord

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma exists_nextRecordAfter {d : ℕ} (ℓ : Vector d) (X : Path d)
    (ht : Tendsto (fun n => dot (realPosition (X n)) ℓ) atTop atTop) (N : ℕ) :
    ∃ n, X ∈ NextRecordAfter ℓ N n := by
  classical
  have he := exists_strictRecord_gt ℓ X ht N
  refine ⟨Nat.find he, (Nat.find_spec he).1, (Nat.find_spec he).2, ?_⟩
  intro j hj hjn hr
  exact Nat.find_min he hjn ⟨hj, hr⟩

lemma annealed_trueRecords_unbounded {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) :
    ∀ᵐ X ∂annealedLaw ν, ∀ N, ∃ m, N < m ∧ TrueRecord ℓ X m := by
  classical
  let μ := annealedLaw ν
  let p := μ (NoDrop ℓ 0)
  have hp : 0 < p := noDrop_positive_of_directionallyTransient ν ℓ htrans
  apply ae_all_iff.mpr
  intro N
  let E : Set (Path d) := {X | ∃ m, N < m ∧ TrueRecord ℓ X m}
  have hE : MeasurableSet E := by
    simp only [E, Set.ofPred_exists, Set.ofPred_and]
    exact MeasurableSet.iUnion fun m =>
      (MeasurableSet.const _).inter (measurableSet_trueRecord ℓ m)
  apply ae_of_prefix_probability_lower μ E hE p hp (measure_ne_top _ _)
  intro n f
  let C := pathCylinder f n
  let A : ℕ → Set (Path d) := fun m => C ∩ NextRecordAfter ℓ (max N n) m
  have hA (m : ℕ) : MeasurableSet (A m) :=
    (measurableSet_pathCylinder f n).inter (measurableSet_nextRecordAfter ℓ _ m)
  have hdis : Pairwise (fun m k => Disjoint (A m) (A k)) := by
    intro m k hmk
    exact (nextRecordAfter_disjoint ℓ (max N n) hmk).mono
      Set.inter_subset_right Set.inter_subset_right
  have hcov : μ (⋃ m, A m) = μ C := by
    apply measure_congr
    filter_upwards [htrans] with X ht
    apply propext
    constructor
    · intro hX
      obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hX
      exact hm.1
    · intro hX
      obtain ⟨m, hm⟩ := exists_nextRecordAfter ℓ X ht (max N n)
      exact Set.mem_iUnion.mpr ⟨m, hX, hm⟩
  have hfac (m : ℕ) : μ (A m ∩ FutureNoDrop ℓ m) = μ (A m) * p := by
    by_cases hm : max N n < m
    · apply annealed_record_event_noDrop ν ℓ m (by omega) (A m)
      · exact prefixDetermined_inter
          (prefixDetermined_mono (by omega) (prefixDetermined_cylinder f n))
          (nextRecordAfter_prefix ℓ _ m)
      · exact fun X hX => hX.2.2.1
    · have he : A m = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        exact fun X hX => hm hX.2.1
      simp [he]
  have hdisD : Pairwise (fun m k =>
      Disjoint (A m ∩ FutureNoDrop ℓ m) (A k ∩ FutureNoDrop ℓ k)) := by
    intro m k hmk
    exact (hdis hmk).mono Set.inter_subset_left Set.inter_subset_left
  calc
    p * μ (pathCylinder f n) = (∑' m, μ (A m)) * p := by
      rw [← measure_iUnion hdis hA, hcov, mul_comm]
    _ = ∑' m, μ (A m ∩ FutureNoDrop ℓ m) := by simp_rw [hfac]; rw [ENNReal.tsum_mul_right]
    _ = μ (⋃ m, A m ∩ FutureNoDrop ℓ m) :=
      (measure_iUnion hdisD (fun m => (hA m).inter (measurableSet_futureNoDrop ℓ m))).symm
    _ ≤ μ (E ∩ pathCylinder f n) := by
      apply measure_mono
      intro X hX
      obtain ⟨m, ⟨hC, hR⟩, hD⟩ := Set.mem_iUnion.mp hX
      exact ⟨⟨m, lt_of_le_of_lt (le_max_left N n) hR.1, hR.2.1, hD⟩, hC⟩

lemma annealed_firstTrueRecord_exists {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) :
    ∀ᵐ X ∂annealedLaw ν, ∃ n, FirstTrueRecord ℓ X n := by
  classical
  filter_upwards [annealed_trueRecords_unbounded ν ℓ htrans] with X hX
  have he := hX 0
  exact ⟨Nat.find he, (Nat.find_spec he).1, (Nat.find_spec he).2,
    fun j hj hjn hr => Nat.find_min he hjn ⟨hj, hr⟩⟩

lemma annealed_ae_of_quenched {d : ℕ} (ν : Measure (Row d))
    (P : Path d → Prop) (hP : MeasurableSet {X | P X})
    (h : ∀ ω : Environment d, ∀ᵐ X ∂quenchedKernel (ω, 0), P X) :
    ∀ᵐ X ∂annealedLaw ν, P X := by
  rw [ae_iff]
  change annealedLaw ν ({X | P X}ᶜ) = 0
  rw [annealed_apply ν hP.compl]
  simp only [show ∀ ω : Environment d, quenchedKernel (ω, 0) {X | P X}ᶜ = 0 from
    fun ω => ae_iff.mp (h ω), lintegral_zero]

lemma annealed_initial {d : ℕ} (ν : Measure (Row d)) :
    ∀ᵐ X ∂annealedLaw ν, X 0 = 0 := by
  exact annealed_ae_of_quenched ν _ (measurableSet_eq_fun (measurable_pi_apply 0)
    measurable_const) (fun ω => quenched_initial_ae (ω, 0))

lemma annealed_nearest_neighbor {d : ℕ} (ν : Measure (Row d)) :
    ∀ᵐ X ∂annealedLaw ν, ∀ n, ∃ e : Direction d, X (n + 1) = X n + step e := by
  apply annealed_ae_of_quenched ν
  · simp only [Set.ofPred_forall, Set.ofPred_exists]
    exact MeasurableSet.iInter fun n => MeasurableSet.iUnion fun e =>
      measurableSet_eq_fun (measurable_pi_apply (n + 1))
        ((measurable_pi_apply n : Measurable (fun X : Path d => X n)).add_const (step e))
  · exact fun ω => quenched_nearest_neighbor (ω, 0)

lemma exists_word_prefix {d : ℕ} (X : Path d)
    (hX : ∀ n, ∃ e : Direction d, X (n + 1) = X n + step e) (N : ℕ) :
    ∃ w : List (Direction d), w.length = N ∧ X ∈ wordCylinder (X 0) w := by
  induction N generalizing X with
  | zero =>
    refine ⟨[], rfl, ?_⟩
    intro j hj
    have : j = 0 := by simpa using hj
    subst j
    rfl
  | succ N ih =>
    obtain ⟨e, he⟩ := hX 0
    obtain ⟨w, hw, hwp⟩ := ih (fun j => X (j + 1)) (fun n => hX (n + 1))
    refine ⟨e :: w, by simp [hw], ?_⟩
    intro j hj
    cases j with
    | zero => rfl
    | succ j =>
      have hh := hwp j (by simpa only [List.length_cons, Nat.add_le_add_iff_right] using hj)
      simpa only [wordPath, he] using hh

lemma word_eq_of_paths {d : ℕ} (x : Lattice d) (u v : List (Direction d))
    (hlen : u.length = v.length)
    (hpath : ∀ j ≤ u.length, wordPath x u j = wordPath x v j) : u = v := by
  induction u generalizing v x with
  | nil =>
    have : v = [] := List.length_eq_zero_iff.mp hlen.symm
    exact this.symm
  | cons e u ih =>
    cases v with
    | nil => simp at hlen
    | cons f v =>
      have he : e = f := by
        apply step_injective
        apply add_left_cancel (a := x)
        simpa only [wordPath, wordPath_zero] using hpath 1 (by simp)
      subst f
      congr 1
      apply ih (x + step e) v (by simpa only [List.length_cons, Nat.add_right_cancel_iff] using hlen)
      intro j hj
      simpa only [wordPath] using hpath (j + 1) (by simpa only [List.length_cons,
        Nat.add_le_add_iff_right] using hj)

lemma word_eq_of_cylinders {d : ℕ} (x : Lattice d) (u v : List (Direction d))
    (X : Path d) (hu : X ∈ wordCylinder x u) (hv : X ∈ wordCylinder x v)
    (hlen : u.length = v.length) : u = v := by
  apply word_eq_of_paths x u v hlen
  intro j hj
  exact (hu j hj).symm.trans (hv j (hlen ▸ hj))

def FirstWordEvent {d : ℕ} (ℓ : Vector d) (w : List (Direction d)) : Set (Path d) :=
  NoDrop ℓ 0 ∩ (wordCylinder 0 w ∩ {X | FirstTrueRecord ℓ X w.length})

lemma measurableSet_firstWordEvent {d : ℕ} (ℓ : Vector d) (w : List (Direction d)) :
    MeasurableSet (FirstWordEvent ℓ w) :=
  (measurableSet_noDrop ℓ 0).inter ((measurableSet_wordCylinder 0 w).inter
    (measurableSet_firstTrueRecord ℓ w.length))

lemma firstWordEvent_nil {d : ℕ} (ℓ : Vector d) : FirstWordEvent ℓ [] = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  exact fun X hX => Nat.lt_irrefl 0 hX.2.2.1

lemma firstWordEvent_disjoint {d : ℕ} (ℓ : Vector d) :
    Pairwise (fun u v => Disjoint (FirstWordEvent ℓ u) (FirstWordEvent ℓ v)) := by
  intro u v huv
  apply Set.disjoint_left.mpr
  intro X hXu hXv
  exact huv (word_eq_of_cylinders 0 u v X hXu.2.1 hXv.2.1
    (firstTrueRecord_unique ℓ X hXu.2.2 hXv.2.2))

lemma firstWordEvent_eq {d : ℕ} (ℓ : Vector d) (w : List (Direction d))
    (hw : AdmissibleTrueWord ℓ w) :
    FirstWordEvent ℓ w = (fun X : Path d => fun j => X (w.length + j) -
      wordPath 0 w w.length) ⁻¹' NoDrop ℓ 0 ∩ wordCylinder 0 w := by
  ext X
  constructor
  · rintro ⟨hD, hcy, hT⟩
    exact ⟨((firstTrueWord_characterization ℓ w X hcy).mp ⟨hD, hT⟩).2, hcy⟩
  · rintro ⟨hD, hcy⟩
    have hh := (firstTrueWord_characterization ℓ w X hcy).mpr ⟨hw, hD⟩
    exact ⟨hh.1, hcy, hh.2⟩

lemma conditionedLaw_absolutelyContinuous {d : ℕ} (ν : Measure (Row d)) (ℓ : Vector d) :
    conditionedLaw ν ℓ ≪ annealedLaw ν :=
  (Measure.AbsolutelyContinuous.smul_left (Measure.absolutelyContinuous_restrict) _)

lemma conditionedLaw_noDrop {d : ℕ} (ν : Measure (Row d)) (ℓ : Vector d) :
    ∀ᵐ X ∂conditionedLaw ν ℓ, X ∈ NoDrop ℓ 0 := by
  exact Measure.ae_smul_measure (ae_restrict_mem (measurableSet_noDrop ℓ 0)) _

lemma conditioned_firstWord_exists {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) :
    ∀ᵐ X ∂conditionedLaw ν ℓ, ∃ w, X ∈ FirstWordEvent ℓ w := by
  have hac := conditionedLaw_absolutelyContinuous ν ℓ
  filter_upwards [conditionedLaw_noDrop ν ℓ, hac.ae_le (annealed_initial ν),
    hac.ae_le (annealed_nearest_neighbor ν), hac.ae_le (annealed_firstTrueRecord_exists ν ℓ htrans)]
    with X hD h0 hNN hT
  obtain ⟨n, hn⟩ := hT
  obtain ⟨w, hw, hcy⟩ := exists_word_prefix X hNN n
  exact ⟨w, hD, by simpa only [h0] using hcy, hw.symm ▸ hn⟩

instance wordMeasurableSpace {d : ℕ} : MeasurableSpace (List (Direction d)) := ⊤

instance wordDiscreteMeasurable {d : ℕ} : DiscreteMeasurableSpace (List (Direction d)) := ⟨fun _ => trivial⟩

open scoped Classical in
noncomputable def firstWord {d : ℕ} (ℓ : Vector d) (X : Path d) : List (Direction d) :=
  if h : ∃ w, X ∈ FirstWordEvent ℓ w then h.choose else []

lemma firstWord_eq_iff {d : ℕ} (ℓ : Vector d) (X : Path d) (w : List (Direction d))
    (hw : w ≠ []) : firstWord ℓ X = w ↔ X ∈ FirstWordEvent ℓ w := by
  classical
  unfold firstWord
  split_ifs with h
  · constructor
    · intro he
      exact he ▸ h.choose_spec
    · intro hX
      by_contra hne
      exact (Set.disjoint_left.mp (firstWordEvent_disjoint ℓ hne)) h.choose_spec hX
  · simp only [eq_comm (a := ([] : List (Direction d))), hw, false_iff]
    exact fun hX => h ⟨w, hX⟩

lemma firstWord_nil_iff {d : ℕ} (ℓ : Vector d) (X : Path d) :
    firstWord ℓ X = [] ↔ ¬ ∃ w, X ∈ FirstWordEvent ℓ w := by
  classical
  unfold firstWord
  split_ifs with h
  · simp only [h, not_true_eq_false, iff_false]
    intro he
    have := h.choose_spec
    rw [he, firstWordEvent_nil] at this
    exact this
  · simp [h]

lemma measurable_firstWord {d : ℕ} (ℓ : Vector d) : Measurable (firstWord ℓ) := by
  classical
  apply measurable_to_countable'
  intro w
  by_cases hw : w = []
  · subst w
    have he : firstWord ℓ ⁻¹' {[]} = (⋃ w, FirstWordEvent ℓ w)ᶜ := by
      ext X
      simp only [Set.mem_preimage, Set.mem_singleton_iff, firstWord_nil_iff,
        Set.mem_compl_iff, Set.mem_iUnion]
    rw [he]
    exact (MeasurableSet.iUnion (measurableSet_firstWordEvent ℓ)).compl
  · have he : firstWord ℓ ⁻¹' {w} = FirstWordEvent ℓ w := by
      ext X
      exact firstWord_eq_iff ℓ X w hw
    rw [he]
    exact measurableSet_firstWordEvent ℓ w

lemma conditionedLaw_inter_noDrop {d : ℕ} (ν : Measure (Row d)) (ℓ : Vector d)
    (A : Set (Path d)) (hA : MeasurableSet A) :
    conditionedLaw ν ℓ (A ∩ NoDrop ℓ 0) = conditionedLaw ν ℓ A := by
  simp only [conditionedLaw, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply hA, Measure.restrict_apply (hA.inter (measurableSet_noDrop ℓ 0)),
    Set.inter_self, Set.inter_assoc]

lemma conditionedLaw_noDrop_mass {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0) :
    conditionedLaw ν ℓ (NoDrop ℓ 0) = 1 := by
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ hp
  simpa only [Set.univ_inter, measure_univ] using
    conditionedLaw_inter_noDrop ν ℓ Set.univ MeasurableSet.univ

lemma conditioned_firstWordEvent_mass {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0)
    (w : List (Direction d)) (hw : AdmissibleTrueWord ℓ w) :
    conditionedLaw ν ℓ (FirstWordEvent ℓ w) = annealedLaw ν (wordCylinder 0 w) := by
  rw [firstWordEvent_eq ℓ w hw, conditioned_true_word_factor ν ℓ w hw _
    (measurableSet_noDrop ℓ 0) (Set.Subset.refl _), conditionedLaw_noDrop_mass ν ℓ hp, mul_one]

lemma firstWordEvent_empty_of_not_admissible {d : ℕ} (ℓ : Vector d)
    (w : List (Direction d)) (hw : ¬ AdmissibleTrueWord ℓ w) : FirstWordEvent ℓ w = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  exact fun X hX => hw (((firstTrueWord_characterization ℓ w X hX.2.1).mp ⟨hX.1, hX.2.2⟩).1)

lemma conditioned_firstWordEvent_factor {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0)
    (w : List (Direction d)) (A : Set (Path d)) (hA : MeasurableSet A) :
    conditionedLaw ν ℓ (FirstWordEvent ℓ w ∩ (fun X : Path d => fun j =>
      X (w.length + j) - wordPath 0 w w.length) ⁻¹' A) =
      conditionedLaw ν ℓ (FirstWordEvent ℓ w) * conditionedLaw ν ℓ A := by
  classical
  by_cases hw : AdmissibleTrueWord ℓ w
  · have he : FirstWordEvent ℓ w ∩ (fun X : Path d => fun j =>
        X (w.length + j) - wordPath 0 w w.length) ⁻¹' A =
        (fun X : Path d => fun j => X (w.length + j) - wordPath 0 w w.length) ⁻¹'
          (A ∩ NoDrop ℓ 0) ∩ wordCylinder 0 w := by
      rw [firstWordEvent_eq ℓ w hw]
      ext X
      simp only [Set.mem_inter_iff, Set.mem_preimage]
      tauto
    rw [he, conditioned_true_word_factor ν ℓ w hw _
      (hA.inter (measurableSet_noDrop ℓ 0)) Set.inter_subset_right,
      conditionedLaw_inter_noDrop ν ℓ A hA, conditioned_firstWordEvent_mass ν ℓ hp w hw]
  · simp only [firstWordEvent_empty_of_not_admissible ℓ w hw, Set.empty_inter,
      measure_empty, zero_mul]

noncomputable def renewSuffix {d : ℕ} (ℓ : Vector d) (X : Path d) : Path d :=
  fun j => X ((firstWord ℓ X).length + j) - X (firstWord ℓ X).length

lemma measurable_renewSuffix {d : ℕ} (ℓ : Vector d) : Measurable (renewSuffix ℓ) := by
  apply Measurable.of_eval
  intro j
  have hf : Measurable (fun X : Path d => (firstWord ℓ X).length) :=
    (measurable_of_countable List.length).comp (measurable_firstWord ℓ)
  have heval : Measurable (fun p : Path d × ℕ => p.1 p.2) :=
    measurable_from_prod_countable_left fun n => measurable_pi_apply n
  exact (heval.comp (measurable_id.prodMk (hf.add_const j))).sub
    (heval.comp (measurable_id.prodMk hf))

lemma renewSuffix_on_firstWordEvent {d : ℕ} (ℓ : Vector d) (w : List (Direction d))
    (X : Path d) (hX : X ∈ FirstWordEvent ℓ w) :
    renewSuffix ℓ X = fun j => X (w.length + j) - wordPath 0 w w.length := by
  have hw : w ≠ [] := by
    intro he
    rw [he, firstWordEvent_nil] at hX
    exact hX
  unfold renewSuffix
  rw [(firstWord_eq_iff ℓ X w hw).mpr hX, hX.2.1 w.length le_rfl]

lemma conditioned_firstWord_fiber_ae {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) (w : List (Direction d)) :
    firstWord ℓ ⁻¹' {w} =ᵐ[conditionedLaw ν ℓ] FirstWordEvent ℓ w := by
  classical
  by_cases hw : w = []
  · subst w
    filter_upwards [conditioned_firstWord_exists ν ℓ htrans] with X hX
    apply propext
    change firstWord ℓ X = [] ↔ X ∈ FirstWordEvent ℓ []
    rw [firstWord_nil_iff, firstWordEvent_nil]
    simp only [hX, not_true_eq_false, Set.mem_empty_iff_false]
  · exact Filter.Eventually.of_forall fun X => propext (firstWord_eq_iff ℓ X w hw)

lemma conditioned_firstWord_fiber_factor {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (w : List (Direction d)) (A : Set (Path d)) (hA : MeasurableSet A) :
    conditionedLaw ν ℓ (firstWord ℓ ⁻¹' {w} ∩ renewSuffix ℓ ⁻¹' A) =
      conditionedLaw ν ℓ (firstWord ℓ ⁻¹' {w}) * conditionedLaw ν ℓ A := by
  have hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  have hcy := conditioned_firstWord_fiber_ae ν ℓ htrans w
  have hE : (firstWord ℓ ⁻¹' {w} ∩ renewSuffix ℓ ⁻¹' A : Set (Path d)) =ᵐ[conditionedLaw ν ℓ]
      (FirstWordEvent ℓ w ∩ renewSuffix ℓ ⁻¹' A : Set (Path d)) :=
    hcy.inter (Filter.Eventually.of_forall fun _ => rfl)
  rw [measure_congr hE, measure_congr hcy]
  have he : FirstWordEvent ℓ w ∩ renewSuffix ℓ ⁻¹' A =
      FirstWordEvent ℓ w ∩ (fun X : Path d => fun j => X (w.length + j) -
        wordPath 0 w w.length) ⁻¹' A := by
    ext X
    by_cases hX : X ∈ FirstWordEvent ℓ w
    · simp only [Set.mem_inter_iff, Set.mem_preimage, hX, true_and,
        renewSuffix_on_firstWordEvent ℓ w X hX]
    · simp only [Set.mem_inter_iff, hX, false_and]
  rw [he]
  exact conditioned_firstWordEvent_factor ν ℓ hp w A hA

lemma renewSuffix_preserves_conditioned {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) :
    MeasurePreserving (renewSuffix ℓ) (conditionedLaw ν ℓ) (conditionedLaw ν ℓ) := by
  have hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ hp
  refine ⟨measurable_renewSuffix ℓ, ?_⟩
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply (measurable_renewSuffix ℓ) hA]
  have hpart : ∀ B : Set (Path d), MeasurableSet B → conditionedLaw ν ℓ B =
      ∑' w : List (Direction d), conditionedLaw ν ℓ (firstWord ℓ ⁻¹' {w} ∩ B) := by
    intro B hB
    have he : (⋃ w : List (Direction d), firstWord ℓ ⁻¹' {w} ∩ B) = B := by
      ext X
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun ⟨w, _, hX⟩ => hX, fun hX => ⟨firstWord ℓ X, rfl, hX⟩⟩
    rw [← he]
    conv_rhs => arg 1; ext w; rw [he]
    exact measure_iUnion (fun u v huv => ((Set.disjoint_singleton.mpr huv).preimage
      (firstWord ℓ)).mono Set.inter_subset_left Set.inter_subset_left)
      (fun w => ((measurable_firstWord ℓ) (measurableSet_singleton w)).inter hB)
  have hsum : (∑' w : List (Direction d), conditionedLaw ν ℓ (firstWord ℓ ⁻¹' {w})) = 1 := by
    simpa only [Set.inter_univ, measure_univ] using (hpart Set.univ MeasurableSet.univ).symm
  rw [hpart (renewSuffix ℓ ⁻¹' A) (hA.preimage (measurable_renewSuffix ℓ))]
  simp_rw [conditioned_firstWord_fiber_factor ν ℓ htrans _ A hA]
  rw [ENNReal.tsum_mul_right, hsum, one_mul]

lemma measure_preimage_partition {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Countable β] [MeasurableSingletonClass β] (μ : Measure α) (f : α → β)
    (hf : Measurable f) (B : Set β) (hB : MeasurableSet B) (C : Set α) :
    μ (f ⁻¹' B ∩ C) = ∑' b : B, μ (f ⁻¹' {b.1} ∩ C) := by
  have h := tsum_measure_preimage_singleton (μ := μ.restrict C) (s := B)
    (Set.to_countable B) (f := f) (fun b _ => hf (measurableSet_singleton b))
  simpa only [Measure.restrict_apply (hf hB),
    Measure.restrict_apply (hf (measurableSet_singleton _))] using h.symm

lemma firstWord_indep_renewSuffix {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) :
    IndepFun (firstWord ℓ) (renewSuffix ℓ) (conditionedLaw ν ℓ) := by
  apply indepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro B A hB hA
  have hT := renewSuffix_preserves_conditioned ν ℓ htrans
  rw [hT.measure_preimage hA.nullMeasurableSet,
    measure_preimage_partition _ _ (measurable_firstWord ℓ) B hB]
  simp_rw [conditioned_firstWord_fiber_factor ν ℓ htrans _ A hA]
  rw [ENNReal.tsum_mul_right]
  have hsum := measure_preimage_partition (conditionedLaw ν ℓ) (firstWord ℓ)
    (measurable_firstWord ℓ) B hB Set.univ
  simpa only [Set.inter_univ] using congrArg (fun x => x * conditionedLaw ν ℓ A) hsum.symm

lemma independent_iterated_symbols {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsProbabilityMeasure μ] (F : α → β) (T : α → α)
    (hF : Measurable F) (hT : MeasurePreserving T μ μ) (hFT : IndepFun F T μ) :
    iIndepFun (fun n : ℕ => fun x => F (T^[n] x)) μ := by
  classical
  have hprefix : ∀ n : ℕ, ∀ (B : ℕ → Set β), (∀ i, MeasurableSet (B i)) →
      μ {x | ∀ i < n, F (T^[i] x) ∈ B i} = ∏ i ∈ Finset.range n, μ (F ⁻¹' B i) := by
    intro n
    induction n with
    | zero => intro B hB; simp
    | succ n ih =>
      intro B hB
      let E : Set α := {x | ∀ i < n, F (T^[i] x) ∈ B (i + 1)}
      have hE : MeasurableSet E := by
        simp only [E, Set.ofPred_forall]
        exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
          (hB (i + 1)).preimage (hF.comp (hT.iterate i).measurable)
      have he : {x | ∀ i < n + 1, F (T^[i] x) ∈ B i} = F ⁻¹' B 0 ∩ T ⁻¹' E := by
        ext x
        constructor
        · intro hx
          refine ⟨by simpa using hx 0 (by omega), ?_⟩
          intro i hi
          simpa only [Function.iterate_succ_apply] using hx (i + 1) (by omega)
        · rintro ⟨h0, hs⟩ i hi
          cases i with
          | zero => simpa using h0
          | succ i =>
            simpa only [Function.iterate_succ_apply] using hs i (by omega)
      rw [he, hFT.measure_inter_preimage_eq_mul _ _ (hB 0) hE,
        hT.measure_preimage hE.nullMeasurableSet]
      change μ (F ⁻¹' B 0) * μ {x | ∀ i < n, F (T^[i] x) ∈ B (i + 1)} = _
      rw [ih (fun i => B (i + 1)) (fun i => hB (i + 1)),
        Finset.prod_range_succ', mul_comm]
  apply iIndepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro S B hB
  let N := S.sup id + 1
  have hS : S ⊆ Finset.range N := by
    intro i hi
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi))
  let C : ℕ → Set β := fun i => if i ∈ S then B i else Set.univ
  have hC : ∀ i, MeasurableSet (C i) := by
    intro i
    by_cases hi : i ∈ S
    · simpa only [C, ite_eq_left hi] using hB i hi
    · simp only [C, ite_eq_right hi]; exact MeasurableSet.univ
  have he : (⋂ i ∈ S, (fun x => F (T^[i] x)) ⁻¹' B i) =
      {x | ∀ i < N, F (T^[i] x) ∈ C i} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_ofPred_eq]
    constructor
    · intro hx i _
      by_cases hi : i ∈ S
      · simpa only [C, ite_eq_left hi] using hx i hi
      · simp only [C, ite_eq_right hi, Set.mem_univ]
    · intro hx i hi
      simpa only [C, ite_eq_left hi] using hx i (Finset.mem_range.mp (hS hi))
  rw [he, hprefix N C hC]
  calc
    (∏ i ∈ Finset.range N, μ (F ⁻¹' C i)) = ∏ i ∈ S, μ (F ⁻¹' C i) := by
      symm
      apply Finset.prod_subset hS
      intro i _ hi
      simp only [C, ite_eq_right hi, Set.preimage_univ, measure_univ]
    _ = ∏ i ∈ S, μ ((fun x => F (T^[i] x)) ⁻¹' B i) := by
      apply Finset.prod_congr rfl
      intro i hi
      simp only [C, ite_eq_left hi]
      exact ((hT.iterate i).measure_preimage ((hB i hi).preimage hF).nullMeasurableSet).symm

end DirectionalTransience
end
end

end OAI

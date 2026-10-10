import Mathlib
import OAI.Probability.Ballisticity.Estimates.SymmetricTruncate

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma common_record_gap_le_max {d : ℕ} (ℓ : Vector d) (e : Direction d) (P : Path d × Path d)
    (h0 : P.1 0 = 0) (h0' : P.2 0 = 0)
    (hP : ∀ n, ((renewPairSuffix ℓ)^[n] P) ∈ FirstPairWordEvent ℓ (commonWords ℓ P n))
    {j k H : ℕ} (hr : CommonTrueRecord ℓ P j k) (hH : recordCount ℓ P.1 j ≤ H) :
    |signedCoordinate e (P.1 j)-signedCoordinate e (P.2 k)| ≤
      partialSumMax (fun n => commonIncrementProcess ℓ e n P) H := by
  obtain ⟨n, hn⟩ := commonTrueRecord_eq_commonTimes ℓ P h0 h0' hP hr
  have hcoord := common_coordinate_sum ℓ e P h0 h0' hP n
  have hnle := commonIndex_le_recordCount ℓ P h0 h0' hP n
  rw [hn] at hcoord hnle
  rw [hcoord]
  exact (abs_partialSum_le_max _ n).trans (partialSumMax_mono _ (hnle.trans hH))

lemma conditioned_record_prefix_true {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0) {n : ℕ} (hn : 0 < n)
    (A : Set (Path d)) (hm : MeasurableSet A) (hA : PrefixDetermined n A)
    (hr : ∀ X ∈ A, StrictRecord ℓ X n)
    (hpos : ∀ X ∈ A, ∀ j ≤ n, 0 ≤ dot (realPosition (X j)) ℓ) :
    conditionedLaw ν ℓ (A ∩ FutureNoDrop ℓ n) = annealedLaw ν A := by
  have hsub : A ∩ FutureNoDrop ℓ n ⊆ NoDrop ℓ 0 := by
    rintro X ⟨hX,hD⟩ j
    simp only [realPosition,dot,Pi.zero_apply,Int.cast_zero,zero_mul,Finset.sum_const_zero]
    by_cases hj : j ≤ n
    · exact hpos X hX j hj
    · have hnj : n ≤ j := by omega
      have h := hD (j-n)
      change dot (realPosition (X n)) ℓ ≤ dot (realPosition (X (n+(j-n)))) ℓ at h
      rw [Nat.add_sub_of_le hnj] at h
      exact (hpos X hX n le_rfl).trans h
  rw [conditionedLaw,Measure.smul_apply,smul_eq_mul,
    Measure.restrict_apply (hm.inter (measurableSet_futureNoDrop ℓ n)),
    Set.inter_eq_left.mpr hsub,annealed_record_event_noDrop ν ℓ n hn A hA hr,
    mul_comm _ (annealedLaw ν A * _),mul_assoc,
    ENNReal.mul_inv_cancel hp (measure_ne_top _ _),mul_one]

noncomputable def recordIndexTime {d : ℕ} (ℓ : Vector d) (r : ℕ) (X : Path d) : ℕ := by
  classical
  exact if h : ∃ n, X ∈ RecordIndexPrefix ℓ r n then Nat.find h else 0

lemma recordIndexTime_eq {d : ℕ} (ℓ : Vector d) (r n : ℕ) (X : Path d)
    (hX : X ∈ RecordIndexPrefix ℓ r n) : recordIndexTime ℓ r X = n := by
  classical
  have hex : ∃ n, X ∈ RecordIndexPrefix ℓ r n := ⟨n,hX⟩
  rw [recordIndexTime,dite_eq_left hex]
  by_contra h
  exact Set.disjoint_left.mp (recordIndexPrefix_disjoint ℓ r h) (Nat.find_spec hex) hX

lemma measurable_recordIndexTime {d : ℕ} (ℓ : Vector d) (r : ℕ) :
    Measurable (recordIndexTime ℓ r) := by
  classical
  apply measurable_to_countable'
  intro n
  have he : {X : Path d | recordIndexTime ℓ r X = n} =
      RecordIndexPrefix ℓ r n ∪
        (if n = 0 then (⋃ m, RecordIndexPrefix ℓ r m)ᶜ else ∅) := by
    ext X
    simp only [Set.mem_ofPred_eq]
    by_cases hx : ∃ m, X ∈ RecordIndexPrefix ℓ r m
    · obtain ⟨m,hm⟩ := hx
      rw [recordIndexTime_eq ℓ r m X hm]
      by_cases hn : n = m
      · subst n
        simp only [Set.mem_union,true_iff]
        exact Or.inl hm
      · have hnot : X ∉ RecordIndexPrefix ℓ r n :=
          fun hn' => Set.disjoint_left.mp (recordIndexPrefix_disjoint ℓ r hn) hn' hm
        have hnot' : X ∈ ⋃ j, RecordIndexPrefix ℓ r j := Set.mem_iUnion.mpr ⟨m,hm⟩
        simp only [Ne.symm hn,false_iff,Set.mem_union]
        rintro (h | h)
        · exact hnot h
        · split_ifs at h
          · exact h hnot'
          · exact h
    · have hm : X ∉ ⋃ m, RecordIndexPrefix ℓ r m := by simpa only [Set.mem_iUnion] using hx
      have hn : X ∉ RecordIndexPrefix ℓ r n := fun h => hx ⟨n,h⟩
      by_cases hn0 : n = 0
      · subst n
        simp only [recordIndexTime,dite_eq_right hx,Set.mem_union,true_iff]
        exact Or.inr hm
      · simp [recordIndexTime,hx,hn,hn0,Ne.symm hn0]
  change MeasurableSet {X : Path d | recordIndexTime ℓ r X = n}
  rw [he]
  exact (measurableSet_recordIndexPrefix ℓ r n).union (by
    split_ifs
    · exact (MeasurableSet.iUnion fun m => measurableSet_recordIndexPrefix ℓ r m).compl
    · exact MeasurableSet.empty)

noncomputable def recordIndexPosition {d : ℕ} (ℓ : Vector d) (r : ℕ) (X : Path d) : Lattice d :=
  X (recordIndexTime ℓ r X)

lemma measurable_recordIndexPosition {d : ℕ} (ℓ : Vector d) (r : ℕ) :
    Measurable (recordIndexPosition ℓ r) :=
  (measurable_from_prod_countable_left
    (f := fun q : Path d × ℕ => q.1 q.2) (fun n => measurable_pi_apply n)).comp
      (measurable_id.prodMk (measurable_recordIndexTime ℓ r))

lemma conditioned_recordIndexPrefix_exists {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) {r : ℕ} (hr : 0 < r) :
    ∀ᵐ X ∂conditionedLaw ν ℓ, ∃ n, X ∈ RecordIndexPrefix ℓ r n := by
  filter_upwards [conditionedLaw_noDrop ν ℓ,
    (conditionedLaw_absolutelyContinuous ν ℓ).ae_le htrans] with X hD ht
  obtain ⟨n,hn,hrec,hcount⟩ := exists_record_at_index ℓ X ht hr
  exact ⟨n,hn,hrec,hcount,fun j _ => hD j⟩

lemma conditioned_recordIndexTime_spec {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ) {r : ℕ} (hr : 0 < r) :
    ∀ᵐ X ∂conditionedLaw ν ℓ, X ∈ RecordIndexPrefix ℓ r (recordIndexTime ℓ r X) := by
  filter_upwards [conditioned_recordIndexPrefix_exists ν ℓ htrans hr] with X hX
  obtain ⟨n,hn⟩ := hX
  rwa [recordIndexTime_eq ℓ r n X hn]

lemma independentConditionedPairLaw_eq_restrict {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) :
    independentConditionedPairLaw ν ℓ =
      ((annealedLaw ν (NoDrop ℓ 0))^2)⁻¹ •
        (independentPairLaw ν).restrict (NoDrop ℓ 0 ×ˢ NoDrop ℓ 0) := by
  rw [independentConditionedPairLaw,conditionedLaw,Measure.prod_smul_left,
    Measure.prod_smul_right,smul_smul,Measure.prod_restrict,← pow_two,← ENNReal.inv_pow]
  rfl

lemma independentConditionedPairLaw_normalization {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0)
    (A : Set (Path d × Path d)) (hA : MeasurableSet A) :
    (annealedLaw ν (NoDrop ℓ 0))^2 * independentConditionedPairLaw ν ℓ A =
      independentPairLaw ν (A ∩ (NoDrop ℓ 0 ×ˢ NoDrop ℓ 0)) := by
  rw [independentConditionedPairLaw_eq_restrict,Measure.smul_apply,smul_eq_mul,
    Measure.restrict_apply hA,← mul_assoc,
    ENNReal.mul_inv_cancel (pow_ne_zero 2 hp) (ENNReal.pow_ne_top (measure_ne_top _ _)),one_mul]

lemma independentConditionedPairLaw_le_raw {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0)
    (A : Set (Path d × Path d)) (hA : MeasurableSet A) :
    (annealedLaw ν (NoDrop ℓ 0))^2 * independentConditionedPairLaw ν ℓ A ≤
      independentPairLaw ν A := by
  rw [independentConditionedPairLaw_normalization ν ℓ hp A hA]
  exact measure_mono Set.inter_subset_left

lemma independent_conditioned_record_prefix_lower {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0)
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (A : Set (Path d × Path d))
    (hAm : MeasurableSet A) (hA : PairPrefixDetermined n m A)
    (hr : ∀ P ∈ A, StrictRecord ℓ P.1 n ∧ StrictRecord ℓ P.2 m ∧
      dot (realPosition (P.1 n)) ℓ = dot (realPosition (P.2 m)) ℓ)
    (hD : A ∩ (FutureNoDrop ℓ n ×ˢ FutureNoDrop ℓ m) ⊆ NoDrop ℓ 0 ×ˢ NoDrop ℓ 0) :
    independentPairLaw ν A ≤ independentConditionedPairLaw ν ℓ
      (A ∩ (FutureNoDrop ℓ n ×ˢ FutureNoDrop ℓ m)) := by
  have hh := pair_record_event_noDrop_lower (independentPairLaw ν) ℓ
    ((annealedLaw ν (NoDrop ℓ 0))^2)
    (fun f g n m hn hm hrf hrg _ =>
      (independent_pair_record_cylinder_noDrop ν ℓ f g n m hn hm hrf hrg).ge)
    n m hn hm A hA hr
  have he := independentConditionedPairLaw_normalization ν ℓ hp
    (A ∩ (FutureNoDrop ℓ n ×ˢ FutureNoDrop ℓ m))
    (hAm.inter ((measurableSet_futureNoDrop ℓ n).prod (measurableSet_futureNoDrop ℓ m)))
  rw [Set.inter_eq_left.mpr hD] at he
  rw [← he] at hh
  exact (ENNReal.mul_le_mul_iff_right (pow_ne_zero 2 hp)
    (ENNReal.pow_ne_top (measure_ne_top _ _))).mp hh

def PairRecordDeviation {d : ℕ} (ℓ : Vector d) (e : Direction d) (H : ℕ) (z : ℝ)
    (n m : ℕ) : Set (Path d × Path d) :=
  {P | (∃ r, 0 < r ∧ r ≤ H ∧ P.1 ∈ RecordIndexPrefix ℓ r n ∧
      P.2 ∈ RecordIndexPrefix ℓ r m) ∧
    dot (realPosition (P.1 n)) ℓ = dot (realPosition (P.2 m)) ℓ ∧
    z < |signedCoordinate e (P.1 n)-signedCoordinate e (P.2 m)|}

def FirstPairRecordDeviation {d : ℕ} (ℓ : Vector d) (e : Direction d) (H : ℕ) (z : ℝ)
    (q : ℕ × ℕ) : Set (Path d × Path d) :=
  PairRecordDeviation ℓ e H z q.1 q.2 ∩
    {P | ∀ j < q.1, ∀ k < q.2, P ∉ PairRecordDeviation ℓ e H z j k}

lemma measurableSet_pairRecordDeviation {d : ℕ} (ℓ : Vector d) (e : Direction d)
    (H : ℕ) (z : ℝ) (n m : ℕ) : MeasurableSet (PairRecordDeviation ℓ e H z n m) := by
  simp only [PairRecordDeviation,Set.ofPred_and,Set.ofPred_exists]
  refine (MeasurableSet.iUnion fun r => (MeasurableSet.const _).inter
    ((MeasurableSet.const _).inter ((measurableSet_recordIndexPrefix ℓ r n).prod
      (measurableSet_recordIndexPrefix ℓ r m)))).inter ?_
  exact (measurableSet_eq_fun
    ((measurable_of_countable (fun x : Lattice d => dot (realPosition x) ℓ)).comp
      ((measurable_pi_apply n).comp measurable_fst))
    ((measurable_of_countable (fun x : Lattice d => dot (realPosition x) ℓ)).comp
      ((measurable_pi_apply m).comp measurable_snd))).inter
    (measurableSet_lt measurable_const
      (((measurable_of_countable (signedCoordinate e)).comp
        ((measurable_pi_apply n).comp measurable_fst)).sub
       ((measurable_of_countable (signedCoordinate e)).comp
        ((measurable_pi_apply m).comp measurable_snd))).abs)

lemma measurableSet_firstPairRecordDeviation {d : ℕ} (ℓ : Vector d) (e : Direction d)
    (H : ℕ) (z : ℝ) (q : ℕ × ℕ) : MeasurableSet (FirstPairRecordDeviation ℓ e H z q) := by
  simp only [FirstPairRecordDeviation,Set.ofPred_forall]
  exact (measurableSet_pairRecordDeviation ℓ e H z q.1 q.2).inter
    (MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      MeasurableSet.iInter fun k => MeasurableSet.iInter fun _ =>
        (measurableSet_pairRecordDeviation ℓ e H z j k).compl)

lemma pairRecordDeviation_prefix {d : ℕ} (ℓ : Vector d) (e : Direction d)
    (H : ℕ) (z : ℝ) {j k n m : ℕ} (hj : j ≤ n) (hk : k ≤ m) :
    PairPrefixDetermined n m (PairRecordDeviation ℓ e H z j k) := by
  intro P Q h1 h2
  have hrec1 (r : ℕ) := recordIndexPrefix_prefix ℓ r j P.1 Q.1 (fun i hi => h1 i (hi.trans hj))
  have hrec2 (r : ℕ) := recordIndexPrefix_prefix ℓ r k P.2 Q.2 (fun i hi => h2 i (hi.trans hk))
  simp only [PairRecordDeviation,Set.mem_ofPred_eq,hrec1,hrec2,h1 j hj,h2 k hk]

lemma firstPairRecordDeviation_prefix {d : ℕ} (ℓ : Vector d) (e : Direction d)
    (H : ℕ) (z : ℝ) (q : ℕ × ℕ) :
    PairPrefixDetermined q.1 q.2 (FirstPairRecordDeviation ℓ e H z q) := by
  intro P Q h1 h2
  have he := pairRecordDeviation_prefix ℓ e H z le_rfl le_rfl P Q h1 h2
  simp only [FirstPairRecordDeviation,Set.mem_inter_iff,Set.mem_ofPred_eq,he]
  apply and_congr Iff.rfl
  exact forall_congr' fun j => forall_congr' fun hj => forall_congr' fun k =>
    forall_congr' fun hk => not_congr
      (pairRecordDeviation_prefix ℓ e H z hj.le hk.le P Q h1 h2)

lemma recordIndexPrefix_time_lt_iff {d : ℕ} (ℓ : Vector d) (X : Path d)
    {r s n m : ℕ} (hn : X ∈ RecordIndexPrefix ℓ r n)
    (hm : X ∈ RecordIndexPrefix ℓ s m) : n < m ↔ r < s := by
  constructor
  · intro h
    have hh := recordCount_lt_of_strictRecord ℓ X h hm.2.1
    simpa only [hn.2.2.1,hm.2.2.1] using hh
  · intro h
    by_contra hh
    have he := recordCount_mono ℓ X (Nat.le_of_not_gt hh)
    rw [hn.2.2.1,hm.2.2.1] at he
    omega

lemma pairRecordDeviation_time_order {d : ℕ} (ℓ : Vector d) (e : Direction d)
    (H : ℕ) (z : ℝ) {P : Path d × Path d} {n m j k : ℕ}
    (hP : P ∈ PairRecordDeviation ℓ e H z n m)
    (hQ : P ∈ PairRecordDeviation ℓ e H z j k) :
    (n < j ↔ m < k) ∧ (n = j ↔ m = k) := by
  obtain ⟨⟨r,_,_,hr,hr'⟩,_⟩ := hP
  obtain ⟨⟨s,_,_,hs,hs'⟩,_⟩ := hQ
  have h1 := recordIndexPrefix_time_lt_iff ℓ P.1 hr hs
  have h2 := recordIndexPrefix_time_lt_iff ℓ P.2 hr' hs'
  refine ⟨h1.trans h2.symm,?_⟩
  have h3 := recordIndexPrefix_time_lt_iff ℓ P.1 hs hr
  have h4 := recordIndexPrefix_time_lt_iff ℓ P.2 hs' hr'
  omega

lemma firstPairRecordDeviation_disjoint {d : ℕ} (ℓ : Vector d) (e : Direction d)
    (H : ℕ) (z : ℝ) : Pairwise (fun q q' =>
      Disjoint (FirstPairRecordDeviation ℓ e H z q) (FirstPairRecordDeviation ℓ e H z q')) := by
  intro q q' hne
  apply Set.disjoint_left.mpr
  intro P hP hQ
  have hord := pairRecordDeviation_time_order ℓ e H z hP.1 hQ.1
  rcases lt_trichotomy q.1 q'.1 with h | h | h
  · exact hQ.2 q.1 h q.2 (hord.1.mp h) hP.1
  · exact hne (Prod.ext h (hord.2.mp h))
  · have hh := (pairRecordDeviation_time_order ℓ e H z hQ.1 hP.1).1.mp h
    exact hP.2 q'.1 h q'.2 hh hQ.1

lemma iUnion_firstPairRecordDeviation {d : ℕ} (ℓ : Vector d) (e : Direction d)
    (H : ℕ) (z : ℝ) :
    (⋃ q, FirstPairRecordDeviation ℓ e H z q) = ⋃ n, ⋃ m, PairRecordDeviation ℓ e H z n m := by
  classical
  apply Set.Subset.antisymm
  · intro P hP
    obtain ⟨q,hq⟩ := Set.mem_iUnion.mp hP
    exact Set.mem_iUnion.mpr ⟨q.1,Set.mem_iUnion.mpr ⟨q.2,hq.1⟩⟩
  · intro P hP
    have hx : ∃ n, ∃ m, P ∈ PairRecordDeviation ℓ e H z n m := by
      simpa only [Set.mem_iUnion] using hP
    obtain ⟨m,hm⟩ := Nat.find_spec hx
    apply Set.mem_iUnion.mpr
    refine ⟨(Nat.find hx,m),hm,?_⟩
    intro j hj k _ h
    exact Nat.find_min hx hj ⟨k,h⟩

lemma firstPairRecordDeviation_force_lower {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0)
    (e : Direction d) (H : ℕ) (z : ℝ) (q : ℕ × ℕ) :
    independentPairLaw ν (FirstPairRecordDeviation ℓ e H z q) ≤
      independentConditionedPairLaw ν ℓ
        (FirstPairRecordDeviation ℓ e H z q ∩ (FutureNoDrop ℓ q.1 ×ˢ FutureNoDrop ℓ q.2)) := by
  by_cases hq : 0 < q.1 ∧ 0 < q.2
  · apply independent_conditioned_record_prefix_lower ν ℓ hp hq.1 hq.2 _
      (measurableSet_firstPairRecordDeviation ℓ e H z q)
      (firstPairRecordDeviation_prefix ℓ e H z q)
    · intro P hP
      obtain ⟨r,_,_,hr,hr'⟩ := hP.1.1
      exact ⟨hr.2.1,hr'.2.1,hP.1.2.1⟩
    · rintro P ⟨hP,hF⟩
      obtain ⟨r,_,_,hr,hr'⟩ := hP.1.1
      exact ⟨recordIndexPrefix_noDrop ℓ r q.1 ⟨hr,hF.1⟩,
        recordIndexPrefix_noDrop ℓ r q.2 ⟨hr',hF.2⟩⟩
  · have he : FirstPairRecordDeviation ℓ e H z q = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro P hP
      obtain ⟨r,_,_,hr,hr'⟩ := hP.1.1
      exact hq ⟨hr.1,hr'.1⟩
    rw [he,measure_empty]
    exact bot_le

lemma independent_pair_deviation_transfer {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1) (e : Direction d) (H : ℕ) (z : ℝ) :
    (annealedLaw ν (NoDrop ℓ 0))^2 * independentConditionedPairLaw ν ℓ
      (⋃ n, ⋃ m, PairRecordDeviation ℓ e H z n m) ≤
    independentConditionedPairLaw ν ℓ
      {P | z < partialSumMax (fun n => commonIncrementProcess ℓ e n P) H} := by
  have hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ hp
  let A := FirstPairRecordDeviation ℓ e H z
  let B (q : ℕ × ℕ) := A q ∩ (FutureNoDrop ℓ q.1 ×ˢ FutureNoDrop ℓ q.2)
  have hAm (q) : MeasurableSet (A q) := measurableSet_firstPairRecordDeviation ℓ e H z q
  have hBm (q) : MeasurableSet (B q) := (hAm q).inter
    ((measurableSet_futureNoDrop ℓ q.1).prod (measurableSet_futureNoDrop ℓ q.2))
  have hBd : Pairwise (fun q q' => Disjoint (B q) (B q')) := by
    intro q q' hne
    exact (firstPairRecordDeviation_disjoint ℓ e H z hne).mono
      Set.inter_subset_left Set.inter_subset_left
  rw [← iUnion_firstPairRecordDeviation]
  calc
    _ ≤ independentPairLaw ν (⋃ q, A q) :=
      independentConditionedPairLaw_le_raw ν ℓ hp _ (MeasurableSet.iUnion hAm)
    _ = ∑' q, independentPairLaw ν (A q) :=
      measure_iUnion (firstPairRecordDeviation_disjoint ℓ e H z) hAm
    _ ≤ ∑' q, independentConditionedPairLaw ν ℓ (B q) :=
      ENNReal.tsum_le_tsum (firstPairRecordDeviation_force_lower ν ℓ hp e H z)
    _ = independentConditionedPairLaw ν ℓ (⋃ q, B q) := (measure_iUnion hBd hBm).symm
    _ ≤ _ := by
      apply measure_mono_ae
      have hac := conditionedLaw_absolutelyContinuous ν ℓ
      have h0 := (Measure.quasiMeasurePreserving_fst.ae (hac.ae_le (annealed_initial ν))).and
        (Measure.quasiMeasurePreserving_snd.ae (hac.ae_le (annealed_initial ν)))
      filter_upwards [h0,independent_conditioned_all_firstPairWords ν ℓ htrans height hproj hstep]
        with P h0 hP hB
      obtain ⟨q,hq⟩ := Set.mem_iUnion.mp hB
      obtain ⟨r,_,hrH,hr,hr'⟩ := hq.1.1.1
      have htrue : CommonTrueRecord ℓ P q.1 q.2 :=
        ⟨⟨hr.2.1,hq.2.1⟩,⟨hr'.2.1,hq.2.2⟩,hq.1.1.2.1⟩
      exact hq.1.1.2.2.trans_le (common_record_gap_le_max ℓ e P h0.1 h0.2 hP htrue
        (hr.2.2.1.trans_le hrH))

lemma measurableSet_pairIndexDeviation {d : ℕ} (ℓ : Vector d) (e : Direction d)
    (H : ℕ) (z : ℝ) : MeasurableSet
      {P : Path d × Path d | ∃ r, 0 < r ∧ r ≤ H ∧
        z < |signedCoordinate e (recordIndexPosition ℓ r P.1) -
          signedCoordinate e (recordIndexPosition ℓ r P.2)|} := by
  simp only [Set.ofPred_exists,Set.ofPred_and]
  refine MeasurableSet.iUnion fun r => (MeasurableSet.const _).inter
    ((MeasurableSet.const _).inter ?_)
  exact measurableSet_lt measurable_const
    ((((measurable_of_countable (signedCoordinate e)).comp
      (measurable_recordIndexPosition ℓ r)).comp measurable_fst).sub
     (((measurable_of_countable (signedCoordinate e)).comp
      (measurable_recordIndexPosition ℓ r)).comp measurable_snd)).abs

lemma independent_firstHit_pair_maximum {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1) (e : Direction d) (H : ℕ) (z : ℝ) :
    (annealedLaw ν (NoDrop ℓ 0))^2 * independentConditionedPairLaw ν ℓ
      {P | ∃ r, 0 < r ∧ r ≤ H ∧
        z < |signedCoordinate e (recordIndexPosition ℓ r P.1) -
          signedCoordinate e (recordIndexPosition ℓ r P.2)|} ≤
    independentConditionedPairLaw ν ℓ
      {P | z < partialSumMax (fun n => commonIncrementProcess ℓ e n P) H} := by
  apply le_trans ?_ (independent_pair_deviation_transfer ν ℓ htrans
    height hproj hstep e H z)
  apply mul_le_mul_right
  have hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ hp
  have hs : ∀ᵐ X ∂conditionedLaw ν ℓ, ∀ r, 0 < r →
      X ∈ RecordIndexPrefix ℓ r (recordIndexTime ℓ r X) :=
    ae_all_iff.mpr fun r => ae_all_iff.mpr fun hr =>
      conditioned_recordIndexTime_spec ν ℓ htrans hr
  have hac := conditionedLaw_absolutelyContinuous ν ℓ
  have h0 := (Measure.quasiMeasurePreserving_fst.ae (hac.ae_le (annealed_initial ν))).and
    (Measure.quasiMeasurePreserving_snd.ae (hac.ae_le (annealed_initial ν)))
  have hNN := (Measure.quasiMeasurePreserving_fst.ae (hac.ae_le (annealed_nearest_neighbor ν))).and
    (Measure.quasiMeasurePreserving_snd.ae (hac.ae_le (annealed_nearest_neighbor ν)))
  have hs' := (Measure.quasiMeasurePreserving_fst.ae hs).and
    (Measure.quasiMeasurePreserving_snd.ae hs)
  apply measure_mono_ae
  filter_upwards [h0,hNN,hs'] with P h0 hNN hs hP
  obtain ⟨r,hr,hrH,hrz⟩ := hP
  have h1 := hs.1 r hr
  have h2 := hs.2 r hr
  have hs1 (j : ℕ) : height (P.1 (j+1)) ≤ height (P.1 j)+1 := by
    obtain ⟨v,hv⟩ := hNN.1 j
    rw [hv]; exact hstep _ _
  have hs2 (j : ℕ) : height (P.2 (j+1)) ≤ height (P.2 j)+1 := by
    obtain ⟨v,hv⟩ := hNN.2 j
    rw [hv]; exact hstep _ _
  refine Set.mem_iUnion.mpr ⟨recordIndexTime ℓ r P.1,Set.mem_iUnion.mpr
    ⟨recordIndexTime ℓ r P.2,⟨r,hr,hrH,h1,h2⟩,?_,hrz⟩⟩
  rw [hproj,hproj,recordCount_eq_height_at_record ℓ height hproj P.1 hs1 h1.2.1,
    recordCount_eq_height_at_record ℓ height hproj P.2 hs2 h2.2.1,h0.1,h0.2,h1.2.2.1,h2.2.2.1]

lemma exists_integer_median (μ : Measure ℤ) [IsProbabilityMeasure μ] :
    ∃ b : ℤ, (1/2 : ℝ≥0∞) ≤ μ (Set.Iic b) ∧ (1/2 : ℝ≥0∞) ≤ μ (Set.Ici b) := by
  have hhalf : (1/2 : ℝ≥0∞) < 1 := by norm_num
  have ht : ∀ᶠ z : ℤ in atTop, (1/2 : ℝ≥0∞) < μ (Set.Iic z) :=
    (tendsto_measure_Iic_atTop μ).eventually (Ioi_mem_nhds (by simpa only [measure_univ] using hhalf))
  have hb : ∀ᶠ z : ℤ in atBot, (1/2 : ℝ≥0∞) < μ (Set.Ici z) :=
    (tendsto_measure_Ici_atBot μ).eventually (Ioi_mem_nhds (by simpa only [measure_univ] using hhalf))
  obtain ⟨b, hb⟩ := hb.exists
  have hbound : ∀ z : ℤ, (1/2 : ℝ≥0∞) ≤ μ (Set.Iic z) → b ≤ z := by
    intro z hz
    by_contra h
    have hzb : z < b := lt_of_not_ge h
    have hdis : Disjoint (Set.Iic z) (Set.Ici b) := Set.disjoint_left.mpr
      (fun x hx hx' => (not_le_of_gt hzb) (hx'.trans hx))
    have hadd : μ (Set.Iic z) + μ (Set.Ici b) ≤ 1 := by
      rw [← measure_union hdis measurableSet_Ici]
      exact prob_le_one
    have hlt : (1 : ℝ≥0∞) < μ (Set.Iic z) + μ (Set.Ici b) := by
      calc
        1 = (1/2 : ℝ≥0∞) + (1/2 : ℝ≥0∞) := (ENNReal.add_halves 1).symm
        _ < μ (Set.Iic z) + μ (Set.Ici b) := ENNReal.add_lt_add_of_le_of_lt (by simp) hz hb
    exact (not_lt_of_ge hadd) hlt
  obtain ⟨m, hm, hmin⟩ := Int.exists_least_of_bdd ⟨b,hbound⟩ (ht.exists.imp fun z hz => hz.le)
  refine ⟨m,hm,?_⟩
  have hprev : μ (Set.Iic (m-1)) < (1/2 : ℝ≥0∞) := by
    by_contra hp
    have := hmin (m-1) (le_of_not_gt hp)
    omega
  have hun : Set.Iic (m-1) ∪ Set.Ici m = Set.univ := by
    ext z
    simp only [Set.mem_union,Set.mem_Iic,Set.mem_Ici,Set.mem_univ,iff_true]
    omega
  have hdis : Disjoint (Set.Iic (m-1)) (Set.Ici m) := Set.disjoint_left.mpr (fun z hz hz' => by
    simp only [Set.mem_Iic,Set.mem_Ici] at hz hz'
    omega)
  have hadd : μ (Set.Iic (m-1)) + μ (Set.Ici m) = 1 := by
    rw [← measure_union hdis measurableSet_Ici,hun,measure_univ]
  by_contra hh
  have hm' := lt_of_not_ge hh
  have hlt := ENNReal.add_lt_add hprev hm'
  rw [hadd] at hlt
  rw [ENNReal.add_halves] at hlt
  exact (lt_irrefl _) hlt

end DirectionalTransience
end
end

end OAI

import Mathlib
import OAI.Probability.Ballisticity.Crossings.FirstHitPairGap

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

def AlignedRecordPrefix {d : ℕ} (ℓ : Vector d) (q : ℕ × ℕ) : Set (Path d × Path d) :=
  {P | (∃ r, 0 < r ∧ P.1 ∈ RecordIndexPrefix ℓ r q.1 ∧
    P.2 ∈ RecordIndexPrefix ℓ r q.2) ∧
    dot (realPosition (P.1 q.1)) ℓ = dot (realPosition (P.2 q.2)) ℓ}

lemma alignedRecordPrefix_order {d : ℕ} (ℓ : Vector d) {P : Path d × Path d} {q q' : ℕ × ℕ}
    (hP : P ∈ AlignedRecordPrefix ℓ q) (hQ : P ∈ AlignedRecordPrefix ℓ q') :
    (q.1 < q'.1 ↔ q.2 < q'.2) ∧ (q.1 = q'.1 ↔ q.2 = q'.2) := by
  obtain ⟨⟨r,_,hr,hr'⟩,_⟩ := hP
  obtain ⟨⟨s,_,hs,hs'⟩,_⟩ := hQ
  have h1 := recordIndexPrefix_time_lt_iff ℓ P.1 hr hs
  have h2 := recordIndexPrefix_time_lt_iff ℓ P.2 hr' hs'
  have h3 := recordIndexPrefix_time_lt_iff ℓ P.1 hs hr
  have h4 := recordIndexPrefix_time_lt_iff ℓ P.2 hs' hr'
  exact ⟨h1.trans h2.symm,by omega⟩

def FirstPairTest {α : Type*} (A : ℕ × ℕ → Set α) (q : ℕ × ℕ) : Set α :=
  A q ∩ {P | ∀ j < q.1, ∀ k < q.2, P ∉ A (j,k)}

lemma measurableSet_firstPairTest {α : Type*} [MeasurableSpace α]
    (A : ℕ × ℕ → Set α) (hA : ∀ q, MeasurableSet (A q)) (q : ℕ × ℕ) :
    MeasurableSet (FirstPairTest A q) := by
  simp only [FirstPairTest,Set.ofPred_forall]
  exact (hA q).inter (MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ =>
    MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ => (hA _).compl)

lemma firstPairTest_prefix {d : ℕ} (A : ℕ × ℕ → Set (Path d × Path d))
    (hA : ∀ q, PairPrefixDetermined q.1 q.2 (A q)) (q : ℕ × ℕ) :
    PairPrefixDetermined q.1 q.2 (FirstPairTest A q) := by
  intro P Q h1 h2
  simp only [FirstPairTest,Set.mem_inter_iff,Set.mem_ofPred_eq,hA q P Q h1 h2]
  apply and_congr Iff.rfl
  exact forall_congr' fun j => forall_congr' fun hj => forall_congr' fun k =>
    forall_congr' fun hk => not_congr (hA (j,k) P Q
      (fun i hi => h1 i (hi.trans hj.le)) (fun i hi => h2 i (hi.trans hk.le)))

lemma firstPairTest_disjoint {d : ℕ} (ℓ : Vector d) (A : ℕ × ℕ → Set (Path d × Path d))
    (hA : ∀ q, A q ⊆ AlignedRecordPrefix ℓ q) :
    Pairwise (fun q q' => Disjoint (FirstPairTest A q) (FirstPairTest A q')) := by
  intro q q' hne
  apply Set.disjoint_left.mpr
  intro P hP hQ
  have hord := alignedRecordPrefix_order ℓ (hA q hP.1) (hA q' hQ.1)
  rcases lt_trichotomy q.1 q'.1 with h | h | h
  · exact hQ.2 q.1 h q.2 (hord.1.mp h) hP.1
  · exact hne (Prod.ext h (hord.2.mp h))
  · exact hP.2 q'.1 h q'.2 ((alignedRecordPrefix_order ℓ (hA q' hQ.1) (hA q hP.1)).1.mp h) hQ.1

lemma iUnion_firstPairTest {α : Type*} (A : ℕ × ℕ → Set α) :
    (⋃ q, FirstPairTest A q) = ⋃ q, A q := by
  classical
  apply Set.Subset.antisymm
  · intro P hP
    obtain ⟨q,hq⟩ := Set.mem_iUnion.mp hP
    exact Set.mem_iUnion.mpr ⟨q,hq.1⟩
  · intro P hP
    have hx : ∃ n, ∃ m, P ∈ A (n,m) := by
      obtain ⟨⟨n,m⟩,h⟩ := Set.mem_iUnion.mp hP
      exact ⟨n,m,h⟩
    obtain ⟨m,hm⟩ := Nat.find_spec hx
    exact Set.mem_iUnion.mpr ⟨(Nat.find hx,m),hm,fun j hj k _ h => Nat.find_min hx hj ⟨k,h⟩⟩

theorem independent_exact_cut_transfer {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0)
    (A : ℕ × ℕ → Set (Path d × Path d)) (hAm : ∀ q, MeasurableSet (A q))
    (hAp : ∀ q, PairPrefixDetermined q.1 q.2 (A q))
    (hA : ∀ q, A q ⊆ AlignedRecordPrefix ℓ q) :
    (annealedLaw ν (NoDrop ℓ 0))^2 * independentConditionedPairLaw ν ℓ (⋃ q, A q) ≤
      independentConditionedPairLaw ν ℓ
        (⋃ q, A q ∩ {P | CommonTrueRecord ℓ P q.1 q.2}) := by
  let F := FirstPairTest A
  let B (q : ℕ × ℕ) := F q ∩ (FutureNoDrop ℓ q.1 ×ˢ FutureNoDrop ℓ q.2)
  have hFm (q) : MeasurableSet (F q) := measurableSet_firstPairTest A hAm q
  have hBm (q) : MeasurableSet (B q) := (hFm q).inter
    ((measurableSet_futureNoDrop ℓ q.1).prod (measurableSet_futureNoDrop ℓ q.2))
  have hBd : Pairwise (fun q q' => Disjoint (B q) (B q')) := by
    intro q q' hne
    exact (firstPairTest_disjoint ℓ A hA hne).mono Set.inter_subset_left Set.inter_subset_left
  have hforce (q) : independentPairLaw ν (F q) ≤ independentConditionedPairLaw ν ℓ (B q) := by
    by_cases hq : 0 < q.1 ∧ 0 < q.2
    · apply independent_conditioned_record_prefix_lower ν ℓ hp hq.1 hq.2 _
        (hFm q) (firstPairTest_prefix A hAp q)
      · intro P hP
        obtain ⟨⟨r,_,hr,hr'⟩,he⟩ := hA q hP.1
        exact ⟨hr.2.1,hr'.2.1,he⟩
      · rintro P ⟨hP,hD⟩
        obtain ⟨⟨r,_,hr,hr'⟩,_⟩ := hA q hP.1
        exact ⟨recordIndexPrefix_noDrop ℓ r q.1 ⟨hr,hD.1⟩,
          recordIndexPrefix_noDrop ℓ r q.2 ⟨hr',hD.2⟩⟩
    · have he : F q = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro P hP
        obtain ⟨⟨r,_,hr,hr'⟩,_⟩ := hA q hP.1
        exact hq ⟨hr.1,hr'.1⟩
      rw [he,measure_empty]
      exact bot_le
  rw [← iUnion_firstPairTest A]
  calc
    _ ≤ independentPairLaw ν (⋃ q, F q) :=
      independentConditionedPairLaw_le_raw ν ℓ hp _ (MeasurableSet.iUnion hFm)
    _ = ∑' q, independentPairLaw ν (F q) := measure_iUnion (firstPairTest_disjoint ℓ A hA) hFm
    _ ≤ ∑' q, independentConditionedPairLaw ν ℓ (B q) := ENNReal.tsum_le_tsum hforce
    _ = independentConditionedPairLaw ν ℓ (⋃ q, B q) := (measure_iUnion hBd hBm).symm
    _ ≤ _ := by
      apply measure_mono
      intro P hP
      obtain ⟨q,hq⟩ := Set.mem_iUnion.mp hP
      obtain ⟨⟨r,_,hr,hr'⟩,he⟩ := hA q hq.1.1
      exact Set.mem_iUnion.mpr ⟨q,hq.1.1,⟨hr.2.1,hq.2.1⟩,⟨hr'.2.1,hq.2.2⟩,he⟩

def RecordOrZeroPrefix {d : ℕ} (ℓ : Vector d) (r n : ℕ) : Set (Path d) :=
  if r = 0 then {_X | n = 0} else RecordIndexPrefix ℓ r n

lemma measurableSet_recordOrZeroPrefix {d : ℕ} (ℓ : Vector d) (r n : ℕ) :
    MeasurableSet (RecordOrZeroPrefix ℓ r n) := by
  unfold RecordOrZeroPrefix
  split_ifs
  · exact MeasurableSet.const _
  · exact measurableSet_recordIndexPrefix ℓ r n

lemma recordOrZeroPrefix_prefix {d : ℕ} (ℓ : Vector d) (r n : ℕ) :
    PrefixDetermined n (RecordOrZeroPrefix ℓ r n) := by
  intro X Y hXY
  unfold RecordOrZeroPrefix
  split_ifs
  · rfl
  · exact recordIndexPrefix_prefix ℓ r n X Y hXY

lemma recordOrZeroPrefix_time {d : ℕ} (ℓ : Vector d) {r n : ℕ} {X : Path d}
    (hX : X ∈ RecordOrZeroPrefix ℓ r n) : recordIndexTime ℓ r X = n := by
  by_cases hr : r = 0
  · subst r
    have : n = 0 := by simpa [RecordOrZeroPrefix] using hX
    rw [this,recordIndexTime_zero]
  · exact recordIndexTime_eq ℓ r n X (by simpa [RecordOrZeroPrefix,hr] using hX)

def PairOscillationTest {d : ℕ} (ℓ : Vector d) (e : Direction d)
    (J : Set (ℕ × ℕ)) (z : ℝ) (q : ℕ × ℕ) : Set (Path d × Path d) :=
  {P | ∃ s r a b : ℕ, (s,r) ∈ J ∧ 0 < r ∧ a ≤ q.1 ∧ b ≤ q.2 ∧
    P.1 ∈ RecordIndexPrefix ℓ r q.1 ∧ P.2 ∈ RecordIndexPrefix ℓ r q.2 ∧
    P.1 ∈ RecordOrZeroPrefix ℓ s a ∧ P.2 ∈ RecordOrZeroPrefix ℓ s b ∧
    dot (realPosition (P.1 q.1)) ℓ = dot (realPosition (P.2 q.2)) ℓ ∧
    z < |(signedCoordinate e (P.1 q.1)-signedCoordinate e (P.2 q.2))-
      (signedCoordinate e (P.1 a)-signedCoordinate e (P.2 b))|}

lemma measurableSet_pairOscillationTest {d : ℕ} (ℓ : Vector d) (e : Direction d)
    (J : Set (ℕ × ℕ)) (z : ℝ) (q : ℕ × ℕ) : MeasurableSet (PairOscillationTest ℓ e J z q) := by
  have hm1 (n : ℕ) : Measurable (fun P : Path d × Path d => signedCoordinate e (P.1 n)) :=
    (measurable_of_countable (signedCoordinate e)).comp ((measurable_pi_apply n).comp measurable_fst)
  have hm2 (n : ℕ) : Measurable (fun P : Path d × Path d => signedCoordinate e (P.2 n)) :=
    (measurable_of_countable (signedCoordinate e)).comp ((measurable_pi_apply n).comp measurable_snd)
  have hh1 : Measurable (fun P : Path d × Path d => dot (realPosition (P.1 q.1)) ℓ) :=
    (measurable_of_countable (fun x : Lattice d => dot (realPosition x) ℓ)).comp ((measurable_pi_apply q.1).comp measurable_fst)
  have hh2 : Measurable (fun P : Path d × Path d => dot (realPosition (P.2 q.2)) ℓ) :=
    (measurable_of_countable (fun x : Lattice d => dot (realPosition x) ℓ)).comp ((measurable_pi_apply q.2).comp measurable_snd)
  simp only [PairOscillationTest,Set.ofPred_exists,Set.ofPred_and]
  refine MeasurableSet.iUnion fun s => MeasurableSet.iUnion fun r =>
    MeasurableSet.iUnion fun a => MeasurableSet.iUnion fun b =>
    (MeasurableSet.const _).inter ((MeasurableSet.const _).inter
    ((MeasurableSet.const _).inter ((MeasurableSet.const _).inter ?_)))
  exact (measurable_fst (measurableSet_recordIndexPrefix ℓ r q.1)).inter
    ((measurable_snd (measurableSet_recordIndexPrefix ℓ r q.2)).inter
    ((measurable_fst (measurableSet_recordOrZeroPrefix ℓ s a)).inter
    ((measurable_snd (measurableSet_recordOrZeroPrefix ℓ s b)).inter
    ((measurableSet_eq_fun hh1 hh2).inter
    (measurableSet_lt measurable_const (((hm1 q.1).sub (hm2 q.2)).sub ((hm1 a).sub (hm2 b))).abs)))))

lemma pairOscillationTest_prefix {d : ℕ} (ℓ : Vector d) (e : Direction d)
    (J : Set (ℕ × ℕ)) (z : ℝ) (q : ℕ × ℕ) :
    PairPrefixDetermined q.1 q.2 (PairOscillationTest ℓ e J z q) := by
  have hdir (P Q : Path d × Path d) (h1 : ∀ n ≤ q.1, P.1 n = Q.1 n)
      (h2 : ∀ n ≤ q.2, P.2 n = Q.2 n) (hP : P ∈ PairOscillationTest ℓ e J z q) :
      Q ∈ PairOscillationTest ℓ e J z q := by
    obtain ⟨s,r,a,b,hJ,hr,ha,hb,hr1,hr2,hs1,hs2,he,hz⟩ := hP
    refine ⟨s,r,a,b,hJ,hr,ha,hb,
      (recordIndexPrefix_prefix ℓ r q.1 P.1 Q.1 h1).mp hr1,
      (recordIndexPrefix_prefix ℓ r q.2 P.2 Q.2 h2).mp hr2,
      (recordOrZeroPrefix_prefix ℓ s a P.1 Q.1 (fun n hn => h1 n (hn.trans ha))).mp hs1,
      (recordOrZeroPrefix_prefix ℓ s b P.2 Q.2 (fun n hn => h2 n (hn.trans hb))).mp hs2,?_,?_⟩
    · rwa [← h1 q.1 le_rfl,← h2 q.2 le_rfl]
    · rwa [← h1 q.1 le_rfl,← h2 q.2 le_rfl,← h1 a ha,← h2 b hb]
  intro P Q h1 h2
  exact ⟨hdir P Q h1 h2,hdir Q P (fun n hn => (h1 n hn).symm) (fun n hn => (h2 n hn).symm)⟩

lemma pairOscillationTest_aligned {d : ℕ} (ℓ : Vector d) (e : Direction d)
    (J : Set (ℕ × ℕ)) (z : ℝ) (q : ℕ × ℕ) :
    PairOscillationTest ℓ e J z q ⊆ AlignedRecordPrefix ℓ q := by
  rintro P ⟨_,r,_,_,_,hr,_,_,hr1,hr2,_,_,he,_⟩
  exact ⟨⟨r,hr,hr1,hr2⟩,he⟩

lemma independent_firstHit_aligned {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1) :
    ∀ᵐ P ∂independentConditionedPairLaw ν ℓ, ∀ r, 0 < r →
      P.1 ∈ RecordIndexPrefix ℓ r (recordIndexTime ℓ r P.1) ∧
      P.2 ∈ RecordIndexPrefix ℓ r (recordIndexTime ℓ r P.2) ∧
      dot (realPosition (recordIndexPosition ℓ r P.1)) ℓ =
        dot (realPosition (recordIndexPosition ℓ r P.2)) ℓ := by
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ
    (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
  have hs : ∀ᵐ X ∂conditionedLaw ν ℓ, ∀ r, 0 < r →
      X ∈ RecordIndexPrefix ℓ r (recordIndexTime ℓ r X) :=
    ae_all_iff.mpr fun r => ae_all_iff.mpr fun hr => conditioned_recordIndexTime_spec ν ℓ htrans hr
  have hac := conditionedLaw_absolutelyContinuous ν ℓ
  have h0 := (Measure.quasiMeasurePreserving_fst.ae (hac.ae_le (annealed_initial ν))).and
    (Measure.quasiMeasurePreserving_snd.ae (hac.ae_le (annealed_initial ν)))
  have hNN := (Measure.quasiMeasurePreserving_fst.ae (hac.ae_le (annealed_nearest_neighbor ν))).and
    (Measure.quasiMeasurePreserving_snd.ae (hac.ae_le (annealed_nearest_neighbor ν)))
  have hs' := (Measure.quasiMeasurePreserving_fst.ae hs).and (Measure.quasiMeasurePreserving_snd.ae hs)
  filter_upwards [h0,hNN,hs'] with P h0 hNN hs r hr
  have h1 := hs.1 r hr
  have h2 := hs.2 r hr
  refine ⟨h1,h2,?_⟩
  have hs1 (j : ℕ) : height (P.1 (j+1)) ≤ height (P.1 j)+1 := by
    obtain ⟨v,hv⟩ := hNN.1 j
    rw [hv]; exact hstep _ _
  have hs2 (j : ℕ) : height (P.2 (j+1)) ≤ height (P.2 j)+1 := by
    obtain ⟨v,hv⟩ := hNN.2 j
    rw [hv]; exact hstep _ _
  change dot (realPosition (P.1 _)) ℓ = dot (realPosition (P.2 _)) ℓ
  rw [hproj,hproj,recordCount_eq_height_at_record ℓ height hproj P.1 hs1 h1.2.1,
    recordCount_eq_height_at_record ℓ height hproj P.2 hs2 h2.2.1,h0.1,h0.2,h1.2.2.1,h2.2.2.1]

lemma firstHitPairGap_prefix_test {d : ℕ} (ℓ : Vector d) (e : Direction d)
    (J : Set (ℕ × ℕ)) (hJ : ∀ sr ∈ J, sr.1 ≤ sr.2) {z : ℝ} (hz : 0 ≤ z)
    {P : Path d × Path d}
    (hs : ∀ r, 0 < r → P.1 ∈ RecordIndexPrefix ℓ r (recordIndexTime ℓ r P.1) ∧
      P.2 ∈ RecordIndexPrefix ℓ r (recordIndexTime ℓ r P.2) ∧
      dot (realPosition (recordIndexPosition ℓ r P.1)) ℓ =
        dot (realPosition (recordIndexPosition ℓ r P.2)) ℓ)
    {s r : ℕ} (hsr : (s,r) ∈ J) (hbad : z < |firstHitPairGap ℓ e r P-firstHitPairGap ℓ e s P|) :
    P ∈ PairOscillationTest ℓ e J z (recordIndexTime ℓ r P.1,recordIndexTime ℓ r P.2) := by
  have hsr' := hJ _ hsr
  have hr : 0 < r := by
    by_contra! hr
    have : s = r := by omega
    simp only [this,sub_self,abs_zero] at hbad
    exact (not_lt_of_ge hz) hbad
  have h1 := hs r hr
  have hprev (X : Path d) (hX : ∀ a, 0 < a → X ∈ RecordIndexPrefix ℓ a (recordIndexTime ℓ a X)) :
      recordIndexTime ℓ s X ≤ recordIndexTime ℓ r X ∧
      X ∈ RecordOrZeroPrefix ℓ s (recordIndexTime ℓ s X) := by
    by_cases hs0 : s = 0
    · simp [hs0,recordIndexTime_zero,RecordOrZeroPrefix]
    · refine ⟨?_,by simpa [RecordOrZeroPrefix,hs0] using hX s (Nat.pos_of_ne_zero hs0)⟩
      by_contra! hh
      have := (recordIndexPrefix_time_lt_iff ℓ X (hX r hr) (hX s (Nat.pos_of_ne_zero hs0))).mp hh
      omega
  have hp1 := hprev P.1 (fun a ha => (hs a ha).1)
  have hp2 := hprev P.2 (fun a ha => (hs a ha).2.1)
  exact ⟨s,r,recordIndexTime ℓ s P.1,recordIndexTime ℓ s P.2,hsr,hr,hp1.1,hp2.1,
    h1.1,h1.2.1,hp1.2,hp2.2,h1.2.2,hbad⟩

theorem independent_firstHit_oscillation_transfer {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (e : Direction d) (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1)
    (J : Set (ℕ × ℕ)) (hJ : ∀ sr ∈ J, sr.1 ≤ sr.2) {z : ℝ} (hz : 0 ≤ z) :
    (annealedLaw ν (NoDrop ℓ 0))^2 * independentConditionedPairLaw ν ℓ
      {P | ∃ s r, (s,r) ∈ J ∧ z < |firstHitPairGap ℓ e r P-firstHitPairGap ℓ e s P|} ≤
    independentConditionedPairLaw ν ℓ {P | ∃ s r, (s,r) ∈ J ∧
      CommonTrueRecord ℓ P (recordIndexTime ℓ r P.1) (recordIndexTime ℓ r P.2) ∧
      z < |firstHitPairGap ℓ e r P-firstHitPairGap ℓ e s P|} := by
  have hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  calc
    _ ≤ (annealedLaw ν (NoDrop ℓ 0))^2 * independentConditionedPairLaw ν ℓ
        (⋃ q, PairOscillationTest ℓ e J z q) := by
      apply mul_le_mul_right
      apply measure_mono_ae
      filter_upwards [independent_firstHit_aligned ν ℓ htrans height hproj hstep] with P hP hh
      obtain ⟨s,r,hsr,hbad⟩ := hh
      exact Set.mem_iUnion.mpr ⟨_,firstHitPairGap_prefix_test ℓ e J hJ hz hP hsr hbad⟩
    _ ≤ independentConditionedPairLaw ν ℓ
        (⋃ q, PairOscillationTest ℓ e J z q ∩ {P | CommonTrueRecord ℓ P q.1 q.2}) :=
      independent_exact_cut_transfer ν ℓ hp _ (measurableSet_pairOscillationTest ℓ e J z)
        (pairOscillationTest_prefix ℓ e J z) (pairOscillationTest_aligned ℓ e J z)
    _ ≤ _ := by
      apply measure_mono
      intro P hP
      obtain ⟨q,hq,htrue⟩ := Set.mem_iUnion.mp hP
      obtain ⟨s,r,a,b,hsr,_,_,_,hr1,hr2,hs1,hs2,_,hbad⟩ := hq
      have he1 := recordIndexTime_eq ℓ r q.1 P.1 hr1
      have he2 := recordIndexTime_eq ℓ r q.2 P.2 hr2
      have hs1' := recordOrZeroPrefix_time ℓ hs1
      have hs2' := recordOrZeroPrefix_time ℓ hs2
      refine ⟨s,r,hsr,by simpa only [he1,he2,Set.mem_ofPred_eq] using htrue,?_⟩
      simpa only [firstHitPairGap,recordIndexPosition,he1,he2,hs1',hs2'] using hbad

noncomputable def commonBoundaryGap {d : ℕ} (ℓ : Vector d) (e : Direction d)
    (h : ℕ) (P : Path d × Path d) : ℝ :=
  realPartialSum (fun k => commonIncrementProcess ℓ e k P)
    (renewalCount (fun k => commonWidthProcess ℓ k P) h)

noncomputable def commonDecoration {d : ℕ} (ℓ : Vector d)
    (h : ℕ) (P : Path d × Path d) : ℝ :=
  wordRadius (commonWords ℓ P (renewalCount (fun k => commonWidthProcess ℓ k P) h)).1 +
  wordRadius (commonWords ℓ P (renewalCount (fun k => commonWidthProcess ℓ k P) h)).2

lemma commonBoundaryGap_eq_at_true {d : ℕ} (ℓ : Vector d) (e : Direction d)
    (P : Path d × Path d) (h0 : P.1 0 = 0) (h0' : P.2 0 = 0)
    (hP : ∀ n, ((renewPairSuffix ℓ)^[n] P) ∈ FirstPairWordEvent ℓ (commonWords ℓ P n))
    {r : ℕ} (hs : 0 < r → P.1 ∈ RecordIndexPrefix ℓ r (recordIndexTime ℓ r P.1))
    (ht : CommonTrueRecord ℓ P (recordIndexTime ℓ r P.1) (recordIndexTime ℓ r P.2)) :
    firstHitPairGap ℓ e r P = commonBoundaryGap ℓ e r P := by
  by_cases hr : r = 0
  · simp only [hr,firstHitPairGap,recordIndexPosition,recordIndexTime_zero,h0,h0',
      sub_self,commonBoundaryGap,renewalCount_zero,realPartialSum_zero]
  obtain ⟨k,hk⟩ := commonTrueRecord_eq_commonTimes ℓ P h0 h0' hP ht
  have hc : renewalSum (fun j => commonWidthProcess ℓ j P) k = r := by
    change (∑ i ∈ Finset.range k, wordRecordCount ℓ (commonWords ℓ P i).1) = r
    rw [← recordCount_commonTimes ℓ P h0 h0' hP k,hk]
    exact (hs (Nat.pos_of_ne_zero hr)).2.2.1
  have hpos (j : ℕ) : 0 < commonWidthProcess ℓ j P := commonWordWidth_positive ℓ _ _ (hP j)
  rw [commonBoundaryGap,← hc,renewalCount_at_sum _ hpos,← common_coordinate_sum ℓ e P h0 h0' hP k,hk]
  rw [hc]
  rfl

lemma independent_commonBoundary_at_true {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (e : Direction d) (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1) :
    ∀ᵐ P ∂independentConditionedPairLaw ν ℓ, ∀ r,
      CommonTrueRecord ℓ P (recordIndexTime ℓ r P.1) (recordIndexTime ℓ r P.2) →
      firstHitPairGap ℓ e r P = commonBoundaryGap ℓ e r P := by
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ
    (ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans))
  have hac := conditionedLaw_absolutelyContinuous ν ℓ
  have h0 := (Measure.quasiMeasurePreserving_fst.ae (hac.ae_le (annealed_initial ν))).and
    (Measure.quasiMeasurePreserving_snd.ae (hac.ae_le (annealed_initial ν)))
  filter_upwards [h0,independent_firstHit_aligned ν ℓ htrans height hproj hstep,
    independent_conditioned_all_firstPairWords ν ℓ htrans height hproj hstep] with P h0 hs hP r ht
  exact commonBoundaryGap_eq_at_true ℓ e P h0.1 h0.2 hP (fun hr => (hs r hr).1) ht

theorem independent_firstHit_boundary_transfer {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (e : Direction d) (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1)
    (J : Set (ℕ × ℕ)) (hJ : ∀ sr ∈ J, sr.1 ≤ sr.2) {z : ℝ} (hz : 0 ≤ z) :
    (annealedLaw ν (NoDrop ℓ 0))^2 * independentConditionedPairLaw ν ℓ
      {P | ∃ s r, (s,r) ∈ J ∧ z < |firstHitPairGap ℓ e r P-firstHitPairGap ℓ e s P|} ≤
    independentConditionedPairLaw ν ℓ {P | ∃ s r, (s,r) ∈ J ∧
      z < |commonBoundaryGap ℓ e r P-commonBoundaryGap ℓ e s P|+commonDecoration ℓ s P} := by
  apply (independent_firstHit_oscillation_transfer ν ℓ e htrans height hproj hstep J hJ hz).trans
  apply measure_mono_ae
  filter_upwards [independent_commonBoundary_at_true ν ℓ e htrans height hproj hstep,
    independent_firstHit_decoration_bound ν ℓ e htrans height hproj hstep] with P hP hdec hh
  obtain ⟨s,r,hJ,ht,hbad⟩ := hh
  refine ⟨s,r,hJ,hbad.trans_le ?_⟩
  rw [hP r ht]
  exact (abs_sub_le _ (commonBoundaryGap ℓ e s P) _).trans
    (add_le_add le_rfl (by simpa only [commonBoundaryGap,commonDecoration,abs_sub_comm] using hdec s))

theorem independent_firstHit_gap_transfer {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (e : Direction d) (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1)
    (J : Set (ℕ × ℕ)) (hJ : ∀ sr ∈ J, sr.1 ≤ sr.2) {z : ℝ} (hz : 0 ≤ z) :
    (annealedLaw ν (NoDrop ℓ 0))^2 * independentConditionedPairLaw ν ℓ
      {P | ∃ s r, (s,r) ∈ J ∧ z < |firstHitPairGap ℓ e r P-firstHitPairGap ℓ e s P|} ≤
    independentConditionedPairLaw ν ℓ {P | ∃ s r, (s,r) ∈ J ∧
      z < |commonBoundaryGap ℓ e r P-commonBoundaryGap ℓ e s P|+
        |firstHitPairGap ℓ e s P-commonBoundaryGap ℓ e s P|} := by
  apply (independent_firstHit_oscillation_transfer ν ℓ e htrans height hproj hstep J hJ hz).trans
  apply measure_mono_ae
  filter_upwards [independent_commonBoundary_at_true ν ℓ e htrans height hproj hstep] with P hP hh
  obtain ⟨s,r,hJ,ht,hbad⟩ := hh
  refine ⟨s,r,hJ,hbad.trans_le ?_⟩
  rw [hP r ht,abs_sub_comm (firstHitPairGap ℓ e s P)]
  exact abs_sub_le _ (commonBoundaryGap ℓ e s P) _

def HeightBlockRelation (H b : ℕ) : Set (ℕ × ℕ) :=
  {sr | sr.2 ≤ H ∧ sr.1 = (sr.2/b)*b}

def HeightOscillation {Ω : Type*} (F : ℕ → Ω → ℝ) (J : Set (ℕ × ℕ)) (z : ℝ) : Set Ω :=
  {ω | ∃ s h, (s,h) ∈ J ∧ z < |F h ω-F s ω|}

def BlockDecoration {Ω : Type*} (F B : ℕ → Ω → ℝ) (M b : ℕ) (z : ℝ) : Set Ω :=
  {ω | ∃ j ≤ M, z < |F (j*b) ω-B (j*b) ω|}

def HeightGapEvent {Ω : Type*} (F B : ℕ → Ω → ℝ) (H : ℕ) (z : ℝ) : Set Ω :=
  {ω | ∃ h ≤ H, z < |F h ω-B h ω|}

lemma heightBlockRelation_order (H b : ℕ) :
    ∀ sr ∈ HeightBlockRelation H b, sr.1 ≤ sr.2 := by
  rintro ⟨s,r⟩ ⟨_,hs⟩
  change s = r / b * b at hs
  simpa only [hs] using Nat.div_mul_le_self r b

lemma heightGap_subset {Ω : Type*} (F B : ℕ → Ω → ℝ) {H b M : ℕ}
    (hM : H/b ≤ M) {a : ℝ} :
    HeightGapEvent F B H (6*a) ⊆
      HeightOscillation F (HeightBlockRelation H b) (2*a) ∪
        HeightOscillation B (HeightBlockRelation H b) a ∪ BlockDecoration F B M b a := by
  rintro ω ⟨h,hh,hbig⟩
  by_contra hnot
  have hnot : ω ∉ HeightOscillation F (HeightBlockRelation H b) (2*a) ∧
      ω ∉ HeightOscillation B (HeightBlockRelation H b) a ∧ ω ∉ BlockDecoration F B M b a := by
    simpa only [Set.mem_union,not_or,and_assoc] using hnot
  let s := h/b*b
  have hsJ : (s,h) ∈ HeightBlockRelation H b := ⟨hh,rfl⟩
  have ha : |F h ω-F s ω| ≤ 2*a := le_of_not_gt (fun hb => hnot.1 ⟨s,h,hsJ,hb⟩)
  have hb : |B h ω-B s ω| ≤ a := le_of_not_gt (fun hb => hnot.2.1 ⟨s,h,hsJ,hb⟩)
  have hd : |F s ω-B s ω| ≤ a := le_of_not_gt (fun hb => hnot.2.2
    ⟨h/b,(Nat.div_le_div_right hh).trans hM,hb⟩)
  have he := (abs_sub_le (F h ω) (F s ω) (B h ω)).trans
    (add_le_add le_rfl (abs_sub_le (F s ω) (B s ω) (B h ω)))
  rw [abs_sub_comm (B s ω)] at he
  have hapos : 0 ≤ a := (abs_nonneg _).trans hb
  linarith

end DirectionalTransience
end
end

end OAI

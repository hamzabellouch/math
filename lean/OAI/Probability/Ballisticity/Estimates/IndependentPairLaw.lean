import Mathlib
import OAI.Probability.Ballisticity.Estimates.PairPrefix

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
namespace DirectionalTransience

lemma shared_pair_common_true_unbounded {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1)
    (x y : Lattice d) (c : ℝ≥0∞) (hc0 : 0 < c) (hct : c ≠ ∞)
    (hc : ∀ u v, c ≤ sharedNoDropMass ν ℓ u v) :
    ∀ᵐ P ∂sharedPairLaw ν x y, ∀ K : ℤ, P ∈ CommonTrueAbove ℓ K := by
  rw [ae_all_iff]
  intro K
  apply ae_of_pair_prefix_probability_lower _ _ (measurableSet_commonTrueAbove ℓ K) c hc0 hct
  exact shared_pair_common_true_after_prefix ν ℓ htrans height hproj hstep x y c hc K

lemma pair_record_event_noDrop_lower {d : ℕ} (μ : Measure (Path d × Path d))
    (ℓ : Vector d) (c : ℝ≥0∞)
    (hfresh : ∀ (f g : Path d) (n m : ℕ), 0 < n → 0 < m →
      StrictRecord ℓ f n → StrictRecord ℓ g m →
      dot (realPosition (f n)) ℓ = dot (realPosition (g m)) ℓ →
      c * μ (pathCylinder f n ×ˢ pathCylinder g m) ≤ μ
        (((fun X : Path d => fun j => X (n+j)) ⁻¹' NoDrop ℓ (f n) ∩ pathCylinder f n) ×ˢ
         ((fun X : Path d => fun j => X (m+j)) ⁻¹' NoDrop ℓ (g m) ∩ pathCylinder g m)))
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) (A : Set (Path d × Path d))
    (hA : PairPrefixDetermined n m A)
    (hr : ∀ P ∈ A, StrictRecord ℓ P.1 n ∧ StrictRecord ℓ P.2 m ∧
      dot (realPosition (P.1 n)) ℓ = dot (realPosition (P.2 m)) ℓ) :
    c * μ A ≤
      μ (A ∩ (FutureNoDrop ℓ n ×ˢ FutureNoDrop ℓ m)) := by
  classical
  rw [measure_partition_pairprefix (μ) A n m,
    measure_partition_pairprefix (μ) (A ∩ _) n m,
    ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro F
  let P : Path d × Path d := (extendPrefix n F.1,extendPrefix m F.2)
  let C := pathCylinder P.1 n ×ˢ pathCylinder P.2 m
  by_cases hP : P ∈ A
  · have hAc : A ∩ C = C := Set.inter_eq_right.mpr fun Q hQ => (hA Q P hQ.1 hQ.2).mpr hP
    have he : (A ∩ (FutureNoDrop ℓ n ×ˢ FutureNoDrop ℓ m)) ∩ C =
        (((fun X : Path d => fun j => X (n+j)) ⁻¹' NoDrop ℓ (P.1 n) ∩ pathCylinder P.1 n) ×ˢ
         ((fun X : Path d => fun j => X (m+j)) ⁻¹' NoDrop ℓ (P.2 m) ∩ pathCylinder P.2 m)) := by
      ext Q
      constructor
      · rintro ⟨⟨_,h1,h2⟩,hc1,hc2⟩
        refine ⟨⟨?_,hc1⟩,⟨?_,hc2⟩⟩
        · intro j; rw [← hc1 n le_rfl]; exact h1 j
        · intro j; rw [← hc2 m le_rfl]; exact h2 j
      · rintro ⟨⟨h1,hc1⟩,⟨h2,hc2⟩⟩
        refine ⟨⟨(hA Q P hc1 hc2).mpr hP,?_,?_⟩,hc1,hc2⟩
        · intro j; rw [hc1 n le_rfl]; exact h1 j
        · intro j; rw [hc2 m le_rfl]; exact h2 j
    change c * μ (A ∩ C) ≤ μ ((A ∩ _) ∩ C)
    rw [hAc,he]
    exact hfresh P.1 P.2 n m hn hm (hr P hP).1 (hr P hP).2.1 (hr P hP).2.2
  · have hAc : A ∩ C = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro Q ⟨hQ,hqc1,hqc2⟩
      exact hP ((hA Q P hqc1 hqc2).mp hQ)
    change c * μ (A ∩ C) ≤ _
    rw [hAc,measure_empty,mul_zero]
    exact zero_le

lemma pair_common_true_after_prefix {d : ℕ} (μ : Measure (Path d × Path d))
    (ℓ : Vector d) (height : Lattice d → ℤ)
    (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ)) (x y : Lattice d)
    (hhits : ∀ H : ℤ, height x < H → height y < H → ∀ᵐ P ∂μ,
      (∃ n, P.1 ∈ FirstLayerHit height H n) ∧ (∃ m, P.2 ∈ FirstLayerHit height H m))
    (c : ℝ≥0∞)
    (hfresh : ∀ (n m : ℕ), 0 < n → 0 < m → ∀ (A : Set (Path d × Path d)),
      PairPrefixDetermined n m A →
      (∀ P ∈ A, StrictRecord ℓ P.1 n ∧ StrictRecord ℓ P.2 m ∧
        dot (realPosition (P.1 n)) ℓ = dot (realPosition (P.2 m)) ℓ) →
      c * μ A ≤ μ (A ∩ (FutureNoDrop ℓ n ×ˢ FutureNoDrop ℓ m)))
    (K : ℤ) (N : ℕ) (f g : Path d) :
    c * μ (pathCylinder f N ×ˢ pathCylinder g N) ≤
      μ (CommonTrueAbove ℓ K ∩ (pathCylinder f N ×ˢ pathCylinder g N)) := by
  classical
  let C := pathCylinder f N ×ˢ pathCylinder g N
  obtain ⟨H,hKH,hx,hy,hH⟩ := finite_pair_prefix_height_bound height f g N K x y
  let A (q : ℕ × ℕ) := C ∩ (FirstLayerHit height H q.1 ×ˢ FirstLayerHit height H q.2)
  let B (q : ℕ × ℕ) := A q ∩ (FutureNoDrop ℓ q.1 ×ˢ FutureNoDrop ℓ q.2)
  have hdisA : Pairwise (fun q r => Disjoint (A q) (A r)) := fun q r hqr =>
    (firstLayerHit_pair_disjoint height H hqr).mono Set.inter_subset_right Set.inter_subset_right
  have hdisB : Pairwise (fun q r => Disjoint (B q) (B r)) := fun q r hqr =>
    (hdisA hqr).mono Set.inter_subset_left Set.inter_subset_left
  have hmA (q : ℕ × ℕ) : MeasurableSet (A q) :=
    ((measurableSet_pathCylinder f N).prod (measurableSet_pathCylinder g N)).inter
      ((measurableSet_firstLayerHit height H q.1).prod (measurableSet_firstLayerHit height H q.2))
  have hmB (q : ℕ × ℕ) : MeasurableSet (B q) := (hmA q).inter
    ((measurableSet_futureNoDrop ℓ q.1).prod (measurableSet_futureNoDrop ℓ q.2))
  have hcover : μ C = ∑' q, μ (A q) := by
    rw [← measure_iUnion hdisA hmA]
    apply measure_congr
    filter_upwards [hhits H hx hy] with P hP
    apply propext
    change P ∈ C ↔ P ∈ ⋃ q, A q
    simp only [Set.mem_iUnion]
    constructor
    · intro hC
      obtain ⟨n,hn⟩ := hP.1
      obtain ⟨m,hm⟩ := hP.2
      exact ⟨(n,m),hC,hn,hm⟩
    · rintro ⟨q,hq⟩
      exact hq.1
  have hindices (q : ℕ × ℕ) (P : Path d × Path d) (hP : P ∈ A q) :
      N < q.1 ∧ N < q.2 := by
    constructor
    · apply firstLayerHit_after_prefix height H P.1 N _ hP.2.1
      intro j hj
      rw [hP.1.1 j hj]
      exact (hH j hj).1
    · apply firstLayerHit_after_prefix height H P.2 N _ hP.2.2
      intro j hj
      rw [hP.1.2 j hj]
      exact (hH j hj).2
  have hlower (q : ℕ × ℕ) : c * μ (A q) ≤ μ (B q) := by
    by_cases hne : (A q).Nonempty
    · obtain ⟨P,hP⟩ := hne
      have hi := hindices q P hP
      apply hfresh q.1 q.2
        (lt_of_le_of_lt (Nat.zero_le _) hi.1) (lt_of_le_of_lt (Nat.zero_le _) hi.2)
      · exact pairPrefixDetermined_inter
          (pairPrefixDetermined_product (prefixDetermined_cylinder_of_le f hi.1.le)
            (prefixDetermined_cylinder_of_le g hi.2.le))
          (pairPrefixDetermined_product (firstLayerHit_prefix height H q.1) (firstLayerHit_prefix height H q.2))
      · intro Q hQ
        refine ⟨firstLayerHit_record ℓ height hproj H q.1 Q.1 hQ.2.1,
          firstLayerHit_record ℓ height hproj H q.2 Q.2 hQ.2.2,?_⟩
        rw [hproj,hproj,hQ.2.1.1,hQ.2.2.1]
    · have hz : A q = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
      rw [hz,measure_empty,mul_zero]
      exact zero_le
  have hsub : (⋃ q, B q) ⊆ CommonTrueAbove ℓ K ∩ C := by
    intro P hP
    obtain ⟨q,hq⟩ := Set.mem_iUnion.mp hP
    refine ⟨⟨q.1,q.2,?_,?_⟩,hq.1.1⟩
    · rw [hproj,hq.1.2.1.1]
      exact_mod_cast hKH
    · refine ⟨?_,?_,?_⟩
      · exact ⟨firstLayerHit_record ℓ height hproj H q.1 P.1 hq.1.2.1,hq.2.1⟩
      · exact ⟨firstLayerHit_record ℓ height hproj H q.2 P.2 hq.1.2.2,hq.2.2⟩
      · rw [hproj,hproj,hq.1.2.1.1,hq.1.2.2.1]
  calc
    c * μ C = ∑' q, c * μ (A q) := by rw [hcover,ENNReal.tsum_mul_left]
    _ ≤ ∑' q, μ (B q) := ENNReal.tsum_le_tsum hlower
    _ = μ (⋃ q, B q) := (measure_iUnion hdisB hmB).symm
    _ ≤ μ (CommonTrueAbove ℓ K ∩ C) := measure_mono hsub

noncomputable def independentPairLaw {d : ℕ} (ν : Measure (Row d)) : Measure (Path d × Path d) :=
  (annealedLaw ν).prod (annealedLaw ν)

instance independentPairLaw_probability {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (independentPairLaw ν) := inferInstanceAs
      (IsProbabilityMeasure ((annealedLaw ν).prod (annealedLaw ν)))

lemma independent_pair_record_cylinder_noDrop {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (f g : Path d) (n m : ℕ)
    (hn : 0 < n) (hm : 0 < m) (hrf : StrictRecord ℓ f n) (hrg : StrictRecord ℓ g m) :
    independentPairLaw ν
      (((fun X : Path d => fun j => X (n+j)) ⁻¹' NoDrop ℓ (f n) ∩ pathCylinder f n) ×ˢ
       ((fun X : Path d => fun j => X (m+j)) ⁻¹' NoDrop ℓ (g m) ∩ pathCylinder g m)) =
      (annealedLaw ν (NoDrop ℓ 0))^2 *
        independentPairLaw ν (pathCylinder f n ×ˢ pathCylinder g m) := by
  rw [independentPairLaw,Measure.prod_prod,Measure.prod_prod,
    annealed_record_cylinder_noDrop ν ℓ f n hn hrf,
    annealed_record_cylinder_noDrop ν ℓ g m hm hrg,pow_two]
  ac_rfl

lemma independent_pair_layer_hits {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1)
    (H : ℤ) (hH : height 0 < H) :
    ∀ᵐ P ∂independentPairLaw ν,
      (∃ n, P.1 ∈ FirstLayerHit height H n) ∧ (∃ m, P.2 ∈ FirstLayerHit height H m) := by
  have ha : ∀ᵐ X ∂annealedLaw ν, ∃ n, X ∈ FirstLayerHit height H n := by
    filter_upwards [htrans,annealed_initial ν,annealed_nearest_neighbor ν] with X ht h0 hn
    apply firstLayerHit_exists height hstep X hn
    · simpa only [hproj] using ht
    · simpa only [h0] using hH
  exact (Measure.quasiMeasurePreserving_fst.ae ha).and
    (Measure.quasiMeasurePreserving_snd.ae ha)

lemma independent_pair_common_true_unbounded {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1) :
    ∀ᵐ P ∂independentPairLaw ν, ∀ K : ℤ, P ∈ CommonTrueAbove ℓ K := by
  rw [ae_all_iff]
  intro K
  let p := annealedLaw ν (NoDrop ℓ 0)
  have hp : 0 < p := noDrop_positive_of_directionallyTransient ν ℓ htrans
  have hpt : p^2 ≠ ∞ := ENNReal.pow_ne_top (measure_ne_top _ _)
  apply ae_of_pair_prefix_probability_lower _ _ (measurableSet_commonTrueAbove ℓ K)
    (p^2) (ENNReal.pow_pos hp _) hpt
  apply pair_common_true_after_prefix (independentPairLaw ν) ℓ height hproj 0 0
    (fun H hx _ => independent_pair_layer_hits ν ℓ htrans height hproj hstep H hx) (p^2)
  intro n m hn hm A hA hr
  apply pair_record_event_noDrop_lower (independentPairLaw ν) ℓ (p^2) _ n m hn hm A hA hr
  intro f g n m hn hm hrf hrg _
  exact le_of_eq (independent_pair_record_cylinder_noDrop ν ℓ f g n m hn hm hrf hrg).symm

lemma commonTrueRecord_time_order {d : ℕ} (ℓ : Vector d) (P : Path d × Path d)
    {n m j k : ℕ} (hn : CommonTrueRecord ℓ P n m) (hj : CommonTrueRecord ℓ P j k) :
    n < j ↔ m < k := by
  constructor
  · intro hnj
    have hheight := hj.1.1 n hnj
    rw [hn.2.2,hj.2.2] at hheight
    by_contra hmk
    rcases lt_or_eq_of_le (not_lt.mp hmk) with hkm | rfl
    · exact (not_lt_of_ge (hn.2.1.1 k hkm).le) hheight
    · exact (lt_irrefl _ hheight)
  · intro hmk
    have hheight := hj.2.1.1 m hmk
    rw [← hn.2.2,← hj.2.2] at hheight
    by_contra hnj
    rcases lt_or_eq_of_le (not_lt.mp hnj) with hjn | rfl
    · exact (not_lt_of_ge (hn.1.1 j hjn).le) hheight
    · exact (lt_irrefl _ hheight)

lemma firstCommonTrueRecord_unique {d : ℕ} (ℓ : Vector d) (P : Path d × Path d)
    {n m j k : ℕ} (hn : FirstCommonTrueRecord ℓ P n m)
    (hj : FirstCommonTrueRecord ℓ P j k) : n = j ∧ m = k := by
  have hnj : n = j := by
    rcases lt_trichotomy n j with h | h | h
    · exact False.elim (hj.2.2.2 n m hn.1 h hn.2.1
        ((commonTrueRecord_time_order ℓ P hn.2.2.1 hj.2.2.1).mp h) hn.2.2.1)
    · exact h
    · exact False.elim (hn.2.2.2 j k hj.1 h hj.2.1
        ((commonTrueRecord_time_order ℓ P hj.2.2.1 hn.2.2.1).mp h) hj.2.2.1)
  refine ⟨hnj,?_⟩
  apply Nat.le_antisymm
  · by_contra h
    have := (commonTrueRecord_time_order ℓ P hj.2.2.1 hn.2.2.1).mpr (by omega : k < m)
    omega
  · by_contra h
    have := (commonTrueRecord_time_order ℓ P hn.2.2.1 hj.2.2.1).mpr (by omega : m < k)
    omega

lemma firstCommonTrueRecord_exists {d : ℕ} (ℓ : Vector d) (P : Path d × Path d)
    (h : ∃ n m, 0 < n ∧ 0 < m ∧ CommonTrueRecord ℓ P n m) :
    ∃ n m, FirstCommonTrueRecord ℓ P n m := by
  classical
  obtain ⟨m,hn,hm,hr⟩ := Nat.find_spec h
  exact ⟨Nat.find h,m,hn,hm,hr,fun j k hj hjn hk _ hc =>
    Nat.find_min h hjn ⟨k,hj,hk,hc⟩⟩

def FirstPairWordEvent {d : ℕ} (ℓ : Vector d)
    (wv : List (Direction d) × List (Direction d)) : Set (Path d × Path d) :=
  (NoDrop ℓ 0 ×ˢ NoDrop ℓ 0) ∩ commonWordEvent ℓ 0 0 wv.1 wv.2

lemma measurableSet_firstPairWordEvent {d : ℕ} (ℓ : Vector d)
    (wv : List (Direction d) × List (Direction d)) : MeasurableSet (FirstPairWordEvent ℓ wv) :=
  ((measurableSet_noDrop ℓ 0).prod (measurableSet_noDrop ℓ 0)).inter
    (measurableSet_commonWordEvent ℓ 0 0 wv.1 wv.2)

lemma firstPairWordEvent_nil {d : ℕ} (ℓ : Vector d) :
    FirstPairWordEvent ℓ (([] : List (Direction d)),[]) = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  exact fun P hP => Nat.lt_irrefl 0 hP.2.2.1

lemma firstPairWordEvent_disjoint {d : ℕ} (ℓ : Vector d) :
    Pairwise (fun u v : List (Direction d) × List (Direction d) =>
      Disjoint (FirstPairWordEvent ℓ u) (FirstPairWordEvent ℓ v)) := by
  intro u v huv
  apply Set.disjoint_left.mpr
  intro P hPu hPv
  have hlen := firstCommonTrueRecord_unique ℓ P hPu.2.2 hPv.2.2
  exact huv (Prod.ext (word_eq_of_cylinders 0 u.1 v.1 P.1 hPu.2.1.1 hPv.2.1.1 hlen.1)
    (word_eq_of_cylinders 0 u.2 v.2 P.2 hPu.2.1.2 hPv.2.1.2 hlen.2))

lemma firstPairWordEvent_admissible {d : ℕ} (ℓ : Vector d)
    (wv : List (Direction d) × List (Direction d)) (P : Path d × Path d)
    (hP : P ∈ FirstPairWordEvent ℓ wv) : AdmissibleCommonWords ℓ 0 0 wv.1 wv.2 :=
  ((firstCommonWords_characterization ℓ 0 0 wv.1 wv.2 P hP.2.1.1 hP.2.1.2).mp
    ⟨hP.1.1,hP.1.2,hP.2.2⟩).1

noncomputable def independentConditionedPairLaw {d : ℕ} (ν : Measure (Row d)) (ℓ : Vector d) :
    Measure (Path d × Path d) := (conditionedLaw ν ℓ).prod (conditionedLaw ν ℓ)

lemma independentConditionedPairLaw_probability {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (hp : annealedLaw ν (NoDrop ℓ 0) ≠ 0) :
    IsProbabilityMeasure (independentConditionedPairLaw ν ℓ) := by
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ hp
  exact inferInstanceAs (IsProbabilityMeasure ((conditionedLaw ν ℓ).prod (conditionedLaw ν ℓ)))

lemma independent_conditioned_firstPairWord_exists {d : ℕ} (ν : Measure (Row d))
    [IsProbabilityMeasure ν] (ℓ : Vector d) (htrans : DirectionallyTransient ν ℓ)
    (height : Lattice d → ℤ) (hproj : ∀ x, dot (realPosition x) ℓ = (height x : ℝ))
    (hstep : ∀ x e, height (x+step e) ≤ height x+1) :
    ∀ᵐ P ∂independentConditionedPairLaw ν ℓ, ∃ wv, P ∈ FirstPairWordEvent ℓ wv := by
  have hp := ne_of_gt (noDrop_positive_of_directionallyTransient ν ℓ htrans)
  let : IsProbabilityMeasure (conditionedLaw ν ℓ) := conditionedLaw_probability ν ℓ hp
  have hac : independentConditionedPairLaw ν ℓ ≪ independentPairLaw ν :=
    (conditionedLaw_absolutelyContinuous ν ℓ).prod (conditionedLaw_absolutelyContinuous ν ℓ)
  have hD := (Measure.quasiMeasurePreserving_fst.ae (conditionedLaw_noDrop ν ℓ)).and
    (Measure.quasiMeasurePreserving_snd.ae (conditionedLaw_noDrop ν ℓ))
  have h0 := (Measure.quasiMeasurePreserving_fst.ae (annealed_initial ν)).and
    (Measure.quasiMeasurePreserving_snd.ae (annealed_initial ν))
  have hNN := (Measure.quasiMeasurePreserving_fst.ae (annealed_nearest_neighbor ν)).and
    (Measure.quasiMeasurePreserving_snd.ae (annealed_nearest_neighbor ν))
  filter_upwards [hac.ae_le (independent_pair_common_true_unbounded ν ℓ htrans height hproj hstep),
    hD,hac.ae_le h0,hac.ae_le hNN] with P hcommon hD h0 hNN
  obtain ⟨n,m,hh,hr⟩ := hcommon (height 0)
  have hn : 0 < n := by
    by_contra hn
    have hz : n = 0 := by omega
    rw [hz,h0.1,hproj] at hh
    exact (lt_irrefl _ hh)
  have hm : 0 < m := by
    by_contra hm
    have hz : m = 0 := by omega
    rw [hr.2.2,hz,h0.2,hproj] at hh
    exact (lt_irrefl _ hh)
  obtain ⟨j,k,hfirst⟩ := firstCommonTrueRecord_exists ℓ P ⟨n,m,hn,hm,hr⟩
  obtain ⟨w,hw,hcw⟩ := exists_word_prefix P.1 hNN.1 j
  obtain ⟨v,hv,hcv⟩ := exists_word_prefix P.2 hNN.2 k
  refine ⟨(w,v),hD,⟨?_,?_⟩,?_⟩
  · simpa only [h0.1] using hcw
  · simpa only [h0.2] using hcv
  · change FirstCommonTrueRecord ℓ P w.length v.length
    simpa only [hw,hv] using hfirst

open scoped Classical in
noncomputable def firstPairWord {d : ℕ} (ℓ : Vector d) (P : Path d × Path d) :
    List (Direction d) × List (Direction d) :=
  if h : ∃ wv, P ∈ FirstPairWordEvent ℓ wv then h.choose else ([],[])

lemma firstPairWord_eq_iff {d : ℕ} (ℓ : Vector d) (P : Path d × Path d)
    (wv : List (Direction d) × List (Direction d)) (hwv : wv ≠ ([],[])) :
    firstPairWord ℓ P = wv ↔ P ∈ FirstPairWordEvent ℓ wv := by
  classical
  unfold firstPairWord
  split_ifs with h
  · constructor
    · intro he
      exact he ▸ h.choose_spec
    · intro hP
      by_contra hne
      exact (Set.disjoint_left.mp (firstPairWordEvent_disjoint ℓ hne)) h.choose_spec hP
  · simp only [eq_comm (a := (([],[]) : List (Direction d) × List (Direction d))),
      hwv,false_iff]
    exact fun hP => h ⟨wv,hP⟩

lemma firstPairWord_nil_iff {d : ℕ} (ℓ : Vector d) (P : Path d × Path d) :
    firstPairWord ℓ P = ([],[]) ↔ ¬ ∃ wv, P ∈ FirstPairWordEvent ℓ wv := by
  classical
  unfold firstPairWord
  split_ifs with h
  · simp only [h,not_true_eq_false,iff_false]
    intro he
    have := h.choose_spec
    rw [he,firstPairWordEvent_nil] at this
    exact this
  · simp [h]

lemma measurable_firstPairWord {d : ℕ} (ℓ : Vector d) : Measurable (firstPairWord ℓ) := by
  classical
  apply measurable_to_countable'
  intro wv
  by_cases h : wv = ([],[])
  · subst wv
    have he : firstPairWord ℓ ⁻¹' {([],[])} = (⋃ wv,FirstPairWordEvent ℓ wv)ᶜ := by
      ext P
      simp only [Set.mem_preimage,Set.mem_singleton_iff,firstPairWord_nil_iff,
        Set.mem_compl_iff,Set.mem_iUnion]
    rw [he]
    exact (MeasurableSet.iUnion (measurableSet_firstPairWordEvent ℓ)).compl
  · have he : firstPairWord ℓ ⁻¹' {wv} = FirstPairWordEvent ℓ wv := by
      ext P
      exact firstPairWord_eq_iff ℓ P wv h
    rw [he]
    exact measurableSet_firstPairWordEvent ℓ wv

noncomputable def renewPairSuffix {d : ℕ} (ℓ : Vector d) (P : Path d × Path d) :
    Path d × Path d :=
  ((fun j => P.1 ((firstPairWord ℓ P).1.length+j) - P.1 (firstPairWord ℓ P).1.length),
   (fun j => P.2 ((firstPairWord ℓ P).2.length+j) - P.2 (firstPairWord ℓ P).2.length))

lemma measurable_renewPairSuffix {d : ℕ} (ℓ : Vector d) : Measurable (renewPairSuffix ℓ) := by
  have hf : Measurable (fun P : Path d × Path d => (firstPairWord ℓ P).1.length) :=
    (measurable_of_countable List.length).comp (measurable_firstPairWord ℓ).fst
  have hg : Measurable (fun P : Path d × Path d => (firstPairWord ℓ P).2.length) :=
    (measurable_of_countable List.length).comp (measurable_firstPairWord ℓ).snd
  have heval : Measurable (fun p : Path d × ℕ => p.1 p.2) :=
    measurable_from_prod_countable_left fun n => measurable_pi_apply n
  apply Measurable.prodMk
  · apply Measurable.of_eval
    intro j
    exact (heval.comp (measurable_fst.prodMk (hf.add_const j))).sub
      (heval.comp (measurable_fst.prodMk hf))
  · apply Measurable.of_eval
    intro j
    exact (heval.comp (measurable_snd.prodMk (hg.add_const j))).sub
      (heval.comp (measurable_snd.prodMk hg))

lemma conditioned_record_word_factor {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (w : List (Direction d)) (hr : StrictRecord ℓ (wordPath 0 w) w.length)
    (hprefix : ∀ j ≤ w.length, dot (realPosition (0 : Lattice d)) ℓ ≤
      dot (realPosition (wordPath 0 w j)) ℓ)
    (A : Set (Path d)) (hA : MeasurableSet A) (hAD : A ⊆ NoDrop ℓ 0) :
    conditionedLaw ν ℓ ((fun X : Path d => fun j => X (w.length+j) -
      wordPath 0 w w.length) ⁻¹' A ∩ wordCylinder 0 w) =
      annealedLaw ν (wordCylinder 0 w) * conditionedLaw ν ℓ A := by
  have hE : MeasurableSet ((fun X : Path d => fun j => X (w.length+j) -
      wordPath 0 w w.length) ⁻¹' A ∩ wordCylinder 0 w) :=
    (hA.preimage (by fun_prop)).inter (measurableSet_wordCylinder _ _)
  have hED : ((fun X : Path d => fun j => X (w.length+j) -
      wordPath 0 w w.length) ⁻¹' A ∩ wordCylinder 0 w) ⊆ NoDrop ℓ 0 := by
    rintro X ⟨hXA,hX⟩
    have hD : X ∈ FutureNoDrop ℓ w.length := by
      apply (suffix_noDrop_iff ℓ X w.length).mp
      simpa only [hX w.length le_rfl] using hAD hXA
    apply (noDrop_iff_prefix_and_future ℓ 0 X w.length hD).mpr
    intro j hj
    rw [hX j hj]
    exact hprefix j hj
  have hdep : ∀ y ∈ wordDepartures 0 w, dot (realPosition y) ℓ <
      dot (realPosition (wordPath 0 w w.length)) ℓ := by
    intro y hy
    obtain ⟨j,hj,rfl⟩ := (wordDepartures_mem_iff 0 y w).mp hy
    exact hr j hj
  rw [conditionedLaw_apply_of_subset ν ℓ _ hE hED,
    annealed_record_suffix ν ℓ w hdep A hA hAD,
    conditionedLaw_apply_of_subset ν ℓ A hA hAD]
  ac_rfl

end DirectionalTransience
end
end

end OAI

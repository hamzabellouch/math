import Mathlib
import OAI.Probability.Ballisticity.Estimates.CommonOffset
import OAI.Probability.Ballisticity.Estimates.RecordPairFuture

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

namespace DirectionalTransience

def truePairCylinder {d : ℕ} (ℓ : Vector d) (f g : Path d) (n m : ℕ) :
    Set (Path d × Path d) :=
  (pathCylinder f n ×ˢ pathCylinder g m) ∩ (FutureNoDrop ℓ n ×ˢ FutureNoDrop ℓ m)

lemma measurableSet_truePairCylinder {d : ℕ} (ℓ : Vector d) (f g : Path d) (n m : ℕ) :
    MeasurableSet (truePairCylinder ℓ f g n m) :=
  ((measurableSet_pathCylinder f n).prod (measurableSet_pathCylinder g m)).inter
    ((measurableSet_futureNoDrop ℓ n).prod (measurableSet_futureNoDrop ℓ m))

lemma truePairCylinder_future {d : ℕ} (ℓ : Vector d) (f g : Path d) (n m : ℕ)
    (B : Set (Path d × Path d)) :
    commonPairSuffix n m ⁻¹' B ∩ truePairCylinder ℓ f g n m =
      commonPairSuffix n m ⁻¹' (B ∩ (NoDrop ℓ (f n) ×ˢ NoDrop ℓ (g m))) ∩
        (pathCylinder f n ×ˢ pathCylinder g m) := by
  ext P
  constructor
  · rintro ⟨hB,⟨hf,hg⟩,hD1,hD2⟩
    refine ⟨⟨hB,?_,?_⟩,hf,hg⟩
    · intro j
      change dot (realPosition (f n)) ℓ ≤ dot (realPosition (P.1 (n+j))) ℓ
      rw [← hf n le_rfl]
      exact hD1 j
    · intro j
      change dot (realPosition (g m)) ℓ ≤ dot (realPosition (P.2 (m+j))) ℓ
      rw [← hg m le_rfl]
      exact hD2 j
  · rintro ⟨⟨hB,hD1,hD2⟩,hf,hg⟩
    refine ⟨hB,⟨hf,hg⟩,?_,?_⟩
    · intro j
      rw [hf n le_rfl]
      exact hD1 j
    · intro j
      rw [hg m le_rfl]
      exact hD2 j

lemma truePairCylinder_noDrop {d : ℕ} (ℓ : Vector d) (f g : Path d) (n m : ℕ)
    (x y : Lattice d)
    (hf : ∀ j ≤ n, dot (realPosition x) ℓ ≤ dot (realPosition (f j)) ℓ)
    (hg : ∀ j ≤ m, dot (realPosition y) ℓ ≤ dot (realPosition (g j)) ℓ) :
    truePairCylinder ℓ f g n m ⊆ NoDrop ℓ x ×ˢ NoDrop ℓ y := by
  rintro P ⟨⟨hP,hQ⟩,hD,hE⟩
  constructor
  · apply (noDrop_iff_prefix_and_future ℓ x P.1 n hD).mpr
    intro j hj
    rw [hP j hj]
    exact hf j hj
  · apply (noDrop_iff_prefix_and_future ℓ y P.2 m hE).mpr
    intro j hj
    rw [hQ j hj]
    exact hg j hj

lemma shared_truePairCylinder_map {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (ℓ : Vector d) (x y : Lattice d) (f g : Path d) (n m : ℕ)
    (hn : 0 < n) (hm : 0 < m) (hrf : StrictRecord ℓ f n) (hrg : StrictRecord ℓ g m)
    (he : dot (realPosition (f n)) ℓ = dot (realPosition (g m)) ℓ)
    (hf : ∀ j ≤ n, dot (realPosition x) ℓ ≤ dot (realPosition (f j)) ℓ)
    (hg : ∀ j ≤ m, dot (realPosition y) ℓ ≤ dot (realPosition (g j)) ℓ)
    (hp : sharedNoDropMass ν ℓ (f n) (g m) ≠ 0) :
    ((sharedConditionedPairLaw ν ℓ x y).restrict (truePairCylinder ℓ f g n m)).map
      (commonPairSuffix n m) =
        sharedConditionedPairLaw ν ℓ x y (truePairCylinder ℓ f g n m) •
          sharedConditionedPairLaw ν ℓ (f n) (g m) := by
  let C := truePairCylinder ℓ f g n m
  let D := NoDrop ℓ (f n) ×ˢ NoDrop ℓ (g m)
  let a := (sharedNoDropMass ν ℓ x y)⁻¹ *
    sharedPairLaw ν x y (pathCylinder f n ×ˢ pathCylinder g m)
  have hC : MeasurableSet C := measurableSet_truePairCylinder ℓ f g n m
  have hCD : C ⊆ NoDrop ℓ x ×ˢ NoDrop ℓ y := truePairCylinder_noDrop ℓ f g n m x y hf hg
  have hD : MeasurableSet D := (measurableSet_noDrop ℓ (f n)).prod (measurableSet_noDrop ℓ (g m))
  have hfactor (B : Set (Path d × Path d)) (hB : MeasurableSet B) :
      sharedConditionedPairLaw ν ℓ x y (commonPairSuffix n m ⁻¹' B ∩ C) =
        a * sharedPairLaw ν (f n) (g m) (B ∩ D) := by
    rw [sharedConditionedPairLaw,Measure.smul_apply,
      Measure.restrict_apply ((hB.preimage (measurable_commonPairSuffix n m)).inter hC),
      Set.inter_eq_left.mpr (Set.Subset.trans Set.inter_subset_right hCD),
      truePairCylinder_future,
      shared_pair_record_cylinder_future ν ℓ x y f g n m hn hm hrf hrg he _
        (hB.inter hD) Set.inter_subset_right]
    simp only [smul_eq_mul,a,mul_assoc]
  have hmass : sharedConditionedPairLaw ν ℓ x y C = a * sharedNoDropMass ν ℓ (f n) (g m) := by
    simpa only [Set.preimage_univ,Set.univ_inter,sharedNoDropMass_eq,D] using
      hfactor Set.univ MeasurableSet.univ
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply (measurable_commonPairSuffix n m) hB,
    Measure.restrict_apply (hB.preimage (measurable_commonPairSuffix n m)),hfactor B hB,
    Measure.smul_apply,hmass,sharedConditionedPairLaw,Measure.smul_apply,Measure.restrict_apply hB]
  have hfin : sharedNoDropMass ν ℓ (f n) (g m) ≠ ∞ :=
    ne_of_lt ((sharedNoDropMass_le_one ν ℓ (f n) (g m)).trans_lt (by simp))
  simp only [smul_eq_mul,mul_assoc]
  rw [← mul_assoc (sharedNoDropMass ν ℓ (f n) (g m)),ENNReal.mul_inv_cancel hp hfin,one_mul]

def BoundaryAt {d : ℕ} (ℓ : Vector d) (H : ℝ) (P : Path d × Path d)
    (n m : ℕ) : Prop :=
  0 < n ∧ 0 < m ∧ CommonTrueRecord ℓ P n m ∧
    H ≤ dot (realPosition (P.1 n)) ℓ ∧
    ∀ j k, 0 < j → j < n → 0 < k → k < m →
      H ≤ dot (realPosition (P.1 j)) ℓ → ¬ CommonTrueRecord ℓ P j k

def AdmissibleBoundaryPrefix {d : ℕ} (ℓ : Vector d) (H : ℝ) (x y : Lattice d)
    (f g : Path d) (n m : ℕ) : Prop :=
  0 < n ∧ 0 < m ∧
    dot (realPosition (f n)) ℓ = dot (realPosition (g m)) ℓ ∧
    StrictRecord ℓ f n ∧ StrictRecord ℓ g m ∧
    (∀ j ≤ n, dot (realPosition x) ℓ ≤ dot (realPosition (f j)) ℓ) ∧
    (∀ k ≤ m, dot (realPosition y) ℓ ≤ dot (realPosition (g k)) ℓ) ∧
    H ≤ dot (realPosition (f n)) ℓ ∧
    ∀ j k, 0 < j → j < n → 0 < k → k < m →
      H ≤ dot (realPosition (f j)) ℓ → StrictRecord ℓ f j → StrictRecord ℓ g k →
      dot (realPosition (f j)) ℓ = dot (realPosition (g k)) ℓ →
      (∃ a, j < a ∧ a < n ∧ dot (realPosition (f a)) ℓ < dot (realPosition (f j)) ℓ) ∨
      (∃ b, k < b ∧ b < m ∧ dot (realPosition (g b)) ℓ < dot (realPosition (g k)) ℓ)

lemma boundaryPrefix_characterization {d : ℕ} (ℓ : Vector d) (H : ℝ)
    (x y : Lattice d) (f g : Path d) (n m : ℕ) (P : Path d × Path d)
    (hf : P.1 ∈ pathCylinder f n) (hg : P.2 ∈ pathCylinder g m) :
    (P.1 ∈ NoDrop ℓ x ∧ P.2 ∈ NoDrop ℓ y ∧ BoundaryAt ℓ H P n m) ↔
      (AdmissibleBoundaryPrefix ℓ H x y f g n m ∧
        P.1 ∈ FutureNoDrop ℓ n ∧ P.2 ∈ FutureNoDrop ℓ m) := by
  have hr1 j (hj : j ≤ n) : StrictRecord ℓ P.1 j ↔ StrictRecord ℓ f j :=
    strictRecord_congr_prefix ℓ hj hf
  have hr2 k (hk : k ≤ m) : StrictRecord ℓ P.2 k ↔ StrictRecord ℓ g k :=
    strictRecord_congr_prefix ℓ hk hg
  constructor
  · rintro ⟨hD1,hD2,hn,hm,⟨ht1,ht2,he⟩,hH,hfirst⟩
    refine ⟨⟨hn,hm,?_,(hr1 _ le_rfl).mp ht1.1,(hr2 _ le_rfl).mp ht2.1,
      ?_,?_,?_,?_⟩,ht1.2,ht2.2⟩
    · simpa only [hf _ le_rfl,hg _ le_rfl] using he
    · intro j hj
      simpa only [hf j hj] using hD1 j
    · intro k hk
      simpa only [hg k hk] using hD2 k
    · simpa only [hf _ le_rfl] using hH
    · intro j k hj hjn hk hkm hjH hrj hrk heq
      have hj' := (hr1 j hjn.le).mpr hrj
      have hk' := (hr2 k hkm.le).mpr hrk
      have he' : dot (realPosition (P.1 j)) ℓ = dot (realPosition (P.2 k)) ℓ := by
        simpa only [hf j hjn.le,hg k hkm.le] using heq
      have hnot := hfirst j k hj hjn hk hkm (by simpa only [hf j hjn.le] using hjH)
      have hdis : ¬ TrueRecord ℓ P.1 j ∨ ¬ TrueRecord ℓ P.2 k := by
        by_cases h1 : TrueRecord ℓ P.1 j
        · exact Or.inr fun h2 => hnot ⟨h1,h2,he'⟩
        · exact Or.inl h1
      rcases hdis with h1 | h2
      · obtain ⟨a,hja,han,ha⟩ := (not_trueRecord_before_true_iff ℓ P.1 hjn hj' ht1).mp h1
        exact Or.inl ⟨a,hja,han,by simpa only [hf a han.le,hf j hjn.le] using ha⟩
      · obtain ⟨b,hkb,hbm,hb⟩ := (not_trueRecord_before_true_iff ℓ P.2 hkm hk' ht2).mp h2
        exact Or.inr ⟨b,hkb,hbm,by simpa only [hg b hbm.le,hg k hkm.le] using hb⟩
  · rintro ⟨⟨hn,hm,he,hrf,hrg,hD1,hD2,hH,hfail⟩,hF1,hF2⟩
    have ht1 : TrueRecord ℓ P.1 n := ⟨(hr1 _ le_rfl).mpr hrf,hF1⟩
    have ht2 : TrueRecord ℓ P.2 m := ⟨(hr2 _ le_rfl).mpr hrg,hF2⟩
    refine ⟨(noDrop_iff_prefix_and_future ℓ x P.1 _ hF1).mpr ?_,
      (noDrop_iff_prefix_and_future ℓ y P.2 _ hF2).mpr ?_,
      hn,hm,⟨ht1,ht2,?_⟩,?_,?_⟩
    · intro j hj
      simpa only [hf j hj] using hD1 j hj
    · intro k hk
      simpa only [hg k hk] using hD2 k hk
    · simpa only [hf _ le_rfl,hg _ le_rfl] using he
    · simpa only [hf _ le_rfl] using hH
    · intro j k hj hjn hk hkm hjH htrue
      have hdis := hfail j k hj hjn hk hkm (by simpa only [hf j hjn.le] using hjH)
        ((hr1 _ hjn.le).mp htrue.1.1) ((hr2 _ hkm.le).mp htrue.2.1.1)
        (by simpa only [hf j hjn.le,hg k hkm.le] using htrue.2.2)
      rcases hdis with ⟨a,hja,han,ha⟩ | ⟨b,hkb,hbm,hb⟩
      · exact (not_trueRecord_before_true_iff ℓ P.1 hjn htrue.1.1 ht1).mpr
          ⟨a,hja,han,by simpa only [hf a han.le,hf j hjn.le] using ha⟩ htrue.1
      · exact (not_trueRecord_before_true_iff ℓ P.2 hkm htrue.2.1.1 ht2).mpr
          ⟨b,hkb,hbm,by simpa only [hg b hbm.le,hg k hkm.le] using hb⟩ htrue.2.1

lemma boundaryAt_unique {d : ℕ} (ℓ : Vector d) (H : ℝ) (P : Path d × Path d)
    {n m j k : ℕ} (hn : BoundaryAt ℓ H P n m) (hj : BoundaryAt ℓ H P j k) :
    n = j ∧ m = k := by
  have hnj : n = j := by
    rcases lt_trichotomy n j with h | h | h
    · exact False.elim (hj.2.2.2.2 n m hn.1 h hn.2.1
        ((commonTrueRecord_time_order ℓ P hn.2.2.1 hj.2.2.1).mp h) hn.2.2.2.1 hn.2.2.1)
    · exact h
    · exact False.elim (hn.2.2.2.2 j k hj.1 h hj.2.1
        ((commonTrueRecord_time_order ℓ P hj.2.2.1 hn.2.2.1).mp h) hj.2.2.2.1 hj.2.2.1)
  refine ⟨hnj,?_⟩
  apply Nat.le_antisymm
  · by_contra h
    have := (commonTrueRecord_time_order ℓ P hj.2.2.1 hn.2.2.1).mpr (by omega : k < m)
    omega
  · by_contra h
    have := (commonTrueRecord_time_order ℓ P hn.2.2.1 hj.2.2.1).mpr (by omega : m < k)
    omega

lemma boundaryAt_exists {d : ℕ} (ℓ : Vector d) (H : ℝ) (P : Path d × Path d)
    (h : ∃ n m, 0 < n ∧ 0 < m ∧ CommonTrueRecord ℓ P n m ∧
      H ≤ dot (realPosition (P.1 n)) ℓ) : ∃ n m, BoundaryAt ℓ H P n m := by
  obtain ⟨m,hn,hm,hr,hH⟩ := Nat.find_spec h
  exact ⟨Nat.find h,m,hn,hm,hr,hH,fun j k hj hjn hk _ hjH hc =>
    Nat.find_min h hjn ⟨k,hj,hk,hc,hjH⟩⟩

lemma measurableSet_boundaryAt {d : ℕ} (ℓ : Vector d) (H : ℝ) (n m : ℕ) :
    MeasurableSet {P : Path d × Path d | BoundaryAt ℓ H P n m} := by
  have hheight (j : ℕ) : MeasurableSet {P : Path d × Path d |
      H ≤ dot (realPosition (P.1 j)) ℓ} :=
    measurableSet_le measurable_const ((measurable_of_countable
      (fun z : Lattice d => dot (realPosition z) ℓ)).comp
      ((measurable_pi_apply j).comp measurable_fst))
  simp only [BoundaryAt,Set.ofPred_and,Set.ofPred_forall]
  refine (MeasurableSet.const _).inter ((MeasurableSet.const _).inter
    ((measurableSet_commonTrueRecord ℓ n m).inter ((hheight n).inter ?_)))
  refine MeasurableSet.iInter fun j => MeasurableSet.iInter fun k =>
    MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ =>
      MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ => ?_
  convert (hheight j).compl.union (measurableSet_commonTrueRecord ℓ j k).compl using 1
  ext P
  simp only [Set.mem_union,Set.mem_compl_iff,Set.mem_ofPred_eq,imp_iff_not_or]

lemma boundaryCode_exists {d : ℕ} (ℓ : Vector d) (H : ℝ) (P : Path d × Path d) :
    ∃ a : ℕ, BoundaryAt ℓ H P (Nat.unpair a).1 (Nat.unpair a).2 ∨
      ¬ ∃ n m, BoundaryAt ℓ H P n m := by
  by_cases h : ∃ n m, BoundaryAt ℓ H P n m
  · obtain ⟨n,m,hnm⟩ := h
    exact ⟨Nat.pair n m,Or.inl (by simpa only [Nat.unpair_pair] using hnm)⟩
  · exact ⟨0,Or.inr h⟩

noncomputable def boundaryCode {d : ℕ} (ℓ : Vector d) (H : ℝ) (P : Path d × Path d) : ℕ :=
  Nat.find (boundaryCode_exists ℓ H P)

noncomputable def boundaryTimes {d : ℕ} (ℓ : Vector d) (H : ℝ) (P : Path d × Path d) : ℕ × ℕ :=
  Nat.unpair (boundaryCode ℓ H P)

lemma measurable_boundaryCode {d : ℕ} (ℓ : Vector d) (H : ℝ) :
    Measurable (boundaryCode ℓ H) := by
  apply measurable_find
  intro a
  apply (measurableSet_boundaryAt ℓ H _ _).union
  change MeasurableSet ({P : Path d × Path d | ∃ n m, BoundaryAt ℓ H P n m}ᶜ)
  simp only [Set.ofPred_exists]
  exact (MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun m =>
    measurableSet_boundaryAt ℓ H n m).compl

lemma measurable_boundaryTimes {d : ℕ} (ℓ : Vector d) (H : ℝ) :
    Measurable (boundaryTimes ℓ H) := (measurable_of_countable _).comp (measurable_boundaryCode ℓ H)

lemma boundaryTimes_spec {d : ℕ} (ℓ : Vector d) (H : ℝ) (P : Path d × Path d)
    (h : ∃ n m, BoundaryAt ℓ H P n m) :
    BoundaryAt ℓ H P (boundaryTimes ℓ H P).1 (boundaryTimes ℓ H P).2 :=
  (Nat.find_spec (boundaryCode_exists ℓ H P)).resolve_right (not_not.mpr h)

lemma boundaryTimes_eq {d : ℕ} (ℓ : Vector d) (H : ℝ) (P : Path d × Path d)
    {n m : ℕ} (h : BoundaryAt ℓ H P n m) : boundaryTimes ℓ H P = (n,m) := by
  exact Prod.ext (boundaryAt_unique ℓ H P (boundaryTimes_spec ℓ H P ⟨n,m,h⟩) h).1
    (boundaryAt_unique ℓ H P (boundaryTimes_spec ℓ H P ⟨n,m,h⟩) h).2

def boundaryAtom {d : ℕ} (ℓ : Vector d) (H : ℝ) (x y : Lattice d)
    (f g : Path d) (n m : ℕ) : Set (Path d × Path d) :=
  (pathCylinder f n ×ˢ pathCylinder g m) ∩
    ((NoDrop ℓ x ×ˢ NoDrop ℓ y) ∩ {P | BoundaryAt ℓ H P n m})

lemma measurableSet_boundaryAtom {d : ℕ} (ℓ : Vector d) (H : ℝ) (x y : Lattice d)
    (f g : Path d) (n m : ℕ) : MeasurableSet (boundaryAtom ℓ H x y f g n m) :=
  ((measurableSet_pathCylinder f n).prod (measurableSet_pathCylinder g m)).inter
    (((measurableSet_noDrop ℓ x).prod (measurableSet_noDrop ℓ y)).inter
      (measurableSet_boundaryAt ℓ H n m))

lemma boundaryAtom_eq {d : ℕ} (ℓ : Vector d) (H : ℝ) (x y : Lattice d)
    (f g : Path d) (n m : ℕ) : boundaryAtom ℓ H x y f g n m =
      if AdmissibleBoundaryPrefix ℓ H x y f g n m then truePairCylinder ℓ f g n m else ∅ := by
  by_cases ha : AdmissibleBoundaryPrefix ℓ H x y f g n m
  · rw [ite_eq_left ha]
    ext P
    constructor
    · rintro ⟨⟨hf,hg⟩,⟨hD,hE⟩,hB⟩
      have := (boundaryPrefix_characterization ℓ H x y f g n m P hf hg).mp ⟨hD,hE,hB⟩
      exact ⟨⟨hf,hg⟩,this.2⟩
    · rintro ⟨⟨hf,hg⟩,hD,hE⟩
      have := (boundaryPrefix_characterization ℓ H x y f g n m P hf hg).mpr ⟨ha,hD,hE⟩
      exact ⟨⟨hf,hg⟩,⟨this.1,this.2.1⟩,this.2.2⟩
  · rw [ite_eq_right ha]
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro P ⟨⟨hf,hg⟩,⟨hD,hE⟩,hB⟩
    exact ha ((boundaryPrefix_characterization ℓ H x y f g n m P hf hg).mp ⟨hD,hE,hB⟩).1

lemma shared_boundaryAtom_map {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1)
    (htrans : DirectionallyTransient ν ℓ) (H : ℝ) (x y : Lattice d)
    (f g : Path d) (n m : ℕ) :
    ((sharedConditionedPairLaw ν ℓ x y).restrict (boundaryAtom ℓ H x y f g n m)).map
      (commonPairSuffix n m) =
        sharedConditionedPairLaw ν ℓ x y (boundaryAtom ℓ H x y f g n m) •
          sharedConditionedPairLaw ν ℓ (f n) (g m) := by
  rw [boundaryAtom_eq]
  split_ifs with ha
  · exact shared_truePairCylinder_map ν ℓ x y f g n m ha.1 ha.2.1
      ha.2.2.2.1 ha.2.2.2.2.1 ha.2.2.1 ha.2.2.2.2.2.1 ha.2.2.2.2.2.2.1
      (ne_of_gt (sharedNoDropMass_positive ν hue ℓ hℓ htrans _ _))
  · simp

lemma boundary_exists_of_commonLayer {d : ℕ} (ℓ : Vector d) (height : Lattice d → ℤ)
    (hproj : ∀ z, dot (realPosition z) ℓ = (height z : ℝ)) (x y : Lattice d)
    (hxy : height x = height y) (H : ℕ) (hH : 0 < H) (P : Path d × Path d)
    (hx : P.1 0 = x) (hy : P.2 0 = y)
    (hex : ∃ k : ℕ, P ∈ CommonLayer ℓ height (height x+H+k)) :
    ∃ n m, BoundaryAt ℓ ((height x+H : ℤ) : ℝ) P n m := by
  obtain ⟨k,n,m,hn,hm,hD,hE⟩ := hex
  apply boundaryAt_exists
  have hnpos : 0 < n := by
    by_contra h
    have he : n = 0 := by omega
    have hi := hn.1
    rw [he,hx] at hi
    omega
  have hmpos : 0 < m := by
    by_contra h
    have he : m = 0 := by omega
    have hi := hm.1
    rw [he,hy,← hxy] at hi
    omega
  refine ⟨n,m,hnpos,hmpos,⟨⟨firstLayerHit_record ℓ height hproj _ n P.1 hn,hD⟩,
    ⟨firstLayerHit_record ℓ height hproj _ m P.2 hm,hE⟩,?_⟩,?_⟩
  · rw [hproj,hproj,hn.1,hm.1]
  · rw [hproj,hn.1]
    exact_mod_cast (show height x+(H:ℤ) ≤ height x+H+k by omega)

lemma shared_boundaryTimes_spec {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1)
    (htrans : DirectionallyTransient ν ℓ) (height : Lattice d → ℤ)
    (hproj : ∀ z, dot (realPosition z) ℓ = (height z : ℝ))
    (hstep : ∀ z e, height (z+step e) ≤ height z+1)
    (x y : Lattice d) (hxy : height x = height y) (H : ℕ) (hH : 0 < H) :
    ∀ᵐ P ∂sharedConditionedPairLaw ν ℓ x y,
      BoundaryAt ℓ ((height x+H : ℤ) : ℝ) P
        (boundaryTimes ℓ ((height x+H : ℤ) : ℝ) P).1
        (boundaryTimes ℓ ((height x+H : ℤ) : ℝ) P).2 := by
  filter_upwards [sharedConditioned_regularPath ν ℓ htrans x y,
    shared_common_boundary_exists ν hue ℓ hℓ htrans height hproj hstep x y hxy H] with P hP hC
  exact boundaryTimes_spec ℓ _ P
    (boundary_exists_of_commonLayer ℓ height hproj x y hxy H hH P hP.1.1.1 hP.2.1.1 hC)

end DirectionalTransience

end

end

end OAI

import Mathlib
import OAI.Probability.Ballisticity.Estimates.JointPastRestart

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

namespace DirectionalTransience

def selectedBoundaryAt {d : ℕ} (ℓ : Vector d) (B : Lattice d × Lattice d → Prop) (P : Path d × Path d)
    (n m : ℕ) : Prop :=
  0 < n ∧ 0 < m ∧ CommonTrueRecord ℓ P n m ∧
    B (P.1 n,P.2 m) ∧
    ∀ j k, 0 < j → j < n → 0 < k → k < m →
      B (P.1 j,P.2 k) → ¬ CommonTrueRecord ℓ P j k

def selectedAdmissibleBoundaryPrefix {d : ℕ} (ℓ : Vector d) (B : Lattice d × Lattice d → Prop) (x y : Lattice d)
    (f g : Path d) (n m : ℕ) : Prop :=
  0 < n ∧ 0 < m ∧
    dot (realPosition (f n)) ℓ = dot (realPosition (g m)) ℓ ∧
    StrictRecord ℓ f n ∧ StrictRecord ℓ g m ∧
    (∀ j ≤ n, dot (realPosition x) ℓ ≤ dot (realPosition (f j)) ℓ) ∧
    (∀ k ≤ m, dot (realPosition y) ℓ ≤ dot (realPosition (g k)) ℓ) ∧
    B (f n,g m) ∧
    ∀ j k, 0 < j → j < n → 0 < k → k < m →
      B (f j,g k) → StrictRecord ℓ f j → StrictRecord ℓ g k →
      dot (realPosition (f j)) ℓ = dot (realPosition (g k)) ℓ →
      (∃ a, j < a ∧ a < n ∧ dot (realPosition (f a)) ℓ < dot (realPosition (f j)) ℓ) ∨
      (∃ b, k < b ∧ b < m ∧ dot (realPosition (g b)) ℓ < dot (realPosition (g k)) ℓ)

lemma selectedBoundaryPrefix_characterization {d : ℕ} (ℓ : Vector d) (B : Lattice d × Lattice d → Prop)
    (x y : Lattice d) (f g : Path d) (n m : ℕ) (P : Path d × Path d)
    (hf : P.1 ∈ pathCylinder f n) (hg : P.2 ∈ pathCylinder g m) :
    (P.1 ∈ NoDrop ℓ x ∧ P.2 ∈ NoDrop ℓ y ∧ selectedBoundaryAt ℓ B P n m) ↔
      (selectedAdmissibleBoundaryPrefix ℓ B x y f g n m ∧
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
    · simpa only [hf _ le_rfl,hg _ le_rfl] using hH
    · intro j k hj hjn hk hkm hjH hrj hrk heq
      have hj' := (hr1 j hjn.le).mpr hrj
      have hk' := (hr2 k hkm.le).mpr hrk
      have he' : dot (realPosition (P.1 j)) ℓ = dot (realPosition (P.2 k)) ℓ := by
        simpa only [hf j hjn.le,hg k hkm.le] using heq
      have hnot := hfirst j k hj hjn hk hkm (by simpa only [hf j hjn.le,hg k hkm.le] using hjH)
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
    · simpa only [hf _ le_rfl,hg _ le_rfl] using hH
    · intro j k hj hjn hk hkm hjH htrue
      have hdis := hfail j k hj hjn hk hkm (by simpa only [hf j hjn.le,hg k hkm.le] using hjH)
        ((hr1 _ hjn.le).mp htrue.1.1) ((hr2 _ hkm.le).mp htrue.2.1.1)
        (by simpa only [hf j hjn.le,hg k hkm.le] using htrue.2.2)
      rcases hdis with ⟨a,hja,han,ha⟩ | ⟨b,hkb,hbm,hb⟩
      · exact (not_trueRecord_before_true_iff ℓ P.1 hjn htrue.1.1 ht1).mpr
          ⟨a,hja,han,by simpa only [hf a han.le,hf j hjn.le] using ha⟩ htrue.1
      · exact (not_trueRecord_before_true_iff ℓ P.2 hkm htrue.2.1.1 ht2).mpr
          ⟨b,hkb,hbm,by simpa only [hg b hbm.le,hg k hkm.le] using hb⟩ htrue.2.1

lemma selectedBoundaryAt_unique {d : ℕ} (ℓ : Vector d) (B : Lattice d × Lattice d → Prop) (P : Path d × Path d)
    {n m j k : ℕ} (hn : selectedBoundaryAt ℓ B P n m) (hj : selectedBoundaryAt ℓ B P j k) :
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

lemma selectedBoundaryAt_exists {d : ℕ} (ℓ : Vector d) (B : Lattice d × Lattice d → Prop) (P : Path d × Path d)
    (h : ∃ n m, 0 < n ∧ 0 < m ∧ CommonTrueRecord ℓ P n m ∧
      B (P.1 n,P.2 m)) : ∃ n m, selectedBoundaryAt ℓ B P n m := by
  obtain ⟨m,hn,hm,hr,hH⟩ := Nat.find_spec h
  exact ⟨Nat.find h,m,hn,hm,hr,hH,fun j k hj hjn hk _ hjH hc =>
    Nat.find_min h hjn ⟨k,hj,hk,hc,hjH⟩⟩

lemma selectedMeasurableSet_boundaryAt {d : ℕ} (ℓ : Vector d) (B : Lattice d × Lattice d → Prop) (n m : ℕ) :
    MeasurableSet {P : Path d × Path d | selectedBoundaryAt ℓ B P n m} := by
  have hheight (j k : ℕ) : MeasurableSet {P : Path d × Path d | B (P.1 j,P.2 k)} :=
    ((Set.to_countable {z | B z}).measurableSet).preimage
      (((measurable_pi_apply j).comp measurable_fst).prodMk
        ((measurable_pi_apply k).comp measurable_snd))
  simp only [selectedBoundaryAt,Set.ofPred_and,Set.ofPred_forall]
  refine (MeasurableSet.const _).inter ((MeasurableSet.const _).inter
    ((measurableSet_commonTrueRecord ℓ n m).inter ((hheight n m).inter ?_)))
  refine MeasurableSet.iInter fun j => MeasurableSet.iInter fun k =>
    MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ =>
      MeasurableSet.iInter fun _ => MeasurableSet.iInter fun _ => ?_
  convert (hheight j k).compl.union (measurableSet_commonTrueRecord ℓ j k).compl using 1
  ext P
  simp only [Set.mem_union,Set.mem_compl_iff,Set.mem_ofPred_eq,imp_iff_not_or]

lemma selectedBoundaryCode_exists {d : ℕ} (ℓ : Vector d) (B : Lattice d × Lattice d → Prop) (P : Path d × Path d) :
    ∃ a : ℕ, selectedBoundaryAt ℓ B P (Nat.unpair a).1 (Nat.unpair a).2 ∨
      ¬ ∃ n m, selectedBoundaryAt ℓ B P n m := by
  by_cases h : ∃ n m, selectedBoundaryAt ℓ B P n m
  · obtain ⟨n,m,hnm⟩ := h
    exact ⟨Nat.pair n m,Or.inl (by simpa only [Nat.unpair_pair] using hnm)⟩
  · exact ⟨0,Or.inr h⟩

noncomputable def selectedBoundaryCode {d : ℕ} (ℓ : Vector d) (B : Lattice d × Lattice d → Prop) (P : Path d × Path d) : ℕ :=
  Nat.find (selectedBoundaryCode_exists ℓ B P)

noncomputable def selectedBoundaryTimes {d : ℕ} (ℓ : Vector d) (B : Lattice d × Lattice d → Prop) (P : Path d × Path d) : ℕ × ℕ :=
  Nat.unpair (selectedBoundaryCode ℓ B P)

lemma measurable_selectedBoundaryCode {d : ℕ} (ℓ : Vector d) (B : Lattice d × Lattice d → Prop) :
    Measurable (selectedBoundaryCode ℓ B) := by
  apply measurable_find
  intro a
  apply (selectedMeasurableSet_boundaryAt ℓ B _ _).union
  change MeasurableSet ({P : Path d × Path d | ∃ n m, selectedBoundaryAt ℓ B P n m}ᶜ)
  simp only [Set.ofPred_exists]
  exact (MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun m =>
    selectedMeasurableSet_boundaryAt ℓ B n m).compl

lemma measurable_selectedBoundaryTimes {d : ℕ} (ℓ : Vector d) (B : Lattice d × Lattice d → Prop) :
    Measurable (selectedBoundaryTimes ℓ B) := (measurable_of_countable _).comp (measurable_selectedBoundaryCode ℓ B)

lemma selectedBoundaryTimes_spec {d : ℕ} (ℓ : Vector d) (B : Lattice d × Lattice d → Prop) (P : Path d × Path d)
    (h : ∃ n m, selectedBoundaryAt ℓ B P n m) :
    selectedBoundaryAt ℓ B P (selectedBoundaryTimes ℓ B P).1 (selectedBoundaryTimes ℓ B P).2 :=
  (Nat.find_spec (selectedBoundaryCode_exists ℓ B P)).resolve_right (not_not.mpr h)

lemma selectedBoundaryTimes_eq {d : ℕ} (ℓ : Vector d) (B : Lattice d × Lattice d → Prop) (P : Path d × Path d)
    {n m : ℕ} (h : selectedBoundaryAt ℓ B P n m) : selectedBoundaryTimes ℓ B P = (n,m) := by
  exact Prod.ext (selectedBoundaryAt_unique ℓ B P (selectedBoundaryTimes_spec ℓ B P ⟨n,m,h⟩) h).1
    (selectedBoundaryAt_unique ℓ B P (selectedBoundaryTimes_spec ℓ B P ⟨n,m,h⟩) h).2

def selectedBoundaryAtom {d : ℕ} (ℓ : Vector d) (B : Lattice d × Lattice d → Prop) (x y : Lattice d)
    (f g : Path d) (n m : ℕ) : Set (Path d × Path d) :=
  (pathCylinder f n ×ˢ pathCylinder g m) ∩
    ((NoDrop ℓ x ×ˢ NoDrop ℓ y) ∩ {P | selectedBoundaryAt ℓ B P n m})

lemma selectedMeasurableSet_selectedBoundaryAtom {d : ℕ} (ℓ : Vector d) (B : Lattice d × Lattice d → Prop) (x y : Lattice d)
    (f g : Path d) (n m : ℕ) : MeasurableSet (selectedBoundaryAtom ℓ B x y f g n m) :=
  ((measurableSet_pathCylinder f n).prod (measurableSet_pathCylinder g m)).inter
    (((measurableSet_noDrop ℓ x).prod (measurableSet_noDrop ℓ y)).inter
      (selectedMeasurableSet_boundaryAt ℓ B n m))

lemma selectedBoundaryAtom_eq {d : ℕ} (ℓ : Vector d) (B : Lattice d × Lattice d → Prop) (x y : Lattice d)
    (f g : Path d) (n m : ℕ) : selectedBoundaryAtom ℓ B x y f g n m =
      if selectedAdmissibleBoundaryPrefix ℓ B x y f g n m then truePairCylinder ℓ f g n m else ∅ := by
  by_cases ha : selectedAdmissibleBoundaryPrefix ℓ B x y f g n m
  · rw [ite_eq_left ha]
    ext P
    constructor
    · rintro ⟨⟨hf,hg⟩,⟨hD,hE⟩,hB⟩
      have := (selectedBoundaryPrefix_characterization ℓ B x y f g n m P hf hg).mp ⟨hD,hE,hB⟩
      exact ⟨⟨hf,hg⟩,this.2⟩
    · rintro ⟨⟨hf,hg⟩,hD,hE⟩
      have := (selectedBoundaryPrefix_characterization ℓ B x y f g n m P hf hg).mpr ⟨ha,hD,hE⟩
      exact ⟨⟨hf,hg⟩,⟨this.1,this.2.1⟩,this.2.2⟩
  · rw [ite_eq_right ha]
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro P ⟨⟨hf,hg⟩,⟨hD,hE⟩,hB⟩
    exact ha ((selectedBoundaryPrefix_characterization ℓ B x y f g n m P hf hg).mp ⟨hD,hE,hB⟩).1

lemma shared_selectedBoundaryAtom_map {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1)
    (htrans : DirectionallyTransient ν ℓ) (B : Lattice d × Lattice d → Prop) (x y : Lattice d)
    (f g : Path d) (n m : ℕ) :
    ((sharedConditionedPairLaw ν ℓ x y).restrict (selectedBoundaryAtom ℓ B x y f g n m)).map
      (commonPairSuffix n m) =
        sharedConditionedPairLaw ν ℓ x y (selectedBoundaryAtom ℓ B x y f g n m) •
          sharedConditionedPairLaw ν ℓ (f n) (g m) := by
  rw [selectedBoundaryAtom_eq]
  split_ifs with ha
  · exact shared_truePairCylinder_map ν ℓ x y f g n m ha.1 ha.2.1
      ha.2.2.2.1 ha.2.2.2.2.1 ha.2.2.1 ha.2.2.2.2.2.1 ha.2.2.2.2.2.2.1
      (ne_of_gt (sharedNoDropMass_positive ν hue ℓ hℓ htrans _ _))
  · simp

noncomputable def selectedBoundaryData {d : ℕ} (ℓ : Vector d) (B : Lattice d × Lattice d → Prop) (P : Path d × Path d) :
    BoundaryData d := ⟨selectedBoundaryTimes ℓ B P,
      pairPrefix (selectedBoundaryTimes ℓ B P).1 (selectedBoundaryTimes ℓ B P).2 P⟩

lemma selectedBoundaryData_fiber {d : ℕ} (ℓ : Vector d) (B : Lattice d × Lattice d → Prop) (F : BoundaryData d) :
    selectedBoundaryData ℓ B ⁻¹' {F} =
      (selectedBoundaryTimes ℓ B ⁻¹' {F.1}) ∩ (pairPrefix F.1.1 F.1.2 ⁻¹' {F.2}) := by
  ext P
  simp only [Set.mem_preimage,Set.mem_singleton_iff,Set.mem_inter_iff]
  constructor
  · intro he
    have ht : selectedBoundaryTimes ℓ B P = F.1 := congrArg Sigma.fst he
    refine ⟨ht,?_⟩
    cases F with
    | mk q f =>
      dsimp only at ht ⊢
      unfold selectedBoundaryData at he
      cases ht
      exact Sigma.mk.inj_iff.mp he |>.2 |> eq_of_heq
  · rintro ⟨ht,hf⟩
    cases F with
    | mk q f =>
      dsimp only at ht hf ⊢
      unfold selectedBoundaryData
      cases ht
      exact congrArg (Sigma.mk _) hf

lemma measurable_selectedBoundaryData {d : ℕ} (ℓ : Vector d) (B : Lattice d × Lattice d → Prop) :
    Measurable (selectedBoundaryData ℓ B) := by
  apply measurable_to_countable'
  intro F
  rw [selectedBoundaryData_fiber]
  exact ((measurable_selectedBoundaryTimes ℓ B) (measurableSet_singleton _)).inter
    ((measurable_pairPrefix _ _) (measurableSet_singleton _))

noncomputable def selectedBoundarySuffix {d : ℕ} (ℓ : Vector d) (B : Lattice d × Lattice d → Prop) (P : Path d × Path d) :
    Path d × Path d := commonPairSuffix (selectedBoundaryTimes ℓ B P).1 (selectedBoundaryTimes ℓ B P).2 P

lemma measurable_selectedBoundarySuffix {d : ℕ} (ℓ : Vector d) (B : Lattice d × Lattice d → Prop) :
    Measurable (selectedBoundarySuffix ℓ B) := by
  have hm : Measurable (fun Z : (Path d × Path d) × (ℕ × ℕ) =>
      commonPairSuffix Z.2.1 Z.2.2 Z.1) :=
    measurable_from_prod_countable_left fun q => measurable_commonPairSuffix q.1 q.2
  exact hm.comp (measurable_id.prodMk (measurable_selectedBoundaryTimes ℓ B))

lemma selectedBoundaryData_times {d : ℕ} (ℓ : Vector d) (B : Lattice d × Lattice d → Prop) (P : Path d × Path d)
    (F : BoundaryData d) (hF : selectedBoundaryData ℓ B P = F) :
    selectedBoundaryTimes ℓ B P = F.1 := congrArg Sigma.fst hF

lemma selectedBoundaryAtom_fiber_ae {d : ℕ} (μ : Measure (Path d × Path d))
    (ℓ : Vector d) (B : Lattice d × Lattice d → Prop) (x y : Lattice d)
    (hD : ∀ᵐ P ∂μ, P.1 ∈ NoDrop ℓ x ∧ P.2 ∈ NoDrop ℓ y)
    (hS : ∀ᵐ P ∂μ, selectedBoundaryAt ℓ B P (selectedBoundaryTimes ℓ B P).1 (selectedBoundaryTimes ℓ B P).2)
    (F : BoundaryData d) :
    (selectedBoundaryData ℓ B ⁻¹' {F}) =ᵐ[μ]
      selectedBoundaryAtom ℓ B x y (extendPrefix F.1.1 F.2.1) (extendPrefix F.1.2 F.2.2) F.1.1 F.1.2 := by
  filter_upwards [hD,hS] with P hDP hSP
  rw [selectedBoundaryData_fiber,pairPrefix_fiber]
  apply propext
  change (selectedBoundaryTimes ℓ B P = F.1 ∧ _) ↔ _
  constructor
  · rintro ⟨ht,hpre⟩
    refine ⟨hpre,hDP,?_⟩
    change selectedBoundaryAt ℓ B P F.1.1 F.1.2
    simpa only [ht] using hSP
  · rintro ⟨hpre,hno,hB⟩
    exact ⟨selectedBoundaryTimes_eq ℓ B P hB,hpre⟩

lemma selectedBoundaryAt_exists_above {d : ℕ} (ℓ : Vector d)
    (B : Lattice d × Lattice d → Prop) (H : ℝ)
    (hB : ∀ z w, H ≤ dot (realPosition z) ℓ → B (z,w))
    (P : Path d × Path d) (h : ∃ n m, BoundaryAt ℓ H P n m) :
    ∃ n m, selectedBoundaryAt ℓ B P n m := by
  obtain ⟨n,m,hn⟩ := h
  exact selectedBoundaryAt_exists ℓ B P ⟨n,m,hn.1,hn.2.1,hn.2.2.1,hB _ _ hn.2.2.2.1⟩

lemma shared_selectedBoundaryTimes_spec {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1)
    (htrans : DirectionallyTransient ν ℓ) (height : Lattice d → ℤ)
    (hproj : ∀ z, dot (realPosition z) ℓ = (height z : ℝ))
    (hstep : ∀ z e, height (z+step e) ≤ height z+1)
    (x y : Lattice d) (hxy : height x = height y) (H : ℕ) (hH : 0 < H)
    (B : Lattice d × Lattice d → Prop)
    (hB : ∀ z w, height x+H ≤ height z → B (z,w)) :
    ∀ᵐ P ∂sharedConditionedPairLaw ν ℓ x y,
      selectedBoundaryAt ℓ B P (selectedBoundaryTimes ℓ B P).1 (selectedBoundaryTimes ℓ B P).2 := by
  filter_upwards [shared_boundaryTimes_spec ν hue ℓ hℓ htrans height hproj hstep x y hxy H hH]
    with P hP
  apply selectedBoundaryTimes_spec
  apply selectedBoundaryAt_exists_above ℓ B ((height x+H : ℤ) : ℝ) _ P
    ⟨_,_,hP⟩
  intro z w hz
  rw [hproj] at hz
  exact hB z w (by exact_mod_cast hz)

def BoundaryData.endpoints {d : ℕ} (F : BoundaryData d) : Lattice d × Lattice d :=
  (extendPrefix F.1.1 F.2.1 F.1.1,extendPrefix F.1.2 F.2.2 F.1.2)

lemma shared_selectedBoundaryData_map {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1)
    (htrans : DirectionallyTransient ν ℓ) (x y : Lattice d)
    (B : Lattice d × Lattice d → Prop)
    (hS : ∀ᵐ P ∂sharedConditionedPairLaw ν ℓ x y,
      selectedBoundaryAt ℓ B P (selectedBoundaryTimes ℓ B P).1 (selectedBoundaryTimes ℓ B P).2)
    (F : BoundaryData d) :
    ((sharedConditionedPairLaw ν ℓ x y).restrict
       (selectedBoundaryData ℓ B ⁻¹' {F})).map (selectedBoundarySuffix ℓ B) =
      sharedConditionedPairLaw ν ℓ x y (selectedBoundaryData ℓ B ⁻¹' {F}) •
      sharedConditionedPairLaw ν ℓ F.endpoints.1 F.endpoints.2 := by
  let μ := sharedConditionedPairLaw ν ℓ x y
  have hae := selectedBoundaryAtom_fiber_ae μ ℓ B x y
    (sharedConditionedPairLaw_noDrop ν ℓ x y) hS F
  have hmap : (μ.restrict (selectedBoundaryData ℓ B ⁻¹' {F})).map (selectedBoundarySuffix ℓ B) =
      (μ.restrict (selectedBoundaryData ℓ B ⁻¹' {F})).map (commonPairSuffix F.1.1 F.1.2) := by
    apply Measure.map_congr
    filter_upwards [ae_restrict_mem ((measurable_selectedBoundaryData ℓ B)
      (measurableSet_singleton F))] with P hP
    have ht := selectedBoundaryData_times ℓ B P F hP
    simp only [selectedBoundarySuffix,ht]
  change (μ.restrict (selectedBoundaryData ℓ B ⁻¹' {F})).map _ = _
  rw [hmap,Measure.restrict_congr_set hae,measure_congr hae]
  exact shared_selectedBoundaryAtom_map ν hue ℓ hℓ htrans B x y _ _ _ _

lemma lintegral_countable_restart_dependent {Ω I S : Type*} [MeasurableSpace Ω] [MeasurableSpace I]
    [MeasurableSpace S] [Countable I] [MeasurableSingletonClass I]
    (μ : Measure Ω) (D : Ω → I) (Y : Ω → S) (κ : I → Measure S)
    (hD : Measurable D) (hY : Measurable Y)
    (hrestart : ∀ i, (μ.restrict (D ⁻¹' {i})).map Y = μ (D ⁻¹' {i}) • κ i)
    (g : I → S → ℝ≥0∞) (hg : ∀ i, Measurable (g i)) :
    (∫⁻ a, g (D a) (Y a) ∂μ) = ∫⁻ a, (∫⁻ z, g (D a) z ∂κ (D a)) ∂μ := by
  rw [lintegral_partition_countable μ D hD,lintegral_partition_countable μ D hD]
  apply tsum_congr
  intro i
  have ha : ∀ᵐ a ∂μ.restrict (D ⁻¹' {i}), D a = i :=
    ae_restrict_mem (hD (measurableSet_singleton i))
  calc
    (∫⁻ a in D ⁻¹' {i}, g (D a) (Y a) ∂μ) =
        ∫⁻ a in D ⁻¹' {i}, g i (Y a) ∂μ :=
      lintegral_congr_ae (ha.mono fun a ha => by dsimp only; rw [ha])
    _ = ∫⁻ z, g i z ∂(μ.restrict (D ⁻¹' {i})).map Y := by
      rw [lintegral_map (hg i) hY]
    _ = μ (D ⁻¹' {i}) * ∫⁻ z, g i z ∂κ i := by
      rw [hrestart i,lintegral_smul_measure,smul_eq_mul]
    _ = ∫⁻ a in D ⁻¹' {i}, (∫⁻ z, g i z ∂κ i) ∂μ := by
      rw [lintegral_const,Measure.restrict_apply MeasurableSet.univ,Set.univ_inter]
      exact mul_comm _ _
    _ = ∫⁻ a in D ⁻¹' {i}, (∫⁻ z, g (D a) z ∂κ (D a)) ∂μ :=
      lintegral_congr_ae (ha.mono fun a ha => by dsimp only; rw [ha])

theorem shared_selected_jointPast_restart {d : ℕ} (ν : Measure (Row d)) [IsProbabilityMeasure ν]
    (hue : UniformElliptic ν) (ℓ : Vector d) (hℓ : dot ℓ ℓ = 1)
    (htrans : DirectionallyTransient ν ℓ) (height : Lattice d → ℤ)
    (hproj : ∀ z, dot (realPosition z) ℓ = (height z : ℝ))
    (hstep : ∀ z e, height (z+step e) ≤ height z+1)
    (x y : Lattice d) (hxy : height x = height y) (H : ℕ) (hH : 0 < H)
    (B : Lattice d × Lattice d → Prop)
    (hB : ∀ z w, height x+H ≤ height z → B (z,w))
    (g : BoundaryData d → (Path d × Path d) → ℝ≥0∞)
    (hg : ∀ F, Measurable (g F)) :
    (∫⁻ P, g (selectedBoundaryData ℓ B P) (selectedBoundarySuffix ℓ B P)
      ∂sharedConditionedPairLaw ν ℓ x y) =
    ∫⁻ P, (∫⁻ Q, g (selectedBoundaryData ℓ B P) Q
      ∂sharedConditionedPairLaw ν ℓ (selectedBoundaryData ℓ B P).endpoints.1
        (selectedBoundaryData ℓ B P).endpoints.2)
      ∂sharedConditionedPairLaw ν ℓ x y := by
  exact lintegral_countable_restart_dependent _ _ _ _ (measurable_selectedBoundaryData ℓ B)
    (measurable_selectedBoundarySuffix ℓ B)
    (shared_selectedBoundaryData_map ν hue ℓ hℓ htrans x y B
      (shared_selectedBoundaryTimes_spec ν hue ℓ hℓ htrans height hproj hstep x y hxy H hH B hB)) g hg

end DirectionalTransience

end

end

end OAI

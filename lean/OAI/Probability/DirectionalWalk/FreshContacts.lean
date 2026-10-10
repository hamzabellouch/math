import OAI.Probability.DirectionalWalk.ActualComparison

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

def wordPairCylinder {d : ℕ} (p : Word d × Word d) : Set (Path d × Path d) :=
  wordCylinder p.1 ×ˢ wordCylinder p.2

lemma measurableSet_wordPairCylinder {d : ℕ} (p : Word d × Word d) :
    MeasurableSet (wordPairCylinder p) :=
  (measurableSet_pathCylinder _ _).prod (measurableSet_pathCylinder _ _)

lemma wordPair_transfer {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (x z : Site d) (a b : Word d) (h : Disjoint (wordDepartures a) (wordDepartures b)) :
    annealed μ x (wordCylinder a) * annealed μ z (wordCylinder b) =
      ∫⁻ ω, quenchedKernel d (ω,x) (wordCylinder a) * quenchedKernel d (ω,z) (wordCylinder b)
        ∂environmentLaw μ := by
  simp only [wordCylinder,annealed_cylinder,quenchedKernel_cylinder]
  split_ifs <;> try simp only [zero_mul,mul_zero,lintegral_zero]
  exact (path_weights_disjoint μ a.1 b.1 (wordPath a) (wordPath b) (by
    intro i hi j hj hij
    exact Set.disjoint_left.mp h ⟨i,hi,rfl⟩ ⟨j,hj,hij.symm⟩)).symm

noncomputable def freshPair {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (x z : Site d) : Measure (Environment d × (Path d × Path d)) :=
  environmentLaw μ ⊗ₘ (freshPathKernel x ×ₖ freshPathKernel z)

instance {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ] (x z : Site d) :
    IsProbabilityMeasure (freshPair μ x z) := by
  unfold freshPair
  infer_instance

lemma freshPair_apply {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ] (x z : Site d)
    {E : Set (Environment d × (Path d × Path d))} (hE : MeasurableSet E) :
    freshPair μ x z E = ∫⁻ ω, ((quenchedKernel d (ω,x)).prod (quenchedKernel d (ω,z)))
      (Prod.mk ω ⁻¹' E) ∂environmentLaw μ := by
  rw [freshPair,Measure.compProd_apply hE]
  simp only [Kernel.prod_apply,freshPathKernel,Kernel.comap_apply]

lemma freshPair_first {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ] (x z : Site d)
    {E : Set (Environment d × Path d)} (hE : MeasurableSet E) :
    freshPair μ x z {ξ | (ξ.1,ξ.2.1) ∈ E} = freshJoint μ x E := by
  change freshPair μ x z ((fun ξ => (ξ.1,ξ.2.1)) ⁻¹' E) = _
  rw [freshPair_apply μ x z (hE.preimage (measurable_fst.prodMk measurable_snd.fst)),
    freshJoint_apply μ x hE]
  apply lintegral_congr
  intro ω
  rw [show (Prod.mk ω ⁻¹' (fun ξ : Environment d × (Path d × Path d) => (ξ.1,ξ.2.1)) ⁻¹' E) =
    (Prod.mk ω ⁻¹' E) ×ˢ Set.univ by ext p; simp]
  rw [Measure.prod_prod,measure_univ,mul_one]

lemma freshPair_second {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ] (x z : Site d)
    {E : Set (Environment d × Path d)} (hE : MeasurableSet E) :
    freshPair μ x z {ξ | (ξ.1,ξ.2.2) ∈ E} = freshJoint μ z E := by
  change freshPair μ x z ((fun ξ => (ξ.1,ξ.2.2)) ⁻¹' E) = _
  rw [freshPair_apply μ x z (hE.preimage (measurable_fst.prodMk measurable_snd.snd)),
    freshJoint_apply μ z hE]
  apply lintegral_congr
  intro ω
  rw [show (Prod.mk ω ⁻¹' (fun ξ : Environment d × (Path d × Path d) => (ξ.1,ξ.2.2)) ⁻¹' E) =
    Set.univ ×ˢ (Prod.mk ω ⁻¹' E) by ext p; simp]
  rw [Measure.prod_prod,measure_univ,one_mul]

lemma wordPairFamily_transfer {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (x z : Site d) (A : Set (Word d × Word d))
    (hdis : Pairwise (fun a b : A => Disjoint (wordPairCylinder a.val) (wordPairCylinder b.val)))
    (hrows : ∀ p ∈ A, Disjoint (wordDepartures p.1) (wordDepartures p.2)) :
    ((annealed μ x).prod (annealed μ z)) (⋃ p : A, wordPairCylinder p.val) =
      freshPair μ x z {ξ | ξ.2 ∈ ⋃ p : A, wordPairCylinder p.val} := by
  have hm := MeasurableSet.iUnion (fun p : A => measurableSet_wordPairCylinder p.val)
  change ((annealed μ x).prod (annealed μ z)) (⋃ p : A, wordPairCylinder p.val) =
    freshPair μ x z (Prod.snd ⁻¹' (⋃ p : A, wordPairCylinder p.val))
  rw [freshPair_apply μ x z (hm.preimage measurable_snd),
    measure_iUnion hdis (fun p => measurableSet_wordPairCylinder p.val)]
  simp only [wordPairCylinder,Measure.prod_prod]
  simp_rw [wordPair_transfer μ x z _ _ (hrows _ (Subtype.property _))]
  rw [← lintegral_tsum]
  · apply lintegral_congr
    intro ω
    change (∑' p : A, quenchedKernel d (ω,x) (wordCylinder p.val.1) *
      quenchedKernel d (ω,z) (wordCylinder p.val.2)) =
        ((quenchedKernel d (ω,x)).prod (quenchedKernel d (ω,z))) (⋃ p : A, wordPairCylinder p.val)
    rw [measure_iUnion hdis (fun p => measurableSet_wordPairCylinder p.val)]
    apply tsum_congr
    intro p
    rw [wordPairCylinder,Measure.prod_prod]
  · intro p
    exact ((((quenchedKernel d).measurable_coe (measurableSet_pathCylinder _ _)).comp
      (measurable_id.prodMk measurable_const)).mul
      (((quenchedKernel d).measurable_coe (measurableSet_pathCylinder _ _)).comp
        (measurable_id.prodMk measurable_const))).aemeasurable

lemma wordPairFamily_visit_bound {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (x z : Site d) (A : Set (Word d × Word d))
    (hdis : Pairwise (fun a b : A => Disjoint (wordPairCylinder a.val) (wordPairCylinder b.val)))
    (hrows : ∀ p ∈ A, Disjoint (wordDepartures p.1) (wordDepartures p.2))
    (V W : Set (Environment d × Path d)) (hV : MeasurableSet V) (hW : MeasurableSet W)
    (hcover : ∀ ξ : Environment d × (Path d × Path d),
      (∃ p : A, ξ.2 ∈ wordPairCylinder p.val) → (ξ.1,ξ.2.1) ∈ V ∨ (ξ.1,ξ.2.2) ∈ W) :
    ((annealed μ x).prod (annealed μ z)) (⋃ p : A, wordPairCylinder p.val) ≤
      freshJoint μ x V + freshJoint μ z W := by
  rw [wordPairFamily_transfer μ x z A hdis hrows]
  calc
    _ ≤ freshPair μ x z ({ξ | (ξ.1,ξ.2.1) ∈ V} ∪ {ξ | (ξ.1,ξ.2.2) ∈ W}) :=
      measure_mono (fun ξ hξ => hcover ξ (Set.mem_iUnion.mp hξ))
    _ ≤ _ := (measure_union_le _ _).trans_eq (by rw [freshPair_first μ x z hV,freshPair_second μ x z hW])

def firstContactPairs {d : ℕ} (T R S K : Set (Site d)) : Set (Word d × Word d) :=
  {p | firstHitWord T p.1 ∧ firstHitWord (wordDepartures p.1) p.2 ∧
    (∃ i < p.1.1, wordPath p.1 i = wordEnd p.2 ∧
      (∃ j ≤ i, wordPath p.1 j ∈ R) ∧ ∀ j ≤ i, wordPath p.1 j ∉ K) ∧
    (∃ j ≤ p.2.1, wordPath p.2 j ∈ S) ∧ ∀ j ≤ p.2.1, wordPath p.2 j ∉ K}

lemma firstContactPairs_rows {d : ℕ} (T R S K : Set (Site d)) (p : Word d × Word d)
    (hp : p ∈ firstContactPairs T R S K) :
    Disjoint (wordDepartures p.1) (wordDepartures p.2) := by
  apply Set.disjoint_left.mpr
  rintro y hy ⟨j,hj,hjy⟩
  exact hp.2.1.2 j hj (hjy ▸ hy)

lemma firstContactPairs_disjoint {d : ℕ} (T R S K : Set (Site d)) :
    Pairwise (fun p q : firstContactPairs T R S K =>
      Disjoint (wordPairCylinder p.val) (wordPairCylinder q.val)) := by
  intro p q hpq
  apply Set.disjoint_left.mpr
  rintro ⟨X,Y⟩ ⟨hp1,hp2⟩ ⟨hq1,hq2⟩
  by_cases h1 : p.val.1 = q.val.1
  · have h2 : p.val.2 ≠ q.val.2 := by
      intro h2
      apply hpq
      exact Subtype.ext (Prod.ext h1 h2)
    have ha := p.property.2.1
    have hb := q.property.2.1
    rw [← h1] at hb
    exact Set.disjoint_left.mp (firstHitWords_prefixFree (wordDepartures p.val.1)
      (i := ⟨p.val.2,ha⟩) (j := ⟨q.val.2,hb⟩)
      (fun h => h2 (congrArg Subtype.val h))) hp2 hq2
  · exact Set.disjoint_left.mp (firstHitWords_prefixFree T
      (i := ⟨p.val.1,p.property.1⟩) (j := ⟨q.val.1,q.property.1⟩)
      (fun h => h1 (congrArg Subtype.val h))) hp1 hq1

lemma firstContactPairs_classify {d : ℕ} (T R S K : Set (Site d))
    (A : Set (Site d)) (p : firstContactPairs T R S K) (X Y : Path d)
    (h : (X,Y) ∈ wordPairCylinder p.val) :
    X ∈ visitAfter R (A \ K) K ∨ Y ∈ visitAfter S (Aᶜ \ K) K := by
  change (X ∈ wordCylinder p.val.1 ∧ Y ∈ wordCylinder p.val.2) at h
  obtain ⟨i,hi,he,⟨j,hji,hR⟩,hK⟩ := p.property.2.2.1
  have hyK : wordEnd p.val.2 ∉ K := by rw [← he];exact hK i le_rfl
  by_cases hy : wordEnd p.val.2 ∈ A
  · left
    refine ⟨i,?_,⟨j,hji,?_⟩,fun k hk => ?_⟩
    · rw [h.1 i hi.le,he]
      exact ⟨hy,hyK⟩
    · rw [h.1 j (hji.trans hi.le)]
      exact hR
    · rw [h.1 k (hk.trans hi.le)]
      exact hK k hk
  · right
    obtain ⟨j,hj,hS⟩ := p.property.2.2.2.1
    refine ⟨p.val.2.1,?_,⟨j,hj,?_⟩,fun k hk => ?_⟩
    · rw [h.2 _ le_rfl]
      exact ⟨hy,hyK⟩
    · rw [h.2 j hj]
      exact hS
    · rw [h.2 k hk]
      exact p.property.2.2.2.2 k hk

lemma firstContactPairs_visit_bound {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (x z : Site d) (T R S K : Set (Site d)) (A : Environment d → Set (Site d))
    (hA : ∀ y, MeasurableSet {ω | y ∈ A ω}) :
    ((annealed μ x).prod (annealed μ z))
      (⋃ p : firstContactPairs T R S K, wordPairCylinder p.val) ≤
      freshJoint μ x {ξ | ξ.2 ∈ visitAfter R (A ξ.1 \ K) K} +
      freshJoint μ z {ξ | ξ.2 ∈ visitAfter S ((A ξ.1)ᶜ \ K) K} := by
  apply wordPairFamily_visit_bound μ x z _ (firstContactPairs_disjoint T R S K)
    (firstContactPairs_rows T R S K) _ _
    (measurable_random_visitAfter _ _ _ (fun y => (hA y).diff (MeasurableSet.const _)))
    (measurable_random_visitAfter _ _ _ (fun y => (hA y).compl.diff (MeasurableSet.const _)))
  rintro ⟨ω,X,Y⟩ ⟨p,hp⟩
  exact firstContactPairs_classify T R S K (A ω) p X Y hp

lemma freshJoint_visitAfter_bound {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (x : Site d) (R B C : Set (Site d)) (A : Environment d → Set (Site d))
    (hA : ∀ y, MeasurableSet {ω | y ∈ A ω}) (c : ℝ≥0∞)
    (hc : ∀ᵐ ω ∂environmentLaw μ, ∀ y ∈ A ω,
      c ≤ quenchedKernel d (ω,y) (hitBefore B C)) :
    c * freshJoint μ x {ξ | ξ.2 ∈ visitAfter R (A ξ.1) (B ∪ C)} ≤
      annealed μ x (hitBefore R B ∩ hitBefore B C) := by
  rw [freshJoint_apply μ x (measurable_random_visitAfter _ _ _ hA),
    annealed_apply μ x ((measurableSet_hitBefore _ _).inter (measurableSet_hitBefore _ _))]
  apply (lintegral_const_mul_le _ _).trans
  apply lintegral_mono_ae
  filter_upwards [hc] with ω hω
  exact quenched_visitAfter_bound ω x R (A ω) B C c hω

lemma firstContactPairs_raw_bound {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (x z : Site d) (T R S B C : Set (Site d))
    (hex : ∀ᵐ ω ∂environmentLaw μ, ∀ y,
      quenchedKernel d (ω,y) (hitBefore B C) + quenchedKernel d (ω,y) (hitBefore C B) = 1) :
    ((annealed μ x).prod (annealed μ z))
      (⋃ p : firstContactPairs T R S (B ∪ C), wordPairCylinder p.val) ≤
      2*(annealed μ x (hitBefore R B ∩ hitBefore B C) +
        annealed μ z (hitBefore S C ∩ hitBefore C B)) := by
  let A : Environment d → Set (Site d) := fun ω =>
    {y | (2 : ℝ≥0∞)⁻¹ ≤ quenchedKernel d (ω,y) (hitBefore B C)}
  have hA (y : Site d) : MeasurableSet {ω | y ∈ A ω} :=
    measurableSet_le measurable_const (((quenchedKernel d).measurable_coe (measurableSet_hitBefore _ _)).comp
      (measurable_id.prodMk measurable_const))
  have hv := firstContactPairs_visit_bound μ x z T R S (B ∪ C) A hA
  have h1 := freshJoint_visitAfter_bound μ x R B C (fun ω => A ω \ (B ∪ C))
    (fun y => (hA y).diff (MeasurableSet.const _)) (2 : ℝ≥0∞)⁻¹ (by
      filter_upwards [] with ω
      exact fun y hy => hy.1)
  have h2 := freshJoint_visitAfter_bound μ z S C B (fun ω => (A ω)ᶜ \ (B ∪ C))
    (fun y => (hA y).compl.diff (MeasurableSet.const _)) (2 : ℝ≥0∞)⁻¹ (by
      filter_upwards [hex] with ω hω
      intro y hy
      have hy' : quenchedKernel d (ω,y) (hitBefore B C) ≤ (2 : ℝ≥0∞)⁻¹ := le_of_lt (lt_of_not_ge hy.1)
      apply (ENNReal.add_le_add_iff_left (by norm_num : (2 : ℝ≥0∞)⁻¹ ≠ ∞)).mp
      calc
        (2 : ℝ≥0∞)⁻¹ + (2 : ℝ≥0∞)⁻¹ = 1 := ENNReal.inv_two_add_inv_two
        _ = _ := (hω y).symm
        _ ≤ _ := add_le_add hy' le_rfl)
  rw [Set.union_comm C B] at h2
  have h : (2 : ℝ≥0∞)⁻¹ * ((annealed μ x).prod (annealed μ z))
      (⋃ p : firstContactPairs T R S (B ∪ C), wordPairCylinder p.val) ≤
      annealed μ x (hitBefore R B ∩ hitBefore B C) +
        annealed μ z (hitBefore S C ∩ hitBefore C B) := by
    calc
      _ ≤ (2 : ℝ≥0∞)⁻¹ * (freshJoint μ x {ξ | ξ.2 ∈ visitAfter R (A ξ.1 \ (B ∪ C)) (B ∪ C)} +
        freshJoint μ z {ξ | ξ.2 ∈ visitAfter S ((A ξ.1)ᶜ \ (B ∪ C)) (B ∪ C)}) := by gcongr
      _ ≤ _ := by rw [mul_add]; exact add_le_add h1 h2
  have h' := mul_le_mul (show (2 : ℝ≥0∞) ≤ 2 from le_rfl) h zero_le zero_le
  simpa only [← mul_assoc,ENNReal.mul_inv_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞),one_mul] using h'

end DirectionalZeroOne

end OAI

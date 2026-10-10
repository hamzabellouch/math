import OAI.Probability.DirectionalWalk.ContactGeometry

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

def visits {d : ℕ} (y : Site d) : Set (Path d) := {X | ∃ n, X n = y}

lemma measurableSet_visits {d : ℕ} (y : Site d) : MeasurableSet (visits y) := by
  simp only [visits,Set.ofPred_exists]
  exact MeasurableSet.iUnion (fun n => measurableSet_eq_fun (measurable_pi_apply n) measurable_const)

def contactAvoid {d : ℕ} (a : Word d) : Set (Path d) :=
  visits (wordEnd a) ∩ avoids (wordDepartures a)

lemma measurableSet_contactAvoid {d : ℕ} (a : Word d) : MeasurableSet (contactAvoid a) :=
  (measurableSet_visits _).inter (measurableSet_avoids _)

lemma contactAvoid_iff_firstHit {d : ℕ} (a : Word d) (B : Path d) :
    B ∈ contactAvoid a ↔ firstHitWord (Set.range B) a := by
  constructor
  · rintro ⟨⟨n,hn⟩,hb⟩
    refine ⟨⟨n,hn⟩,fun i hi ⟨j,hj⟩ => ?_⟩
    exact hb j ⟨i,hi,hj.symm⟩
  · rintro ⟨⟨n,hn⟩,hb⟩
    refine ⟨⟨n,hn⟩,fun j ⟨i,hi,he⟩ => ?_⟩
    exact hb i hi ⟨j,he.symm⟩

def contactRectangle {d : ℕ} (a : Word d) : Set (Path d × Path d) :=
  wordCylinder a ×ˢ contactAvoid a

lemma measurableSet_contactRectangle {d : ℕ} (a : Word d) : MeasurableSet (contactRectangle a) :=
  (measurableSet_pathCylinder _ _).prod (measurableSet_contactAvoid a)

lemma contactRectangles_disjoint {d : ℕ} :
    Pairwise (fun a b : Word d => Disjoint (contactRectangle a) (contactRectangle b)) := by
  intro a b hab
  apply Set.disjoint_left.mpr
  rintro ⟨X,B⟩ ⟨ha,hBa⟩ ⟨hb,hBb⟩
  have h1 := (contactAvoid_iff_firstHit a B).mp hBa
  have h2 := (contactAvoid_iff_firstHit b B).mp hBb
  have hd := firstHitWords_prefixFree (Set.range B) (i := ⟨a,h1⟩) (j := ⟨b,h2⟩)
    (fun h => hab (congrArg Subtype.val h))
  exact Set.disjoint_left.mp hd ha hb

lemma annealed_contactRectangle_transfer {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (x z : Site d) (a : Word d) (ha : wordPath a 0 = x) {D : Set (Path d)}
    (hD : MeasurableSet D) :
    annealed μ x (wordCylinder a) * annealed μ z (D ∩ contactAvoid a) =
      ∫⁻ ω, ((quenchedKernel d (ω,x)).prod (quenchedKernel d (ω,z)))
        (wordCylinder a ×ˢ (D ∩ contactAvoid a)) ∂environmentLaw μ := by
  have he : D ∩ contactAvoid a = (D ∩ visits (wordEnd a)) ∩ avoids (wordDepartures a) := by
    ext X
    exact and_assoc.symm
  rw [he,wordCylinder,annealed_cylinder,ite_eq_left ha.symm,
    ← word_contact_transfer μ a z (hD.inter (measurableSet_visits _))]
  apply lintegral_congr
  intro ω
  rw [Measure.prod_prod,quenchedKernel_cylinder,ite_eq_left ha.symm]

lemma weighted_contact_transfer {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (x z : Site d) (A : Set (Word d)) (hA : ∀ a ∈ A, wordPath a 0 = x)
    (w : Word d → ℝ≥0∞) {D : Set (Path d)} (hD : MeasurableSet D) :
    ∑' a : A, w a * (annealed μ x (wordCylinder a) * annealed μ z (D ∩ contactAvoid a)) =
      ∫⁻ ω, ∑' a : A, w a * (((quenchedKernel d (ω,x)).prod (quenchedKernel d (ω,z)))
        (wordCylinder a ×ˢ (D ∩ contactAvoid a))) ∂environmentLaw μ := by
  simp_rw [annealed_contactRectangle_transfer μ x z _ (hA _ (Subtype.mem _)) hD,
    Measure.prod_prod]
  have hm (a : A) : Measurable (fun ω : Environment d =>
      quenchedKernel d (ω,x) (wordCylinder a) *
        quenchedKernel d (ω,z) (D ∩ contactAvoid a)) :=
    (((quenchedKernel d).measurable_coe (measurableSet_pathCylinder _ _)).comp
      (measurable_id.prodMk measurable_const)).mul
      (((quenchedKernel d).measurable_coe (hD.inter (measurableSet_contactAvoid _))).comp
      (measurable_id.prodMk measurable_const))
  have hwm (a : A) : Measurable (fun ω : Environment d => w a *
      (quenchedKernel d (ω,x) (wordCylinder a) *
        quenchedKernel d (ω,z) (D ∩ contactAvoid a))) := measurable_const.mul (hm a)
  rw [lintegral_tsum (fun a => (hwm a).aemeasurable)]
  apply tsum_congr
  intro a
  exact (lintegral_const_mul (w a) (hm a)).symm

lemma hits_eq_firstHitWords {d : ℕ} (A : Set (Site d)) :
    {X : Path d | ∃ n, X n ∈ A} = ⋃ a : {a | firstHitWord A a}, wordCylinder a.val := by
  classical
  ext X
  constructor
  · intro h
    let n := Nat.find h
    have ha : firstHitWord A (prefixWord n X) := by
      refine ⟨?_,fun i hi => ?_⟩
      · change wordPath (prefixWord n X) n ∈ A
        rw [wordPath_prefixWord n X le_rfl]
        exact Nat.find_spec h
      · rw [wordPath_prefixWord n X hi.le]
        exact Nat.find_min h (show i < Nat.find h from hi)
    exact Set.mem_iUnion.mpr ⟨⟨prefixWord n X,ha⟩,fun i hi => (wordPath_prefixWord n X hi).symm⟩
  · intro h
    obtain ⟨a,ha⟩ := Set.mem_iUnion.mp h
    exact ⟨a.val.1,by rw [ha a.val.1 le_rfl];exact a.property.1⟩

lemma negative_visit_firstWord_subset {d : ℕ} (A B C : Set (Site d)) :
    {X : Path d | (∃ n, X n ∈ A) ∧ (∀ n, ∃ m, n ≤ m ∧ X m ∈ B) ∧ X ∈ avoids C} ⊆
      ⋃ a : {a | firstHitWord A a}, wordCylinder a.val ∩ tailPath a.val.1 ⁻¹' hitBefore B C := by
  rintro X ⟨hA,hB,hC⟩
  obtain ⟨a,ha⟩ := Set.mem_iUnion.mp ((Set.ext_iff.mp (hits_eq_firstHitWords A) X).mp hA)
  obtain ⟨m,hm,hbm⟩ := hB a.val.1
  obtain ⟨j,hj⟩ := Nat.exists_eq_add_of_le hm
  refine Set.mem_iUnion.mpr ⟨a,ha,j,?_,fun i _ => ?_⟩
  · simpa only [tailPath,← hj] using hbm
  · exact hC (a.val.1+i)

lemma quenched_negative_visit_bound {d : ℕ} (ω : Environment d) (x : Site d)
    (A B C : Set (Site d)) (c : ℝ≥0∞)
    (hc : ∀ y ∈ A, quenchedKernel d (ω,y) (hitBefore B C) ≤ c) :
    quenchedKernel d (ω,x)
      {X | (∃ n, X n ∈ A) ∧ (∀ n, ∃ m, n ≤ m ∧ X m ∈ B) ∧ X ∈ avoids C} ≤ c := by
  apply (measure_mono (negative_visit_firstWord_subset A B C)).trans
  rw [quenched_prefix_family ω x _ (firstHitWords_prefixFree _) (fun _ => hitBefore B C)
    (fun _ _ => measurableSet_hitBefore _ _)]
  calc
    ∑' a : {a | firstHitWord A a}, quenchedKernel d (ω,x) (wordCylinder a) *
        quenchedKernel d (ω,wordEnd a) (hitBefore B C) ≤
      ∑' a : {a | firstHitWord A a}, c * quenchedKernel d (ω,x) (wordCylinder a) := by
        apply ENNReal.tsum_le_tsum
        intro a
        rw [mul_comm c]
        exact mul_le_mul_right (hc _ a.property.1) _
    _ = c * quenchedKernel d (ω,x) (⋃ a : {a | firstHitWord A a}, wordCylinder a.val) := by
      rw [ENNReal.tsum_mul_left,measure_iUnion (firstHitWords_prefixFree A)
        (fun _ => measurableSet_pathCylinder _ _)]
    _ ≤ c := by
      simpa only [mul_one] using mul_le_mul_right (prob_le_one
        (μ := quenchedKernel d (ω,x))) c

def lateVisits {d : ℕ} (A : Set (Site d)) : Set (Path d) :=
  {X | ∀ n, ∃ m, n ≤ m ∧ X m ∈ A}

lemma measurableSet_lateVisits {d : ℕ} (A : Set (Site d)) : MeasurableSet (lateVisits A) := by
  simp only [lateVisits,Set.ofPred_forall,Set.ofPred_exists,Set.ofPred_and]
  apply MeasurableSet.iInter
  intro n
  apply MeasurableSet.iUnion
  intro m
  exact (MeasurableSet.const _).inter ((Set.to_countable A).measurableSet.preimage (measurable_pi_apply m))

lemma annealed_avoidsUpper_lateLower {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d) (x : Site d) (k N : ℤ) :
    ∀ᵐ X ∂annealed μ x, X ∈ avoids (axisUpper e N) → X ∈ lateVisits (axisLower e k) := by
  filter_upwards [finite_supremum μ hell x (axisDirection e) (axisDirection_ne_zero e)] with X hX
  intro hD
  have hbound : ∃ b, ∀ n, height (axisDirection e) (X n) ≤ b := by
    refine ⟨(N : ℝ),fun n => ?_⟩
    have hn : axisHeight e (X n) < N := lt_of_not_ge (hD n)
    rw [height_axisDirection]
    exact_mod_cast hn.le
  have ht := tendsto_atBot.mp (hX hbound) ((k-1 : ℤ) : ℝ)
  obtain ⟨m,hm⟩ := eventually_atTop.mp ht
  intro n
  refine ⟨max m n,le_max_right _ _,?_⟩
  have he := hm (max m n) (le_max_left _ _)
  rw [height_axisDirection] at he
  have hh : axisHeight e (X (max m n)) ≤ k-1 := by exact_mod_cast he
  change axisHeight e (X (max m n)) < k
  omega

lemma quenched_negative_bins {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d) :
    ∀ᵐ ω ∂environmentLaw μ, ∀ (x : Site d) (k N : ℤ) (K : Set (Site d)) (c : ℝ≥0∞),
      (∀ y ∈ K, quenchedKernel d (ω,y) (hitBefore (axisLower e k) (axisUpper e N)) ≤ c) →
      quenchedKernel d (ω,x) (avoids (axisUpper e N) ∩ {B | ∃ n, B n ∈ K}) ≤ c := by
  have hAE : ∀ᵐ ω ∂environmentLaw μ, ∀ (x : Site d) (k N : ℤ),
      ∀ᵐ X ∂quenchedKernel d (ω,x),
        X ∈ avoids (axisUpper e N) → X ∈ lateVisits (axisLower e k) := by
    simp only [ae_all_iff]
    intro x k N
    apply annealed_ae_quenched μ x
    · simp only [imp_iff_not_or]
      exact (measurableSet_avoids _).compl.union (measurableSet_lateVisits _)
    · exact annealed_avoidsUpper_lateLower μ hell e x k N
  filter_upwards [hAE] with ω hω
  intro x k N K c hc
  apply (measure_mono_ae (show (avoids (axisUpper e N) ∩ {B | ∃ n, B n ∈ K} : Set (Path d)) ≤ᵐ[quenchedKernel d (ω,x)]
    {X | (∃ n, X n ∈ K) ∧ (∀ n, ∃ m, n ≤ m ∧ X m ∈ axisLower e k) ∧ X ∈ avoids (axisUpper e N)} from ?_)).trans
    (quenched_negative_visit_bound ω x K (axisLower e k) (axisUpper e N) c hc)
  filter_upwards [hω x k N] with X hX
  exact fun h => ⟨h.2,hX h.1,h.1⟩

lemma weighted_disjoint_measure_bound {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι]
    (μ : Measure Ω) (s : ι → Set Ω) (hs : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (fun i j => Disjoint (s i) (s j))) (w : ι → ℝ≥0∞) (F : Ω → ℝ≥0∞)
    (E : Set Ω) (hsub : ∀ i, s i ⊆ E) (hbound : ∀ i, ∀ ω ∈ s i, w i ≤ F ω) :
    ∑' i, w i * μ (s i) ≤ ∫⁻ ω in E, F ω ∂μ := by
  calc
    ∑' i, w i * μ (s i) ≤ ∑' i, ∫⁻ ω in s i, F ω ∂μ := by
      apply ENNReal.tsum_le_tsum
      intro i
      rw [← setLIntegral_const]
      apply setLIntegral_mono' (hs i)
      exact hbound i
    _ = ∫⁻ ω in ⋃ i, s i, F ω ∂μ := (lintegral_iUnion hs hd F).symm
    _ ≤ _ := lintegral_mono_set (Set.iUnion_subset hsub)

lemma weighted_contact_bin_bound {d : ℕ} (P Q : Measure (Path d)) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (A : Set (Word d)) (D V : Set (Path d)) (K : Set (Site d))
    (hD : MeasurableSet D) (w : Word d → ℝ≥0∞) (M : Path d → ℝ≥0∞)
    (hM : Measurable M) (hA : ∀ a ∈ A, wordEnd a ∈ K)
    (hAV : ∀ a ∈ A, wordCylinder a ⊆ V)
    (hw : ∀ a ∈ A, ∀ X ∈ wordCylinder a, w a ≤ M X) (c : ℝ≥0∞)
    (hc : Q (D ∩ {B | ∃ n, B n ∈ K}) ≤ c) :
    ∑' a : A, w a * (P (wordCylinder a) * Q (D ∩ contactAvoid a)) ≤
      c * ∫⁻ X in V, M X ∂P := by
  let R : Set (Path d) := D ∩ {B | ∃ n, B n ∈ K}
  have hR : MeasurableSet R := hD.inter (by
    simp only [Set.ofPred_exists]
    exact MeasurableSet.iUnion (fun n => (Set.to_countable K).measurableSet.preimage (measurable_pi_apply n)))
  have hs (a : A) : MeasurableSet (wordCylinder a.val ×ˢ (D ∩ contactAvoid a.val)) :=
    (measurableSet_pathCylinder _ _).prod (hD.inter (measurableSet_contactAvoid _))
  have hd : Pairwise (fun a b : A => Disjoint
      (wordCylinder a.val ×ˢ (D ∩ contactAvoid a.val))
      (wordCylinder b.val ×ˢ (D ∩ contactAvoid b.val))) := by
    intro a b hab
    apply (contactRectangles_disjoint (i := a.val) (j := b.val) (fun h => hab (Subtype.ext h))).mono
    · exact fun _ h => ⟨h.1,h.2.2⟩
    · exact fun _ h => ⟨h.1,h.2.2⟩
  have hsub (a : A) : wordCylinder a.val ×ˢ (D ∩ contactAvoid a.val) ⊆ V ×ˢ R := by
    rintro ⟨X,B⟩ ⟨hX,hB⟩
    obtain ⟨n,hn⟩ := hB.2.1
    exact ⟨hAV _ a.property hX,hB.1,n,hn ▸ hA _ a.property⟩
  have h := weighted_disjoint_measure_bound (P.prod Q)
    (fun a : A => wordCylinder a.val ×ˢ (D ∩ contactAvoid a.val)) hs hd
    (fun a => w a) (fun p => M p.1) (V ×ˢ R) hsub
    (fun a _ h => hw a a.property _ h.1)
  simp only [Measure.prod_prod] at h
  apply h.trans
  rw [setLIntegral_prod (fun p : Path d × Path d => M p.1) (hM.comp measurable_fst).aemeasurable.restrict]
  simp only [setLIntegral_const]
  rw [lintegral_mul_const _ hM]
  rw [mul_comm]
  exact mul_le_mul_left hc _

end DirectionalZeroOne

end OAI

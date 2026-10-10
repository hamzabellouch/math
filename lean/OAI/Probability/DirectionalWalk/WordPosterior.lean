import OAI.Probability.DirectionalWalk.ContactEvents

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

open scoped Classical

noncomputable def firstVisitIndex {d : ℕ} (K : Set (Site d)) (X : Path d) : ℕ :=
  if h : ∃ n, X n ∈ K then Nat.find h else 0

lemma firstVisitIndex_eq {d : ℕ} (K : Set (Site d)) (X : Path d) (h : ∃ n, X n ∈ K) :
    firstVisitIndex K X = Nat.find h := by simp only [firstVisitIndex,dite_eq_left h]

lemma firstVisitIndex_fiber {d : ℕ} (K : Set (Site d)) (n : ℕ) :
    {X : Path d | firstVisitIndex K X = n} =
      {X | X n ∈ K ∧ ∀ i < n, X i ∉ K} ∪ {X | n = 0 ∧ ¬∃ i, X i ∈ K} := by
  classical
  ext X
  change firstVisitIndex K X = n ↔ (X n ∈ K ∧ ∀ i < n, X i ∉ K) ∨ (n = 0 ∧ ¬∃ i, X i ∈ K)
  by_cases h : ∃ i, X i ∈ K
  · rw [firstVisitIndex,dite_eq_left h]
    simp only [h,not_true_eq_false,and_false,or_false]
    exact Nat.find_eq_iff h
  · have hn : X n ∉ K := fun hn => h ⟨n,hn⟩
    rw [firstVisitIndex,dite_eq_right h]
    simp only [hn,h,false_and,
      not_false_eq_true,and_true,false_or,eq_comm]

lemma measurable_firstVisitIndex {d : ℕ} (K : Set (Site d)) : Measurable (firstVisitIndex K) := by
  apply measurable_to_countable'
  intro n
  change MeasurableSet {X : Path d | firstVisitIndex K X = n}
  rw [firstVisitIndex_fiber]
  have hi (i : ℕ) : MeasurableSet {X : Path d | X i ∈ K} :=
    (Set.to_countable K).measurableSet.preimage (measurable_pi_apply i)
  have hp : MeasurableSet {X : Path d | ∀ i < n, X i ∉ K} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun _ => (hi i).compl))
  have hno : MeasurableSet {X : Path d | ¬∃ i, X i ∈ K} := by
    change MeasurableSet ({X : Path d | ∃ i, X i ∈ K}ᶜ)
    simp only [Set.ofPred_exists]
    exact (MeasurableSet.iUnion hi).compl
  exact ((hi n).inter hp).union ((MeasurableSet.const _).inter hno)

noncomputable def firstVisitWord {d : ℕ} (K : Set (Site d)) (X : Path d) : Word d :=
  prefixWord (firstVisitIndex K X) X

lemma measurable_firstVisitWord {d : ℕ} (K : Set (Site d)) : Measurable (firstVisitWord K) := by
  exact (measurable_from_prod_countable_right (f := fun (p : ℕ × Path d) => prefixWord p.1 p.2) (fun n => measurable_prefixWord n)).comp
    ((measurable_firstVisitIndex K).prodMk measurable_id)

lemma firstVisitWord_spec {d : ℕ} (K : Set (Site d)) (X : Path d) (h : ∃ n, X n ∈ K) :
    firstHitWord K (firstVisitWord K X) ∧ X ∈ wordCylinder (firstVisitWord K X) := by
  classical
  have he := firstVisitIndex_eq K X h
  refine ⟨⟨?_,fun i hi => ?_⟩,fun i hi => ?_⟩
  · change wordPath (prefixWord (firstVisitIndex K X) X) (firstVisitIndex K X) ∈ K
    rw [wordPath_prefixWord _ _ le_rfl,he]
    exact Nat.find_spec h
  · change wordPath (prefixWord (firstVisitIndex K X) X) i ∉ K
    rw [wordPath_prefixWord _ _ (show i ≤ firstVisitIndex K X from hi.le)]
    exact Nat.find_min h (he ▸ (show i < firstVisitIndex K X from hi))
  · exact (wordPath_prefixWord _ _ hi).symm

lemma firstVisitWord_eq_of_cylinder {d : ℕ} (K : Set (Site d)) (a : Word d)
    (ha : firstHitWord K a) (X : Path d) (hX : X ∈ wordCylinder a) :
    firstVisitWord K X = a := by
  have hex : ∃ n, X n ∈ K := ⟨a.1,by rw [hX _ le_rfl];exact ha.1⟩
  have hs := firstVisitWord_spec K X hex
  by_contra hne
  exact Set.disjoint_left.mp (firstHitWords_prefixFree K
    (i := ⟨firstVisitWord K X,hs.1⟩) (j := ⟨a,ha⟩) (fun h => hne (congrArg Subtype.val h))) hs.2 hX

lemma firstVisitWord_fiber_ae {d : ℕ} (P : Measure (Path d)) (K : Set (Site d))
    (hP : ∀ᵐ X ∂P, ∃ n, X n ∈ K) (a : Word d) :
    (firstVisitWord K ⁻¹' {a} : Set (Path d)) =ᵐ[P]
      (if firstHitWord K a then wordCylinder a else ∅ : Set (Path d)) := by
  classical
  filter_upwards [hP] with X hX
  have hs := firstVisitWord_spec K X hX
  by_cases ha : firstHitWord K a
  · rw [ite_eq_left ha]
    apply propext
    change firstVisitWord K X = a ↔ X ∈ wordCylinder a
    exact ⟨fun he => he ▸ hs.2,firstVisitWord_eq_of_cylinder K a ha X⟩
  · rw [ite_eq_right ha]
    apply propext
    change firstVisitWord K X = a ↔ False
    exact ⟨fun he => ha (he ▸ hs.1),False.elim⟩

lemma firstVisitWord_map_eq {d : ℕ} (P Q : Measure (Path d)) (K : Set (Site d))
    (hP : ∀ᵐ X ∂P, ∃ n, X n ∈ K) (hQ : ∀ᵐ X ∂Q, ∃ n, X n ∈ K)
    (h : ∀ a, firstHitWord K a → P (wordCylinder a) = Q (wordCylinder a)) :
    P.map (firstVisitWord K) = Q.map (firstVisitWord K) := by
  classical
  apply Measure.ext_of_singleton
  intro a
  rw [Measure.map_apply (measurable_firstVisitWord K) (measurableSet_singleton a),
    Measure.map_apply (measurable_firstVisitWord K) (measurableSet_singleton a),
    measure_congr (firstVisitWord_fiber_ae P K hP a),measure_congr (firstVisitWord_fiber_ae Q K hQ a)]
  by_cases ha : firstHitWord K a
  · simp only [ite_eq_left ha];exact h a ha
  · simp only [ite_eq_right ha,measure_empty]

noncomputable def continuationLaw {d : ℕ} (P : Measure (Path d)) (a : Word d) : Measure (Path d) :=
  (ProbabilityTheory.cond P (wordCylinder a)).map (tailPath a.1)

lemma continuationLaw_probability {d : ℕ} (P : Measure (Path d)) [IsProbabilityMeasure P]
    (a : Word d) (ha : P (wordCylinder a) ≠ 0) : IsProbabilityMeasure (continuationLaw P a) := by
  let := ProbabilityTheory.cond_isProbabilityMeasure (μ := P) ha
  exact probabilityMeasure_map (measurable_tailPath a.1).aemeasurable

lemma annealed_disjoint_prefix_tail' {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (x : Site d) (n m : ℕ) (γ δ : Path d)
    (hdis : ∀ i < n, ∀ j < m, γ i ≠ δ j) :
    annealed μ x (pathCylinder n γ ∩ tailPath n ⁻¹' pathCylinder m δ) =
      annealed μ x (pathCylinder n γ) * annealed μ (γ n) (pathCylinder m δ) := by
  classical
  by_cases hjoin : γ n = δ 0
  · exact annealed_disjoint_prefix_tail μ x n m γ δ hjoin hdis
  · have he : pathCylinder n γ ∩ tailPath n ⁻¹' pathCylinder m δ = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro X ⟨hX,hY⟩
      exact hjoin ((hX n le_rfl).symm.trans (by simpa only [tailPath,Nat.add_zero] using hY 0 (Nat.zero_le m)))
    rw [he,measure_empty,annealed_cylinder μ (γ n) m δ,ite_eq_right hjoin,mul_zero]

lemma continuationLaw_fresh_cylinder {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (x : Site d) (a b : Word d) (ha : annealed μ x (wordCylinder a) ≠ 0)
    (hdis : Disjoint (wordDepartures a) (wordDepartures b)) :
    continuationLaw (annealed μ x) a (wordCylinder b) = annealed μ (wordEnd a) (wordCylinder b) := by
  dsimp only [continuationLaw,wordCylinder]
  rw [Measure.map_apply (measurable_tailPath a.1) (measurableSet_pathCylinder _ _),
    ProbabilityTheory.cond_apply (measurableSet_pathCylinder _ _) _ _]
  rw [annealed_disjoint_prefix_tail' μ x a.1 b.1 (wordPath a) (wordPath b) (by
    intro i hi j hj he
    exact Set.disjoint_left.mp hdis ⟨i,hi,rfl⟩ ⟨j,hj,he.symm⟩)]
  change (annealed μ x (wordCylinder a))⁻¹ * (annealed μ x (wordCylinder a) *
    annealed μ (wordEnd a) (wordCylinder b)) = _
  rw [← mul_assoc,ENNReal.inv_mul_cancel ha (measure_ne_top _ _),one_mul]
  rfl

lemma firstHitWords_full_of_cylinder_eq {d : ℕ} (P Q : Measure (Path d))
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (K : Set (Site d))
    (hQ : ∀ᵐ X ∂Q, ∃ n, X n ∈ K)
    (h : ∀ a, firstHitWord K a → P (wordCylinder a) = Q (wordCylinder a)) :
    ∀ᵐ X ∂P, ∃ n, X n ∈ K := by
  have hm : MeasurableSet {X : Path d | ∃ n, X n ∈ K} := by
    rw [hits_eq_firstHitWords]
    exact MeasurableSet.iUnion (fun _ => measurableSet_pathCylinder _ _)
  have he : P {X | ∃ n, X n ∈ K} = Q {X | ∃ n, X n ∈ K} := by
    rw [hits_eq_firstHitWords,measure_iUnion (firstHitWords_prefixFree K)
      (fun _ => measurableSet_pathCylinder _ _),measure_iUnion (firstHitWords_prefixFree K)
      (fun _ => measurableSet_pathCylinder _ _)]
    exact tsum_congr (fun a => h a a.property)
  have hq : Q {X | ∃ n, X n ∈ K} = 1 := by
    rw [← measure_univ (μ := Q)]
    exact measure_congr (by filter_upwards [hQ] with X hX;exact propext ⟨fun _ => trivial,fun _ => hX⟩)
  rw [ae_iff]
  change P ({X | ∃ n, X n ∈ K}ᶜ) = 0
  rw [measure_compl hm (measure_ne_top _ _),he,hq,measure_univ,tsub_self]

lemma continuationLaw_fresh_stopped {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (x : Site d) (a : Word d) (K : Set (Site d)) (ha : annealed μ x (wordCylinder a) ≠ 0)
    (hdep : wordDepartures a ⊆ K)
    (hex : ∀ᵐ X ∂annealed μ (wordEnd a), ∃ n, X n ∈ K) :
    (continuationLaw (annealed μ x) a).map (firstVisitWord K) =
      (annealed μ (wordEnd a)).map (firstVisitWord K) := by
  have := continuationLaw_probability (annealed μ x) a ha
  have he (b : Word d) (hb : firstHitWord K b) :
      continuationLaw (annealed μ x) a (wordCylinder b) = annealed μ (wordEnd a) (wordCylinder b) := by
    apply continuationLaw_fresh_cylinder μ x a b ha
    apply Set.disjoint_left.mpr
    rintro y hy ⟨j,hj,rfl⟩
    exact hb.2 j hj (hdep hy)
  exact firstVisitWord_map_eq _ _ K (firstHitWords_full_of_cylinder_eq _ _ K hex he) hex he

noncomputable def wordPosterior {d ι : ℕ} (P : Measure (Path d))
    (E : Fin ι → Set (Path d)) (e : Fin ι) (a : Word d) : ℝ :=
  P.real (E e ∩ wordCylinder a) / P.real (wordCylinder a)

noncomputable def endpointPosterior {d ι : ℕ} (P : Measure (Path d))
    (E : Fin ι → Set (Path d)) (e : Fin ι) (n : ℕ) (X : Path d) : ℝ :=
  wordPosterior P E e (prefixWord n X)

lemma wordCylinder_prefixWord {d : ℕ} (n : ℕ) (X : Path d) :
    wordCylinder (prefixWord n X) = pathCylinder n X := by
  ext Y
  constructor
  · intro h i hi
    exact (h i hi).trans (wordPath_prefixWord n X hi)
  · intro h i hi
    exact (h i hi).trans (wordPath_prefixWord n X hi).symm

lemma endpointPosterior_eq_ratio {d ι : ℕ} (P : Measure (Path d))
    (E : Fin ι → Set (Path d)) (e : Fin ι) (n : ℕ) (X : Path d) :
    endpointPosterior P E e n X = P.real (E e ∩ pathCylinder n X) / P.real (pathCylinder n X) := by
  simp only [endpointPosterior,wordPosterior,wordCylinder_prefixWord]

lemma measurable_prefixWord_filtration {d : ℕ} (n : ℕ) :
    Measurable[pathFiltration d n] (prefixWord (d := d) n) := by
  rw [pathFiltration_eq]
  exact (measurable_of_countable (fun a : Finset.Iic n → Site d => (⟨n,a⟩ : Word d))).comp
    (Measurable.of_comap_le le_rfl)

lemma endpointPosterior_adapted {d ι : ℕ} (P : Measure (Path d)) (E : Fin ι → Set (Path d))
    (e : Fin ι) (n : ℕ) : StronglyMeasurable[pathFiltration d n] (endpointPosterior P E e n) :=
  ((measurable_of_countable (wordPosterior P E e)).comp (measurable_prefixWord_filtration n)).stronglyMeasurable

lemma endpointPosterior_condExp {d ι : ℕ} (P : Measure (Path d)) [IsFiniteMeasure P]
    (E : Fin ι → Set (Path d)) (hE : ∀ e, MeasurableSet (E e)) (e : Fin ι) (n : ℕ) :
    P[(E e).indicator (fun _ => (1 : ℝ)) | pathFiltration d n] =ᵐ[P] endpointPosterior P E e n := by
  filter_upwards [ae_pathCylinder_ne_zero P] with X hX
  rw [endpointPosterior_eq_ratio]
  have hp : P.real (pathCylinder n X) ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨hX n,measure_ne_top _ _⟩
  apply (eq_div_iff hp).mpr
  simpa only [mul_comm] using condExp_indicator_cylinder P (hE e) n X

lemma endpointPosterior_martingale {d ι : ℕ} (P : Measure (Path d)) [IsFiniteMeasure P]
    (E : Fin ι → Set (Path d)) (hE : ∀ e, MeasurableSet (E e)) (e : Fin ι) :
    Martingale (endpointPosterior P E e) (pathFiltration d) P := by
  apply (martingale_condExp ((E e).indicator (fun _ => (1 : ℝ))) (pathFiltration d) P).congr
  · exact endpointPosterior_adapted P E e
  · exact endpointPosterior_condExp P E hE e

lemma wordPosterior_bounds {d ι : ℕ} (P : Measure (Path d)) [IsFiniteMeasure P]
    (E : Fin ι → Set (Path d)) (hE : ∀ e, MeasurableSet (E e))
    (hdis : Pairwise (fun i j => Disjoint (E i) (E j))) (a : Word d) :
    (∀ e, 0 ≤ wordPosterior P E e a) ∧ ∑ e, wordPosterior P E e a ≤ 1 := by
  constructor
  · exact fun _ => div_nonneg measureReal_nonneg measureReal_nonneg
  · unfold wordPosterior
    rw [← Finset.sum_div]
    by_cases hp : P.real (wordCylinder a) = 0
    · simp only [hp,div_zero];norm_num
    · have hp0 : 0 < P.real (wordCylinder a) := lt_of_le_of_ne measureReal_nonneg (Ne.symm hp)
      apply (div_le_one hp0).mpr
      rw [← measureReal_iUnion_fintype (μ := P) (f := fun i => E i ∩ wordCylinder a) (fun i j hij => (hdis hij).mono Set.inter_subset_left Set.inter_subset_left)
        (fun i => (hE i).inter (measurableSet_pathCylinder _ _)) (fun _ => measure_ne_top _ _)]
      exact measureReal_mono (Set.iUnion_subset (fun _ => Set.inter_subset_right)) (measure_ne_top _ _)

lemma endpointPosterior_bounds {d ι : ℕ} (P : Measure (Path d)) [IsFiniteMeasure P]
    (E : Fin ι → Set (Path d)) (hE : ∀ e, MeasurableSet (E e))
    (hdis : Pairwise (fun i j => Disjoint (E i) (E j))) :
    (∀ e n X, 0 ≤ endpointPosterior P E e n X) ∧
    (∀ n X, ∑ e, endpointPosterior P E e n X ≤ 1) :=
  ⟨fun e n X => (wordPosterior_bounds P E hE hdis (prefixWord n X)).1 e,
    fun n X => (wordPosterior_bounds P E hE hdis (prefixWord n X)).2⟩

lemma endpointPosterior_prefix {d ι : ℕ} (P : Measure (Path d))
    (E : Fin ι → Set (Path d)) (e : Fin ι) (a : Word d) (X : Path d)
    (hX : X ∈ wordCylinder a) {j : ℕ} (hj : j ≤ a.1) :
    endpointPosterior P E e j X = endpointPosterior P E e j (wordPath a) := by
  unfold endpointPosterior
  rw [prefixWord_of_wordCylinder a X hX j hj]

noncomputable def wordEndpointMax {d ι : ℕ} (P : Measure (Path d))
    (E : Fin ι → Set (Path d)) (a : Word d) : ℝ :=
  posteriorMax (endpointPosterior P E) a.1 (wordPath a)

lemma wordEndpointMax_prefixWord {d ι : ℕ} (P : Measure (Path d))
    (E : Fin ι → Set (Path d)) (n : ℕ) (X : Path d) :
    wordEndpointMax P E (prefixWord n X) = posteriorMax (endpointPosterior P E) n X := by
  classical
  unfold wordEndpointMax posteriorMax
  apply Finset.sum_congr rfl
  intro e _
  unfold runningMax
  apply Finset.sup'_congr _ rfl
  intro j hj
  exact (endpointPosterior_prefix P E e (prefixWord n X) X
    (by intro i hi;exact (wordPath_prefixWord n X hi).symm)
    (Nat.le_of_lt_succ (Finset.mem_range.mp hj))).symm

lemma wordEndpointMax_bounds {d ι : ℕ} (P : Measure (Path d)) [IsFiniteMeasure P]
    (E : Fin ι → Set (Path d)) (hE : ∀ e, MeasurableSet (E e))
    (hdis : Pairwise (fun i j => Disjoint (E i) (E j))) (a : Word d) :
    0 ≤ wordEndpointMax P E a ∧ wordEndpointMax P E a ≤ ι := by
  have hb := endpointPosterior_bounds P E hE hdis
  exact ⟨posteriorMax_nonneg _ hb.1 _ _,by simpa only [wordEndpointMax,Fintype.card_fin] using posteriorMax_le_card _ hb.1 hb.2 a.1 (wordPath a)⟩

lemma stoppedEndpointMax_le {d ι : ℕ} (P : Measure (Path d)) [IsFiniteMeasure P]
    (E : Fin ι → Set (Path d)) (hE : ∀ e, MeasurableSet (E e))
    (hdis : Pairwise (fun i j => Disjoint (E i) (E j))) (K : Set (Site d)) (X : Path d) :
    wordEndpointMax P E (firstVisitWord K X) ≤ posteriorSup (endpointPosterior P E) X := by
  rw [firstVisitWord,wordEndpointMax_prefixWord]
  have hb := endpointPosterior_bounds P E hE hdis
  have hba : BddAbove (Set.range (fun n => posteriorMax (endpointPosterior P E) n X)) :=
    ⟨(ι : ℝ),by rintro _ ⟨n,rfl⟩;simpa only [Fintype.card_fin] using posteriorMax_le_card _ hb.1 hb.2 n X⟩
  exact le_ciSup hba _

lemma stoppedEndpointMax_exponential {d ι : ℕ} [NeZero ι]
    (P Q : Measure (Path d)) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (E : Fin ι → Set (Path d)) (hE : ∀ e, MeasurableSet (E e))
    (hdis : Pairwise (fun i j => Disjoint (E i) (E j))) (K : Set (Site d))
    (he : P.map (firstVisitWord K) = Q.map (firstVisitWord K)) :
    (∫ X, Real.exp (posteriorExponent / Real.log (ι+1) * wordEndpointMax P E (firstVisitWord K X)) ∂Q) ≤ 12 := by
  let c := posteriorExponent / Real.log (ι+1)
  have hc : 0 ≤ c := (div_pos posteriorExponent_pos
    (Real.log_pos (by exact_mod_cast (show 1 < ι+1 by have := NeZero.pos ι;omega)))).le
  have hf : Measurable (fun X => wordEndpointMax P E (firstVisitWord K X)) :=
    (measurable_of_countable (wordEndpointMax P E)).comp (measurable_firstVisitWord K)
  have hi : (∫ X, Real.exp (c * wordEndpointMax P E (firstVisitWord K X)) ∂Q) =
      ∫ X, Real.exp (c * wordEndpointMax P E (firstVisitWord K X)) ∂P := by
    have hsm := (measurable_of_countable (fun a : Word d => Real.exp (c*wordEndpointMax P E a))).stronglyMeasurable
    rw [← integral_map_of_stronglyMeasurable (measurable_firstVisitWord K) hsm,
      ← integral_map_of_stronglyMeasurable (measurable_firstVisitWord K) hsm,he]
  rw [show posteriorExponent / Real.log (↑ι+1) = c from rfl,hi]
  have hw := endpointPosterior_martingale P E hE
  have hb := endpointPosterior_bounds P E hE hdis
  apply (integral_mono (integrable_exp_of_bound P _ hf ι c (fun X => (wordEndpointMax_bounds P E hE hdis _).2) hc)
    (integrable_exp_of_bound P _ (measurable_posteriorSup P (pathFiltration d) _ hw) ι c
      (fun X => by simpa using (posteriorSup_bounds _ hb.1 hb.2 X).2) hc)
    (fun X => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (stoppedEndpointMax_le P E hE hdis K X) hc))).trans
  simpa only [Fintype.card_fin] using posteriorSup_exponential_log P (pathFiltration d) _ hw hb.1 hb.2

lemma stoppedEndpointMax_joint_weight {d ι : ℕ} [NeZero ι]
    {Ξ : Type*} [MeasurableSpace Ξ] (P Q : Measure (Path d))
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (E : Fin ι → Set (Path d)) (hE : ∀ e, MeasurableSet (E e))
    (hdis : Pairwise (fun i j => Disjoint (E i) (E j))) (K : Set (Site d))
    (he : P.map (firstVisitWord K) = Q.map (firstVisitWord K))
    (ν : Measure Ξ) [IsProbabilityMeasure ν] (π : Ξ → Path d) (hπ : MeasurePreserving π ν Q)
    (V : Set Ξ) :
    (∫ ξ in V, wordEndpointMax P E (firstVisitWord K (π ξ)) ∂ν) ≤
      (12/posteriorExponent) * Real.log (ι+1) * ν.real V * (1-Real.log (ν.real V)) := by
  let c := posteriorExponent / Real.log (ι+1)
  let f := fun X => wordEndpointMax P E (firstVisitWord K X)
  have hc : 0 < c := div_pos posteriorExponent_pos
    (Real.log_pos (by exact_mod_cast (show 1 < ι+1 by have := NeZero.pos ι;omega)))
  have hm : Measurable f := (measurable_of_countable (wordEndpointMax P E)).comp (measurable_firstVisitWord K)
  have hib : Integrable f Q := (integrable_const (ι : ℝ)).mono' hm.aestronglyMeasurable (by
    filter_upwards [] with X
    rw [Real.norm_eq_abs,abs_of_nonneg (wordEndpointMax_bounds P E hE hdis _).1]
    exact (wordEndpointMax_bounds P E hE hdis _).2)
  have hie := integrable_exp_of_bound Q f hm ι c (fun X => (wordEndpointMax_bounds P E hE hdis _).2) hc.le
  have hex : (∫ ξ, Real.exp (c*f (π ξ)) ∂ν) ≤ 12 := by
    have hi : (∫ ξ, Real.exp (c*f (π ξ)) ∂ν) = ∫ X, Real.exp (c*f X) ∂Q := by
      rw [← hπ.map_eq]
      exact (integral_map_of_stronglyMeasurable hπ.measurable (hm.const_mul c).exp.stronglyMeasurable).symm
    rw [hi]
    exact stoppedEndpointMax_exponential P Q E hE hdis K he
  have hi := setIntegral_entropy_of_exp ν (fun ξ => f (π ξ))
    (hπ.integrable_comp_of_integrable hib) c hc (hπ.integrable_comp_of_integrable hie) hex V
  have hs : 12/c = (12/posteriorExponent)*Real.log (ι+1) := by dsimp [c];field_simp
  simpa only [hs] using hi

end DirectionalZeroOne

end OAI

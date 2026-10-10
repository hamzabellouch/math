import OAI.Probability.DirectionalWalk.RelativeContinuation

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

lemma property_of_atom {α : Type*} [MeasurableSpace α] (ν : Measure α)
    (P : α → Prop) (hP : ∀ᵐ a ∂ν, P a) (a : α) (ha : ν {a} ≠ 0) : P a := by
  by_contra h
  apply ha
  exact measure_mono_null (Set.singleton_subset_iff.mpr h) (ae_iff.mp hP)

lemma windowCommonLaw_support {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (P : Bool → α → Prop) (hP : ∀ b, ∀ᵐ a ∂ν b, P b a) (k n : ℕ) :
    ∀ᵐ a ∂windowCommonLaw ν L k n, InCountWindow L k n a ∧ ∀ b i, P b ((a b).2 i) := by
  classical
  filter_upwards [ae_atom_pos (windowCommonLaw ν L k n),windowCommonLaw_ae_window ν L hL he k n] with a ha hw
  rw [windowCommonLaw_atom ν L hL he,ite_eq_left hw] at ha
  have hp : twoListWeight ν a ≠ 0 := right_ne_zero_of_mul ha
  refine ⟨hw,fun b i => property_of_atom (ν b) (P b) (hP b) _ ?_⟩
  exact (Finset.prod_ne_zero_iff.mp (Finset.prod_ne_zero_iff.mp hp b (Finset.mem_univ b))) i (Finset.mem_univ i)

lemma listCommonCount_le_height {α : Type*} (L : Bool → α → ℕ) (a : TwoTapeList α) :
    listCommonCount L a ≤ chunkHeight L a := by
  classical
  unfold listCommonCount chunkHeight
  calc
    _ ≤ ∑ _j ∈ Finset.range (listHeight (L false) (a false)), 1 := by
      apply Finset.sum_le_sum
      intro j hj
      split_ifs <;> omega
    _ = _ := by simp

lemma experimentLaw_fourWindows {α G : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [AddCommGroup G] [Countable G] [MeasurableSpace G]
    [MeasurableSingletonClass G] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (D : Bool → α → G) (n : ℕ) :
    experimentLaw ν L D n = ((windowCommonLaw ν L n n).prod (threeChunkLaw ν L n)).map
      (fun p => ((threeHeight L p.2,pairTotal D p.1+signedTotal (D false) (splitThree p.2).1),splitThree p.2)) := by
  rw [experimentLaw,← windowCommonLaw_marked ν L hL he D n n,signedChunkLaw,
    Measure.map_prod_map _ _ (measurable_of_countable _) (measurable_of_countable _),
    Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  congr 1

lemma axisHeight_listTotal {d : ℕ} (e : Step d) (b : Bool) (a : TapeList (Word d))
    (ha : ∀ i, RegenerationWord (axisDirection (placedAxis e b)) (a.2 i)) :
    axisHeight e (listTotal wordEnd a) = if b then -(listHeight (placedWidth e b) a : ℤ)
      else (listHeight (placedWidth e b) a : ℤ) := by
  rw [listTotal,axisHeight_sum]
  cases b with
  | false =>
    simp only [Bool.false_eq_true,↓reduceIte,listHeight,Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact axisHeight_wordEnd e _ (ha i)
  | true =>
    simp only [↓reduceIte,listHeight,Nat.cast_sum,← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have h := axisHeight_wordEnd (oppositeStep e) _ (ha i)
    rw [axisHeight_opposite] at h
    exact neg_eq_iff_eq_neg.mp h

lemma axisHeight_pairTotal {d : ℕ} (e : Step d) (a : TwoTapeList (Word d))
    (hb : BalancedList (placedWidth e) a)
    (ha : ∀ b i, RegenerationWord (axisDirection (placedAxis e b)) ((a b).2 i)) :
    axisHeight e (pairTotal (fun _ => wordEnd) a) = 0 := by
  rw [pairTotal,axisHeight_add,axisHeight_listTotal e false _ (ha false),
    axisHeight_listTotal e true _ (ha true)]
  simp only [Bool.false_eq_true,↓reduceIte,hb true,add_neg_cancel]

lemma axisHeight_signedTotal {d : ℕ} (e : Step d) (a : ThreeChunk (Word d))
    (ha : ∀ i, RegenerationWord (axisDirection e) ((a.1 false).2 i))
    (hb : ∀ i, RegenerationWord (axisDirection e) ((a.2.1 false).2 i))
    (hc : ∀ i, RegenerationWord (axisDirection e) ((a.2.2 false).2 i)) :
    axisHeight e (signedTotal wordEnd (splitThree a).1) =
      ((threeHeight (placedWidth e) a).1+(threeHeight (placedWidth e) a).2.1+
        (threeHeight (placedWidth e) a).2.2 : ℕ) := by
  simp only [signedTotal,splitThree,axisHeight_add,axisHeight_listTotal e false _ ha,
    axisHeight_listTotal e false _ hb,axisHeight_listTotal e false _ hc,Bool.false_eq_true,↓reduceIte]
  simp only [threeHeight,chunkHeight,Nat.cast_add,add_assoc]

lemma experimentLaw_axis_support {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d)
    (hp : ∀ b, 0 < annealed μ 0 (nonBacktracking (axisDirection (placedAxis e b))))
    (he : letI : ∀ b, IsProbabilityMeasure (slabLaw μ (axisDirection (placedAxis e b))) :=
      fun b => slabLaw_probability μ _ (hp b)
      ∀ᵐ Z ∂twoTapeLaw (fun b => slabLaw μ (axisDirection (placedAxis e b))),
        ∃ H, 0 < H ∧ Z ∈ commonCut (placedWidth e) H)
    (n : ℕ) [NeZero n] :
    let : ∀ b, IsProbabilityMeasure (slabLaw μ (axisDirection (placedAxis e b))) :=
      fun b => slabLaw_probability μ _ (hp b)
    ∀ᵐ x ∂experimentLaw (fun b => slabLaw μ (axisDirection (placedAxis e b))) (placedWidth e)
      (fun _ => wordEnd) n,
      n ≤ x.1.1.1 ∧ n ≤ x.1.1.2.2 ∧
        axisHeight e x.1.2 = ((x.1.1.1+x.1.1.2.1+x.1.1.2.2 : ℕ) : ℤ) := by
  dsimp only
  let : ∀ b, IsProbabilityMeasure (slabLaw μ (axisDirection (placedAxis e b))) :=
      fun b => slabLaw_probability μ _ (hp b)
  have : Countable (Word d) := inferInstance
  have : Countable (TapeList (Word d)) := inferInstance
  have : Countable (TwoTapeList (Word d)) := inferInstance
  have : Countable (ThreeChunk (Word d)) := inferInstance
  have : Countable (ThreeLists (Word d)) := inferInstance
  let ν := fun b => slabLaw μ (axisDirection (placedAxis e b))
  have hs (b : Bool) : ∀ᵐ a ∂ν b, RegenerationWord (axisDirection (placedAxis e b)) a :=
    ae_slabLaw_regeneration μ hell _ (axisDirection_ne_zero (placedAxis e b)) (hp b)
  have hL (b : Bool) : ∀ᵐ a ∂ν b, 0 < placedWidth e b a := by
    filter_upwards [hs b] with a ha
    exact slabRecords_pos _ _ ha
  have hw (k : ℕ) := windowCommonLaw_support ν (placedWidth e) hL he _ hs k n
  rw [experimentLaw_fourWindows ν (placedWidth e) hL he,
    ae_map_iff (measurable_of_countable _).aemeasurable (Set.to_countable _).measurableSet]
  apply (Measure.ae_prod_iff_ae_ae (Set.to_countable _).measurableSet).mpr
  filter_upwards [hw n] with a ha
  change ∀ᵐ c ∂(windowCommonLaw ν (placedWidth e) n n).prod
    ((windowCommonLaw ν (placedWidth e) (7*n) n).prod (windowCommonLaw ν (placedWidth e) n n)), _
  apply (Measure.ae_prod_iff_ae_ae (Set.to_countable _).measurableSet).mpr
  filter_upwards [hw n] with b hb
  apply (Measure.ae_prod_iff_ae_ae (Set.to_countable _).measurableSet).mpr
  filter_upwards [hw (7*n)] with c hc
  filter_upwards [hw n] with f hf
  refine ⟨hb.1.2.1.trans (listCommonCount_le_height _ b),
    hf.1.2.1.trans (listCommonCount_le_height _ f),?_⟩
  rw [axisHeight_add,axisHeight_pairTotal e a ha.1.1 ha.2,zero_add]
  exact axisHeight_signedTotal e (b,c,f) (hb.2 false) (hc.2 false) (hf.2 false)

lemma experiment_height_moment {α G : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [AddCommGroup G] [Countable G] [MeasurableSpace G]
    [MeasurableSingletonClass G] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (hi : Integrable (fun Z => (firstCommonWidth L Z : ℝ)) (twoTapeLaw ν))
    (D : Bool → α → G) (n : ℕ) [NeZero n] :
    Integrable (fun x => ((x.1.1.1+x.1.1.2.1+x.1.1.2.2 : ℕ) : ℝ)) (experimentLaw ν L D n) ∧
      (∫ x, ((x.1.1.1+x.1.1.2.1+x.1.1.2.2 : ℕ) : ℝ) ∂experimentLaw ν L D n) ≤
        12*n*(∫ Z, (firstCommonWidth L Z : ℝ) ∂twoTapeLaw ν) := by
  have h0 := windowCommonLaw_height_integrable ν L hL he hi n n
  have h1 := windowCommonLaw_height_integrable ν L hL he hi (7*n) n
  have hv : Integrable (fun a : ThreeChunk α =>
      (chunkHeight L a.1 : ℝ)+(chunkHeight L a.2.1 : ℝ)+(chunkHeight L a.2.2 : ℝ))
      (threeChunkLaw ν L n) :=
    ((h0.comp_fst _).add ((h1.comp_fst _).comp_snd _)).add ((h0.comp_snd _).comp_snd _)
  rw [experimentLaw_fourWindows ν L hL he]
  constructor
  · rw [integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
      (measurable_of_countable _).aemeasurable]
    simpa only [Function.comp_def,threeHeight,Nat.cast_add] using hv.comp_snd (windowCommonLaw ν L n n)
  · rw [integral_map (measurable_of_countable _).aemeasurable
      (measurable_of_countable _).aestronglyMeasurable]
    simp only [threeHeight,Nat.cast_add]
    rw [integral_prod _ (hv.comp_snd _)]
    simp only [integral_const,probReal_univ,one_smul]
    have hs : (∫ a : ThreeChunk α, (chunkHeight L a.1 : ℝ)+(chunkHeight L a.2.1 : ℝ)+(chunkHeight L a.2.2 : ℝ) ∂threeChunkLaw ν L n) =
        (∫ a : ThreeChunk α, (chunkHeight L a.1 : ℝ) ∂threeChunkLaw ν L n) +
        (∫ a : ThreeChunk α, (chunkHeight L a.2.1 : ℝ) ∂threeChunkLaw ν L n) +
        (∫ a : ThreeChunk α, (chunkHeight L a.2.2 : ℝ) ∂threeChunkLaw ν L n) := by
      calc
        _ = (∫ a : ThreeChunk α, (chunkHeight L a.1 : ℝ)+(chunkHeight L a.2.1 : ℝ) ∂threeChunkLaw ν L n) + _ :=
          integral_add ((h0.comp_fst _).add ((h1.comp_fst _).comp_snd _)) ((h0.comp_snd _).comp_snd _)
        _ = _ := congrArg (fun t : ℝ => t+(∫ a : ThreeChunk α, (chunkHeight L a.2.2 : ℝ) ∂threeChunkLaw ν L n))
          (integral_add (h0.comp_fst _) ((h1.comp_fst _).comp_snd _))
    rw [hs]
    simp only [threeChunkLaw]
    rw [integral_prod _ (h0.comp_fst _),integral_prod _ ((h1.comp_fst _).comp_snd _),
      integral_prod _ ((h0.comp_snd _).comp_snd _)]
    simp only [integral_const,probReal_univ,one_smul]
    rw [integral_prod _ (h1.comp_fst _),integral_prod _ (h0.comp_snd _)]
    simp only [integral_const,probReal_univ,one_smul]
    have hm0 := windowCommonLaw_height_mean ν L hL he hi n n
    have hm1 := windowCommonLaw_height_mean ν L hL he hi (7*n) n
    push_cast at hm0 hm1
    linarith

lemma axis_renewal_tail_bound_ennreal {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d)
    (hp : 0 < annealed μ 0 (nonBacktracking (axisDirection e))) {n N : ℕ} (hnN : n ≤ N) :
    axisReachProb μ e n-axisReachProb μ e N ≤ (N : ℝ≥0∞)*axisWidthTail μ e n := by
  have := slabLaw_probability μ (axisDirection e) hp
  apply (ENNReal.toReal_le_toReal (lt_of_le_of_lt tsub_le_self (measure_lt_top _ _)).ne
    (ENNReal.mul_ne_top (by simp) (measure_ne_top _ _))).mp
  change (axisReachProb μ e n-axisReachProb μ e N).toReal ≤ ((N : ℝ≥0∞)*axisWidthTail μ e n).toReal
  rw [ENNReal.toReal_sub_of_le (axisReachProb_antitone μ e hnN) (measure_ne_top _ _),
    ENNReal.toReal_mul,ENNReal.toReal_natCast]
  refine (axis_renewal_tail_bound μ hell e hp hnN).2.trans ?_
  exact mul_le_mul_of_nonneg_right (sub_le_self _ (Nat.cast_nonneg _)) ENNReal.toReal_nonneg

def experimentContact {d : ℕ} (e : Step d) :
    Set (((ℕ × (ℕ × ℕ)) × Site d) × (ThreeLists (Word d) × ThreeLists (Word d))) :=
  {x | x.2 ∈ middleContact (x.1.2-stepVector e)}

lemma experimentReference_contact_bound {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (e : Step d)
    (hp : ∀ b, 0 < annealed μ 0 (nonBacktracking (axisDirection (placedAxis e b))))
    (he : letI : ∀ b, IsProbabilityMeasure (slabLaw μ (axisDirection (placedAxis e b))) :=
      fun b => slabLaw_probability μ _ (hp b)
      ∀ᵐ Z ∂twoTapeLaw (fun b => slabLaw μ (axisDirection (placedAxis e b))),
      ∃ H, 0 < H ∧ Z ∈ commonCut (placedWidth e) H)
    (hi : letI : ∀ b, IsProbabilityMeasure (slabLaw μ (axisDirection (placedAxis e b))) :=
      fun b => slabLaw_probability μ _ (hp b)
      Integrable (fun Z => (firstCommonWidth (placedWidth e) Z : ℝ))
      (twoTapeLaw (fun b => slabLaw μ (axisDirection (placedAxis e b)))))
    (n : ℕ) [NeZero n] :
    letI : ∀ b, IsProbabilityMeasure (slabLaw μ (axisDirection (placedAxis e b))) :=
      fun b => slabLaw_probability μ _ (hp b)
    experimentReference (fun b => slabLaw μ (axisDirection (placedAxis e b))) (placedWidth e)
      (fun _ => wordEnd) n (experimentContact e) ≤
      ((annealed μ 0 (nonBacktracking (axisDirection e)))⁻¹)^2 *
      ((annealed μ 0 (nonBacktracking (axisDirection (oppositeStep e))))⁻¹)^2 * 2 *
      ENNReal.ofReal (12*n*(∫ Z, (firstCommonWidth (placedWidth e) Z : ℝ)
        ∂twoTapeLaw (fun b => slabLaw μ (axisDirection (placedAxis e b))))) *
      (axisWidthTail μ e n+axisWidthTail μ (oppositeStep e) n) := by
  let : ∀ b, IsProbabilityMeasure (slabLaw μ (axisDirection (placedAxis e b))) :=
    fun b => slabLaw_probability μ _ (hp b)
  have : Countable (Word d) := inferInstance
  have : Countable (TapeList (Word d)) := inferInstance
  have : Countable (ThreeLists (Word d)) := inferInstance
  let ν := fun b => slabLaw μ (axisDirection (placedAxis e b))
  let P := experimentLaw ν (placedWidth e) (fun _ => wordEnd) n
  let C : ℝ≥0∞ := ((annealed μ 0 (nonBacktracking (axisDirection e)))⁻¹)^2 *
      ((annealed μ 0 (nonBacktracking (axisDirection (oppositeStep e))))⁻¹)^2 * 2
  let F := axisWidthTail μ e n+axisWidthTail μ (oppositeStep e) n
  have hL (b : Bool) : ∀ᵐ a ∂ν b, 0 < placedWidth e b a := by
    filter_upwards [ae_slabLaw_regeneration μ hell _ (axisDirection_ne_zero _) (hp b)] with a ha
    exact slabRecords_pos _ _ ha
  have hu (b : Bool) (H : ℕ) : Measure.infinitePi (fun _ : ℕ => ν b)
      (renewalCut (placedWidth e b) H) ≠ 0 := by
    rw [show Measure.infinitePi (fun _ : ℕ => ν b) (renewalCut (placedWidth e b) H) =
      axisReachProb μ (placedAxis e b) H from axis_tapeCut_mass μ hell _ (hp b) H]
    exact ne_of_gt ((hp b).trans_le (axisReachProb_lower μ hell _ _))
  let : IsMarkovKernel (signedThreeKernel (ν false) (placedWidth e false)) :=
    signedThreeKernel_markov _ _ (hu false)
  let : IsMarkovKernel (signedThreeKernel (ν true) (placedWidth e true)) :=
    signedThreeKernel_markov _ _ (hu true)
  have hs : ∀ᵐ x ∂P.fst, n ≤ x.1.1 ∧ n ≤ x.1.2.2 ∧
      axisHeight e x.2 = ((x.1.1+x.1.2.1+x.1.2.2 : ℕ) : ℤ) := by
    rw [Measure.fst,ae_map_iff measurable_fst.aemeasurable (Set.to_countable _).measurableSet]
    exact experimentLaw_axis_support μ hell e hp he n
  have hm := experiment_height_moment ν (placedWidth e) hL he hi (fun _ => wordEnd) n
  have hm' : Integrable (fun x : (ℕ × (ℕ × ℕ)) × Site d =>
      ((x.1.1+x.1.2.1+x.1.2.2 : ℕ) : ℝ)) P.fst := by
    rw [Measure.fst,integrable_map_measure (measurable_of_countable _).aestronglyMeasurable measurable_fst.aemeasurable]
    exact hm.1
  have hmean : (∫⁻ x : (ℕ × (ℕ × ℕ)) × Site d,
      (x.1.1+x.1.2.1+x.1.2.2 : ℝ≥0∞) ∂P.fst) ≤
      ENNReal.ofReal (12*n*(∫ Z, (firstCommonWidth (placedWidth e) Z : ℝ) ∂twoTapeLaw ν)) := by
    have heq (x : (ℕ × (ℕ × ℕ)) × Site d) :
        (x.1.1+x.1.2.1+x.1.2.2 : ℝ≥0∞) = ENNReal.ofReal ((x.1.1+x.1.2.1+x.1.2.2 : ℕ) : ℝ) := by
      norm_cast
    simp_rw [heq]
    rw [← ofReal_integral_eq_lintegral_ofReal hm' (Filter.Eventually.of_forall (by intro x; positivity)),
      Measure.fst,integral_map measurable_fst.aemeasurable (measurable_of_countable _).aestronglyMeasurable]
    exact ENNReal.ofReal_le_ofReal hm.2
  unfold experimentReference
  rw [Measure.compProd_apply (Set.to_countable _).measurableSet]
  change (∫⁻ x, _ ∂P.fst) ≤ _
  calc
    _ ≤ ∫⁻ x : (ℕ × (ℕ × ℕ)) × Site d, C*(x.1.1+x.1.2.1+x.1.2.2 : ℝ≥0∞)*F ∂P.fst := by
      apply lintegral_mono_ae
      filter_upwards [hs] with x hx
      have hz : axisHeight e (x.2-stepVector e) = ((x.1.1+x.1.2.1+x.1.2.2 : ℕ) : ℤ)-1 := by
        rw [sub_eq_add_neg,axisHeight_add,axisHeight_neg,axisHeight_step_self,hx.2.2]; rfl
      have hh := four_bridge_contact_le μ hell e (hp false) (hp true) x.1 (x.2-stepVector e) n hx.1 hx.2.1 hz
      rw [Kernel.comap_apply,Kernel.prod_apply]
      change ((signedThreeKernel (ν false) (placedWidth e false) x.1).prod
        (signedThreeKernel (ν true) (placedWidth e true) x.1)) (middleContact (x.2-stepVector e)) ≤ _
      refine hh.trans ?_
      have hp' := axis_renewal_tail_bound_ennreal μ hell e (hp false)
        (show n ≤ x.1.1+x.1.2.1+x.1.2.2 by omega)
      have hm' := axis_renewal_tail_bound_ennreal μ hell (oppositeStep e) (hp true)
        (show n ≤ x.1.1+x.1.2.1+x.1.2.2 by omega)
      calc
        _ ≤ _ * _ * (2*((x.1.1+x.1.2.1+x.1.2.2 : ℝ≥0∞)*axisWidthTail μ e n+
            (x.1.1+x.1.2.1+x.1.2.2 : ℝ≥0∞)*axisWidthTail μ (oppositeStep e) n)) := by
              gcongr
              · simpa only [Nat.cast_add] using hp'
              · simpa only [Nat.cast_add] using hm'
        _ = _ := by dsimp only [C,F];ring
    _ = C*(∫⁻ x : (ℕ × (ℕ × ℕ)) × Site d, (x.1.1+x.1.2.1+x.1.2.2 : ℝ≥0∞) ∂P.fst)*F := by
      rw [lintegral_mul_const _ (measurable_of_countable _),lintegral_const_mul _ (measurable_of_countable _)]
    _ ≤ _ := by
      change C*_ *F ≤ C*_ *F
      exact mul_le_mul_left (mul_le_mul_right hmean C) F

lemma axisBridgeWords_prefixFree {d : ℕ} (e : Step d) (k : ℕ) :
    PrefixFreeWords {a : Word d | AxisBridgeWord e k a} := by
  intro a b hab
  exact (firstHitWords_prefixFree (axisUpper e k))
    (i := ⟨a,a.property.firstHit⟩) (j := ⟨b,b.property.firstHit⟩)
    (fun h => hab (Subtype.ext (congrArg (fun x : {a | firstHitWord (axisUpper e k) a} => x.val) h)))

lemma prefix_contact_total_bound {d ι : ℕ} [NeZero ι]
    (μ : Measure (Row d)) [IsProbabilityMeasure μ] (hell : StrictEllipticity μ)
    (e : Step d) (k r N m : ℕ) (hrN : r ≤ N)
    (E : Word d → Fin ι → Set (Path d)) (hE : ∀ a q, MeasurableSet (E a q))
    (hdis : ∀ a, Pairwise (fun i j => Disjoint (E a i) (E a j)))
    (start : Word d → Fin ι → Site d)
    (hΔ : axisReachProb μ e r-axisReachProb μ e N ≤ ENNReal.ofReal ((1/2 : ℝ)^m)) :
    (∑' a : {a : Word d | AxisBridgeWord e k a}, ∑ q,
      ∑' b : {b | upperContactWord 0 (axisUpper e r) (axisLower e 0 ∪ axisUpper e N) b},
        annealed μ 0 (wordCylinder a ∩ (shiftPath (-wordEnd a) ∘ tailPath a.val.1) ⁻¹'
          (E a q ∩ wordCylinder b)) *
        annealed μ (start a q) (avoids (axisUpper e N) ∩ contactAvoid b)) ≤
      ENNReal.ofReal ((24 / posteriorExponent)*Real.log (ι+1)*(m+1)^2*(1/2 : ℝ)^m) := by
  let C := ENNReal.ofReal ((24 / posteriorExponent)*Real.log (ι+1)*(m+1)^2*(1/2 : ℝ)^m)
  calc
    _ ≤ ∑' a : {a : Word d | AxisBridgeWord e k a}, annealed μ 0 (wordCylinder a)*C := by
      apply ENNReal.tsum_le_tsum
      intro a
      by_cases ha : annealed μ 0 (wordCylinder a) = 0
      · have hz (q : Fin ι) (b : {b | upperContactWord 0 (axisUpper e r) (axisLower e 0 ∪ axisUpper e N) b}) :
          annealed μ 0 (wordCylinder a ∩ (shiftPath (-wordEnd a) ∘ tailPath a.val.1) ⁻¹'
            (E a q ∩ wordCylinder b)) = 0 := measure_mono_null Set.inter_subset_left ha
        simp only [hz,zero_mul,tsum_zero,Finset.sum_const_zero,ha,le_refl]
      · exact posterior_old_prefix_weighted_bound μ hell e a ha
          (fun i hi => (a.property.2 i hi).2.trans_eq a.property.1.symm)
          (E a) (hE a) (hdis a) (start a) r N m hrN hΔ
    _ = annealed μ 0 (⋃ a : {a : Word d | AxisBridgeWord e k a}, wordCylinder a)*C := by
      rw [ENNReal.tsum_mul_right,measure_iUnion (axisBridgeWords_prefixFree e k)
        (fun _ => measurableSet_pathCylinder _ _)]
    _ ≤ C := by simpa only [one_mul] using mul_le_mul_left (prob_le_one (μ := annealed μ 0)) C

lemma conditioned_negative_shift {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (e : Step d) (z : Site d) (N : ℕ) (hz : axisHeight e z = (N : ℤ)-1)
    (E : Set (Path d)) (hE : MeasurableSet E) :
    conditioned μ (axisDirection (oppositeStep e)) (shiftPath z ⁻¹' E) =
      (annealed μ 0 (nonBacktracking (axisDirection (oppositeStep e))))⁻¹ *
        annealed μ z (avoids (axisUpper e N) ∩ E) := by
  have hb : shiftPath z ⁻¹' avoids (axisUpper e N) = nonBacktracking (axisDirection (oppositeStep e)) := by
    ext X
    change (∀ j, ¬(N : ℤ) ≤ axisHeight e (X j+z)) ↔
      ∀ j, 0 ≤ height (axisDirection (oppositeStep e)) (X j)
    simp only [axisHeight_add,hz,height_axisDirection,axisHeight_opposite]
    constructor
    · intro h j
      have hj := h j
      have hx : axisHeight e (X j) ≤ 0 := by omega
      exact_mod_cast (neg_nonneg.mpr hx)
    · intro h j
      have hx : -(axisHeight e (X j)) ≥ 0 := by exact_mod_cast h j
      omega
  rw [conditioned,cond_apply (measurableSet_nonBacktracking _)]
  have hh := congrArg (fun M : Measure (Path d) => M (avoids (axisUpper e N) ∩ E)) (annealed_shift μ 0 z)
  rw [zero_add,Measure.map_apply (measurable_shiftPath z) ((measurableSet_avoids _).inter hE),
    Set.preimage_inter,hb] at hh
  rw [hh]

end DirectionalZeroOne

end OAI

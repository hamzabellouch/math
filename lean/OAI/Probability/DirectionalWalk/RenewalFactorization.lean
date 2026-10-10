import OAI.Probability.DirectionalWalk.DyadicBounds

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

lemma measurable_dependent_subtype_tsum {Ω α : Type*} [MeasurableSpace Ω] [Countable α]
    (A : Ω → Set α) (hA : ∀ a, MeasurableSet {ω | a ∈ A ω})
    (f : α → Ω → ℝ≥0∞) (hf : ∀ a, Measurable (f a)) :
    Measurable (fun ω => ∑' a : A ω, f a ω) := by
  classical
  have he : (fun ω => ∑' a : A ω, f a ω) =
      fun ω => ∑' a : α, if a ∈ A ω then f a ω else 0 := by
    funext ω
    simpa only [Set.indicator_apply] using tsum_subtype (A ω) (fun a => f a ω)
  rw [he]
  exact Measurable.tsum (fun a => Measurable.ite (hA a) (hf a) measurable_const)

lemma measurable_contactBinMass {d ι : ℕ} (P : Measure (Path d))
    (E : Fin ι → Set (Path d)) (e : Step d) (z : Site d) (start : Fin ι → Site d)
    (r N : ℕ) (a : ℝ≥0∞) :
    Measurable (fun ω => ∑ q, ∑' b : contactBinWords e z r N a ω,
      ENNReal.ofReal (wordPosterior P E q b) *
        (quenchedKernel d (ω,z) (wordCylinder b) *
          quenchedKernel d (ω,start q) (avoids (axisUpper e N) ∩ contactAvoid b))) := by
  apply Finset.measurable_sum
  intro q _
  refine measurable_dependent_subtype_tsum (contactBinWords e z r N a) ?_
    (fun b ω => ENNReal.ofReal (wordPosterior P E q b) *
      (quenchedKernel d (ω,z) (wordCylinder b) *
        quenchedKernel d (ω,start q) (avoids (axisUpper e N) ∩ contactAvoid b))) ?_
  · intro b
    exact (MeasurableSet.const _).inter (measurableSet_returnBin e 0 N a (wordEnd b))
  · intro b
    apply measurable_const.mul
    exact (((quenchedKernel d).measurable_coe (measurableSet_pathCylinder _ _)).comp
      (measurable_id.prodMk measurable_const)).mul
      (((quenchedKernel d).measurable_coe ((measurableSet_avoids _).inter
        (measurableSet_contactAvoid b))).comp (measurable_id.prodMk measurable_const))

lemma measurable_quenched_apply {d : ℕ} (z : Site d) (E : Set (Path d)) (hE : MeasurableSet E) :
    Measurable (fun ω => quenchedKernel d (ω,z) E) :=
  ((quenchedKernel d).measurable_coe hE).comp (measurable_id.prodMk measurable_const)

lemma measurable_kernel_weighted_sum {Ω ξ β α : Type*} [MeasurableSpace Ω] [MeasurableSpace ξ]
    [MeasurableSpace β] [Countable α] (κ : Kernel (Ω × ξ) β) (z y : ξ)
    (A B : α → Set β) (hA : ∀ a, MeasurableSet (A a)) (hB : ∀ a, MeasurableSet (B a)) (f : α → ℝ≥0∞) :
    Measurable (fun ω => ∑' a, f a * (κ (ω,z) (A a) * κ (ω,y) (B a))) := by
  apply Measurable.tsum
  intro a
  exact measurable_const.mul (((κ.measurable_coe (hA a)).comp (measurable_id.prodMk measurable_const)).mul
    ((κ.measurable_coe (hB a)).comp (measurable_id.prodMk measurable_const)))

lemma measurable_weighted_contact_tsum {d : ℕ} (A : Set (Word d)) (f : Word d → ℝ≥0∞)
    (z y : Site d) (K : Set (Site d)) :
    Measurable (fun ω => ∑' a : A, f a * (quenchedKernel d (ω,z) (wordCylinder a) *
      quenchedKernel d (ω,y) (avoids K ∩ contactAvoid a))) := by
  exact measurable_kernel_weighted_sum (quenchedKernel d) z y
    (fun a : A => wordCylinder a) (fun a : A => avoids K ∩ contactAvoid a)
    (fun a => measurableSet_pathCylinder a.val.1 (wordPath a.val))
    (fun a => (measurableSet_avoids K).inter (measurableSet_contactAvoid a.val)) (fun a => f a.val)

lemma totalPosterior_le_bins {d ι : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (P : Measure (Path d)) (E : Fin ι → Set (Path d))
    (e : Step d) (z : Site d) (start : Fin ι → Site d) (r N : ℕ) :
    (∑ q, ∑' b : {b | upperContactWord z (axisUpper e r) (axisLower e 0 ∪ axisUpper e N) b},
      ENNReal.ofReal (wordPosterior P E q b) *
        (annealed μ z (wordCylinder b) *
          annealed μ (start q) (avoids (axisUpper e N) ∩ contactAvoid b))) ≤
    ∑' j, ∫⁻ ω, ∑ q, ∑' b : contactBinWords e z r N (dyad j) ω,
      ENNReal.ofReal (wordPosterior P E q b) *
        (quenchedKernel d (ω,z) (wordCylinder b) *
          quenchedKernel d (ω,start q) (avoids (axisUpper e N) ∩ contactAvoid b)) ∂environmentLaw μ := by
  classical
  let A := {b | upperContactWord z (axisUpper e r) (axisLower e 0 ∪ axisUpper e N) b}
  have he (q : Fin ι) := weighted_contact_transfer μ z (start q) A (fun _ hb => hb.1)
    (fun b => ENNReal.ofReal (wordPosterior P E q b)) (measurableSet_avoids (axisUpper e N))
  simp only [Measure.prod_prod] at he
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun q _ => he q)
  rw [hsum]
  have hme (q : Fin ι) : Measurable (fun ω => ∑' a : A,
      ENNReal.ofReal (wordPosterior P E q a) *
        (quenchedKernel d (ω,z) (wordCylinder a) *
          quenchedKernel d (ω,start q) (avoids (axisUpper e N) ∩ contactAvoid a))) :=
    measurable_weighted_contact_tsum A (fun a => ENNReal.ofReal (wordPosterior P E q a)) z (start q) (axisUpper e N)
  rw [← lintegral_finsetSum _ (fun q _ => hme q)]
  rw [← lintegral_tsum (fun j => (measurable_contactBinMass P E e z start r N (dyad j)).aemeasurable)]
  apply lintegral_mono_ae
  filter_upwards [all_rows_strictly_positive μ hell] with ω hω
  calc
    _ ≤ ∑ q, ∑' j, ∑' b : contactBinWords e z r N (dyad j) ω,
        ENNReal.ofReal (wordPosterior P E q b) *
          (quenchedKernel d (ω,z) (wordCylinder b) *
            quenchedKernel d (ω,start q) (avoids (axisUpper e N) ∩ contactAvoid b)) := by
      apply Finset.sum_le_sum
      intro q _
      refine tsum_subtype_cover A (fun j => contactBinWords e z r N (dyad j) ω) ?_
        (fun b => ENNReal.ofReal (wordPosterior P E q b) *
          (quenchedKernel d (ω,z) (wordCylinder b) *
            quenchedKernel d (ω,start q) (avoids (axisUpper e N) ∩ contactAvoid b)))
      intro b hb
      obtain ⟨j,hj⟩ := return_bins_cover e 0 N ω hω (wordEnd b) (by
        have hh := hb.2.2 b.1 le_rfl
        simp only [Set.mem_union,not_or,axisLower,axisUpper,Set.mem_ofPred_eq,not_lt,not_le] at hh
        exact hh)
      exact Set.mem_iUnion.mpr ⟨j,hb,hj⟩
    _ = _ := by
      simpa only [tsum_fintype] using (ENNReal.tsum_comm (f := fun q j => ∑' b : contactBinWords e z r N (dyad j) ω,
        ENNReal.ofReal (wordPosterior P E q b) *
          (quenchedKernel d (ω,z) (wordCylinder b) *
            quenchedKernel d (ω,start q) (avoids (axisUpper e N) ∩ contactAvoid b))))

lemma posterior_contact_raw_bound {d ι : ℕ} [NeZero ι]
    (μ : Measure (Row d)) [IsProbabilityMeasure μ] (hell : StrictEllipticity μ)
    (P : Measure (Path d)) [IsProbabilityMeasure P]
    (E : Fin ι → Set (Path d)) (hE : ∀ q, MeasurableSet (E q))
    (hdis : Pairwise (fun i j => Disjoint (E i) (E j))) (e : Step d)
    (start : Fin ι → Site d) (r N m : ℕ) (hrN : r ≤ N)
    (he : P.map (firstVisitWord (axisLower e 0 ∪ axisUpper e N)) =
      (annealed μ 0).map (firstVisitWord (axisLower e 0 ∪ axisUpper e N)))
    (hΔ : axisReachProb μ e r - axisReachProb μ e N ≤ ENNReal.ofReal ((1/2 : ℝ)^m)) :
    (∑ q, ∑' b : {b | upperContactWord 0 (axisUpper e r) (axisLower e 0 ∪ axisUpper e N) b},
      ENNReal.ofReal (wordPosterior P E q b) *
        (annealed μ 0 (wordCylinder b) *
          annealed μ (start q) (avoids (axisUpper e N) ∩ contactAvoid b))) ≤
      ENNReal.ofReal ((24 / posteriorExponent)*Real.log (ι+1)*(m+1)^2*(1/2 : ℝ)^m) := by
  let K := axisLower e 0 ∪ axisUpper e N
  let V := fun j => {ξ : Environment d × Path d | ξ.2 ∈ visitAfter (axisUpper e r)
    (returnAtLeast e 0 N (dyad j) ξ.1) K}
  let f := fun X : Path d => wordEndpointMax P E (firstVisitWord K X)
  let ν := freshJoint μ 0
  let c := posteriorExponent/Real.log (ι+1)
  have hc : 0 < c := div_pos posteriorExponent_pos
    (Real.log_pos (by exact_mod_cast (show 1 < ι+1 by have := NeZero.pos ι;omega)))
  have hm : Measurable f := (measurable_of_countable (wordEndpointMax P E)).comp (measurable_firstVisitWord K)
  have hmf : Measurable (fun ξ : Environment d × Path d => f ξ.2) := hm.comp measurable_snd
  have hb (X : Path d) : 0 ≤ f X ∧ f X ≤ ι := wordEndpointMax_bounds P E hE hdis _
  have hi : Integrable (fun ξ : Environment d × Path d => f ξ.2) ν :=
    (integrable_const (ι : ℝ)).mono' hmf.aestronglyMeasurable (by
      filter_upwards [] with ξ
      rw [Real.norm_eq_abs,abs_of_nonneg (hb ξ.2).1]
      exact (hb ξ.2).2)
  have hie := integrable_exp_of_bound ν (fun ξ => f ξ.2) hmf ι c (fun ξ => (hb ξ.2).2) hc.le
  have hex : (∫ ξ, Real.exp (c*f ξ.2) ∂ν) ≤ 12 := by
    have hπ := freshJoint_path_marginal μ 0
    have hi' : (∫ ξ, Real.exp (c*f ξ.2) ∂ν) = ∫ X, Real.exp (c*f X) ∂annealed μ 0 := by
      rw [← hπ.map_eq]
      exact (integral_map_of_stronglyMeasurable hπ.measurable (hm.const_mul c).exp.stronglyMeasurable).symm
    rw [hi']
    exact stoppedEndpointMax_exponential P (annealed μ 0) E hE hdis K he
  have hv (j : ℕ) : dyad j * ν (V j) ≤ ENNReal.ofReal ((1/2 : ℝ)^m) :=
    (freshJoint_return_visit_bound μ hell e hrN (dyad j)).trans hΔ
  have hn := dyadic_event_weight_bound ν (fun ξ => f ξ.2) hi (fun ξ => (hb ξ.2).1)
    c hc hie hex V m hv
  have hs : 24/c = (24/posteriorExponent)*Real.log (ι+1) := by dsimp [c];field_simp
  rw [hs] at hn
  apply (totalPosterior_le_bins μ hell P E e 0 start r N).trans
  apply le_trans (ENNReal.tsum_le_tsum (fun j => posterior_contact_bin_joint μ hell P E hE hdis e 0 start r N
    (dyad j) ENNReal.ofReal_ne_top)) hn

noncomputable def commonCount {α : Type*} (L : Bool → α → ℕ) (H : ℕ) (Z : TwoTape α) : ℕ := by
  classical
  exact ∑ j ∈ Finset.range H, if Z ∈ commonCut L (j+1) then 1 else 0

noncomputable def listCommonCount {α : Type*} (L : Bool → α → ℕ) (a : TwoTapeList α) : ℕ := by
  classical
  exact ∑ j ∈ Finset.range (listHeight (L false) (a false)),
    if ∀ b, listHasCut (L b) (a b) (j+1) then 1 else 0

lemma commonCount_cutList {α : Type*} (L : Bool → α → ℕ) (H : ℕ) (Z : TwoTape α)
    (hZ : ∀ b i, 0 < L b (Z (b,i))) (hc : Z ∈ commonCut L H) :
    listCommonCount L (commonCutList L H Z) = commonCount L H Z := by
  classical
  have hh := ((commonCutList_atom_iff L H Z hZ (commonCutList L H Z)).mp ⟨hc,rfl⟩).1 false
  unfold listCommonCount commonCount
  rw [hh]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [← commonCut_iff_listHasCut L Z hZ H (j+1) hc (by have := Finset.mem_range.mp hj;omega)]

lemma commonCount_zero {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α) :
    commonCount L 0 Z = 0 := by simp [commonCount]

lemma commonCount_succ {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α) (H : ℕ) :
    commonCount L (H+1) Z = commonCount L H Z + (by classical exact if Z ∈ commonCut L (H+1) then 1 else 0) := by
  classical
  exact Finset.sum_range_succ _ _

lemma commonCount_mono {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α) :
    Monotone (fun H => commonCount L H Z) := by
  classical
  intro H J hHJ
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hHJ) (fun _ _ _ => Nat.zero_le _)

lemma commonCount_lt_at_cut {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α)
    {H J : ℕ} (hHJ : H < J) (hJ : Z ∈ commonCut L J) :
    commonCount L H Z < commonCount L J Z := by
  classical
  have hm : commonCount L H Z ≤ commonCount L (J-1) Z := commonCount_mono L Z (by omega)
  have hh : commonCount L J Z = commonCount L (J-1) Z + 1 := by
    have hs := commonCount_succ L Z (J-1)
    simpa only [show J-1+1=J by omega,ite_eq_left hJ] using hs
  omega

lemma commonCut_count_injective {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α)
    {H J : ℕ} (hH : Z ∈ commonCut L H) (hJ : Z ∈ commonCut L J)
    (he : commonCount L H Z = commonCount L J Z) : H = J := by
  rcases lt_trichotomy H J with h | h | h
  · exact False.elim ((ne_of_lt (commonCount_lt_at_cut L Z h hJ)) he)
  · exact h
  · exact False.elim ((ne_of_lt (commonCount_lt_at_cut L Z h hH)) he.symm)

lemma commonCount_add {α : Type*} (L : Bool → α → ℕ) (H J : ℕ) (Z : TwoTape α)
    (hZ : ∀ b i, 0 < L b (Z (b,i))) (hc : Z ∈ commonCut L H) :
    commonCount L (H+J) Z = commonCount L H Z + commonCount L J (afterCommonCut L H Z) := by
  classical
  unfold commonCount
  rw [Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [Nat.add_assoc,commonCut_add_iff L H Z hZ hc (j+1)]

lemma commonCount_first {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α)
    (he : ∃ H, 0 < H ∧ Z ∈ commonCut L H) :
    commonCount L (firstCommonWidth L Z) Z = 1 := by
  classical
  obtain ⟨hpos,hcut,hmin⟩ := firstCommonWidth_spec L Z he
  have hzero : commonCount L (firstCommonWidth L Z-1) Z = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hj' := Finset.mem_range.mp hj
    exact ite_eq_right (hmin (j+1) (by omega) (by omega))
  have heq : firstCommonWidth L Z = (firstCommonWidth L Z-1)+1 := by omega
  have hs := commonCount_succ L Z (firstCommonWidth L Z-1)
  simpa only [← heq,ite_eq_left hcut,hzero,zero_add] using hs

lemma twoShift_comp {α : Type*} (n m : Bool → ℕ) (Z : TwoTape α) :
    twoShift m (twoShift n Z) = twoShift (fun b => n b + m b) Z := by
  funext i
  simp only [twoShift,Nat.add_assoc]

lemma cutListIndex_spec {α : Type*} (L : α → ℕ) (H : ℕ) (Z : ℕ → α)
    (hZ : ∀ i, 0 < L (Z i)) (hc : Z ∈ renewalCut L H) :
    tapeHeight L Z (cutListIndex L H Z) = H := by
  obtain ⟨n,hn⟩ := hc
  rw [cutListIndex_eq L H Z hZ hn,hn]

lemma afterCommonCut_add {α : Type*} (L : Bool → α → ℕ) (H J : ℕ) (Z : TwoTape α)
    (hZ : ∀ b i, 0 < L b (Z (b,i))) (hH : Z ∈ commonCut L H)
    (hJ : afterCommonCut L H Z ∈ commonCut L J) :
    afterCommonCut L (H+J) Z = afterCommonCut L J (afterCommonCut L H Z) := by
  have hie (b : Bool) : commonCutIndices L (H+J) Z b =
      commonCutIndices L H Z b + commonCutIndices L J (afterCommonCut L H Z) b := by
    apply cutListIndex_eq (L b) (H+J) _ (hZ b)
    rw [tapeHeight_add]
    have h1 : tapeHeight (L b) (fun i => Z (b,i)) (commonCutIndices L H Z b) = H := by
      exact cutListIndex_spec (L b) H _ (hZ b) (hH b)
    have h2 : tapeHeight (L b) (fun i => Z (b,commonCutIndices L H Z b+i))
        (commonCutIndices L J (afterCommonCut L H Z) b) = J := by
      exact cutListIndex_spec (L b) J _ (fun i => hZ b _) (hJ b)
    rw [h1,h2]
  unfold afterCommonCut
  rw [twoShift_comp]
  congr 1
  exact funext hie

noncomputable def commonDepth {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α) (r : ℕ) : ℕ :=
  ∑ i ∈ Finset.range r, firstCommonWidth L ((commonRestart L)^[i] Z)

lemma commonDepth_zero {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α) :
    commonDepth L Z 0 = 0 := by simp [commonDepth]

lemma commonDepth_succ {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α) (r : ℕ) :
    commonDepth L Z (r+1) = commonDepth L Z r + firstCommonWidth L ((commonRestart L)^[r] Z) := by
  exact Finset.sum_range_succ _ _

lemma commonDepth_spec {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α)
    (hZ : ∀ b i, 0 < L b (Z (b,i)))
    (he : ∀ r, ∃ H, 0 < H ∧ ((commonRestart L)^[r] Z) ∈ commonCut L H) (r : ℕ) :
    Z ∈ commonCut L (commonDepth L Z r) ∧
    afterCommonCut L (commonDepth L Z r) Z = (commonRestart L)^[r] Z ∧
    commonCount L (commonDepth L Z r) Z = r := by
  induction r with
  | zero =>
    have h0 : commonCutIndices L 0 Z = fun _ => 0 := by
      funext b
      exact cutListIndex_eq (L b) 0 _ (hZ b) rfl
    refine ⟨by rw [commonDepth_zero,commonCut_zero];trivial,?_,by rw [commonDepth_zero,commonCount_zero]⟩
    simp only [commonDepth_zero,afterCommonCut,h0,Function.iterate_zero, id_eq]
    funext i
    exact congrArg Z (by cases i;simp only [Nat.zero_add])
  | succ r ih =>
    obtain ⟨_,hc,_⟩ := firstCommonWidth_spec L ((commonRestart L)^[r] Z) (he r)
    have hc' : afterCommonCut L (commonDepth L Z r) Z ∈
        commonCut L (firstCommonWidth L ((commonRestart L)^[r] Z)) := by rw [ih.2.1];exact hc
    rw [commonDepth_succ]
    refine ⟨(commonCut_add_iff L _ Z hZ ih.1 _).mpr hc',?_,?_⟩
    · rw [afterCommonCut_add L _ _ Z hZ ih.1 hc',ih.2.1,Function.iterate_succ_apply']
      rfl
    · rw [commonCount_add L _ _ Z hZ ih.1,ih.2.1,ih.2.2,commonCount_first L _ (he r)]

lemma ae_common_iterates {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H) :
    ∀ᵐ Z ∂twoTapeLaw ν, ∀ r, ∃ H, 0 < H ∧ ((commonRestart L)^[r] Z) ∈ commonCut L H := by
  rw [ae_all_iff]
  intro r
  exact ((commonRestart_measurePreserving ν L hL he).iterate r).quasiMeasurePreserving.ae he

lemma measurable_commonDepth {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (L : Bool → α → ℕ) (r : ℕ) : Measurable (fun Z => commonDepth L Z r) := by
  exact Finset.measurable_sum _ (fun i _ => (measurable_firstCommonWidth L).comp
    ((measurable_commonRestart L).iterate i))

noncomputable def nthCommonList {α : Type*} (L : Bool → α → ℕ) (r : ℕ) (Z : TwoTape α) : TwoTapeList α :=
  commonCutList L (commonDepth L Z r) Z

lemma measurable_nthCommonList {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (L : Bool → α → ℕ) (r : ℕ) : Measurable (nthCommonList L r) := by
  have hm : Measurable (fun p : TwoTape α × ℕ => commonCutList L p.2 p.1) :=
    measurable_from_prod_countable_left (measurable_commonCutList L)
  exact hm.comp (measurable_id.prodMk (measurable_commonDepth L r))

def BalancedList {α : Type*} (L : Bool → α → ℕ) (a : TwoTapeList α) : Prop :=
  ∀ b, listHeight (L b) (a b) = listHeight (L false) (a false)

lemma nthCommonList_atom_iff {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α)
    (hZ : ∀ b i, 0 < L b (Z (b,i)))
    (he : ∀ r, ∃ H, 0 < H ∧ ((commonRestart L)^[r] Z) ∈ commonCut L H)
    (r : ℕ) (a : TwoTapeList α) :
    nthCommonList L r Z = a ↔ (BalancedList L a ∧ listCommonCount L a = r ∧ Z ∈ twoCylinder a) := by
  obtain ⟨hc,_,hr⟩ := commonDepth_spec L Z hZ he r
  constructor
  · intro ha
    have hh := (commonCutList_atom_iff L (commonDepth L Z r) Z hZ a).mp ⟨hc,ha⟩
    refine ⟨fun b => (hh.1 b).trans (hh.1 false).symm,?_,hh.2⟩
    rw [← ha]
    exact (commonCount_cutList L _ Z hZ hc).trans hr
  · rintro ⟨hb,hr',hpre⟩
    obtain ⟨hc',hh⟩ := (commonCutList_atom_iff L _ Z hZ a).mpr ⟨hb,hpre⟩
    have hn : commonDepth L Z r = listHeight (L false) (a false) := by
      apply commonCut_count_injective L Z hc hc'
      rw [hr,← commonCount_cutList L _ Z hZ hc',hh,hr']
    unfold nthCommonList
    rw [hn,hh]

noncomputable def nthCommonLaw {α : Type*} [MeasurableSpace α]
    (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (r : ℕ) : Measure (TwoTapeList α) :=
  (twoTapeLaw ν).map (nthCommonList L r)

instance nthCommonLaw_probability {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (r : ℕ) : IsProbabilityMeasure (nthCommonLaw ν L r) :=
  probabilityMeasure_map (μ := twoTapeLaw ν) (measurable_nthCommonList L r).aemeasurable

lemma nthCommonLaw_atom {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (r : ℕ) (a : TwoTapeList α) :
    nthCommonLaw ν L r {a} = (by classical exact if BalancedList L a ∧ listCommonCount L a = r
      then (∏ b : Bool, ∏ i : Fin (a b).1, ν b {(a b).2 i}) else 0) := by
  classical
  have hZ := ae_twoTape_prop ν (fun b a => 0 < L b a)
    (fun b => measurableSet_lt measurable_const (measurable_of_countable (L b))) hL
  have hiter := ae_common_iterates ν L hL he
  rw [nthCommonLaw,Measure.map_apply (measurable_nthCommonList L r) (measurableSet_singleton a)]
  by_cases ha : BalancedList L a ∧ listCommonCount L a = r
  · rw [ite_eq_left ha,← twoCylinder_mass ν a]
    apply measure_congr
    filter_upwards [hZ,hiter] with Z hZ hiter
    apply propext
    exact ⟨fun h => ((nthCommonList_atom_iff L Z hZ hiter r a).mp h).2.2,
      fun h => (nthCommonList_atom_iff L Z hZ hiter r a).mpr ⟨ha.1,ha.2,h⟩⟩
  · rw [ite_eq_right ha]
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hZ,hiter] with Z hZ hiter h
    have hh := (nthCommonList_atom_iff L Z hZ hiter r a).mp h
    exact ha ⟨hh.1,hh.2.1⟩

lemma nthCommon_suffix_factorization {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (r : ℕ) (a : TwoTapeList α) (E : Set (TwoTape α)) (hE : MeasurableSet E) :
    twoTapeLaw ν {Z | nthCommonList L r Z = a ∧ (commonRestart L)^[r] Z ∈ E} =
      nthCommonLaw ν L r {a} * twoTapeLaw ν E := by
  classical
  have hZ := ae_twoTape_prop ν (fun b a => 0 < L b a)
    (fun b => measurableSet_lt measurable_const (measurable_of_countable (L b))) hL
  have hiter := ae_common_iterates ν L hL he
  by_cases ha : BalancedList L a ∧ listCommonCount L a = r
  · rw [nthCommonLaw_atom ν L hL he r a,ite_eq_left ha]
    rw [← twoCylinder_suffix_factorization ν a E hE]
    apply measure_congr
    filter_upwards [hZ,hiter] with Z hZ hiter
    have hs (hh : nthCommonList L r Z = a) :
        (commonRestart L)^[r] Z = twoShift (fun b => (a b).1) Z := by
      rw [← (commonDepth_spec L Z hZ hiter r).2.1]
      unfold afterCommonCut
      rw [commonCutIndices_eq_lengths L _ Z a hh]
    apply propext
    constructor
    · rintro ⟨hb,hE⟩
      exact ⟨((nthCommonList_atom_iff L Z hZ hiter r a).mp hb).2.2,by rwa [← hs hb]⟩
    · rintro ⟨hb,hE⟩
      have hh := (nthCommonList_atom_iff L Z hZ hiter r a).mpr ⟨ha.1,ha.2,hb⟩
      exact ⟨hh,by rwa [hs hh]⟩
  · rw [nthCommonLaw_atom ν L hL he r a,ite_eq_right ha,zero_mul]
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hZ,hiter] with Z hZ hiter h
    have hh := (nthCommonList_atom_iff L Z hZ hiter r a).mp h.1
    exact ha ⟨hh.1,hh.2.1⟩

noncomputable def windowCommonLaw {α : Type*} [MeasurableSpace α]
    (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (k n : ℕ) : Measure (TwoTapeList α) :=
  (n : ℝ≥0∞)⁻¹ • ∑ i : Fin n, nthCommonLaw ν L (k+i)

instance windowCommonLaw_probability {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (k n : ℕ) [NeZero n] : IsProbabilityMeasure (windowCommonLaw ν L k n) := by
  constructor
  simp only [windowCommonLaw,Measure.smul_apply,smul_eq_mul,Measure.finsetSum_apply,measure_univ,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast NeZero.ne n) (by finiteness)

noncomputable def twoListWeight {α : Type*} [MeasurableSpace α]
    (ν : Bool → Measure α) (a : TwoTapeList α) : ℝ≥0∞ :=
  ∏ b : Bool, ∏ i : Fin (a b).1, ν b {(a b).2 i}

end DirectionalZeroOne

end OAI

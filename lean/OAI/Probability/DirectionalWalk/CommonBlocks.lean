import OAI.Probability.DirectionalWalk.TwoTapes

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

noncomputable def firstCommonWidth {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α) : ℕ := by
  classical
  exact if h : ∃ H, 0 < H ∧ Z ∈ commonCut L H then Nat.find h else 0

lemma firstCommonWidth_spec {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α)
    (h : ∃ H, 0 < H ∧ Z ∈ commonCut L H) :
    0 < firstCommonWidth L Z ∧ Z ∈ commonCut L (firstCommonWidth L Z) ∧
      ∀ j < firstCommonWidth L Z, 0 < j → Z ∉ commonCut L j := by
  classical
  simp only [firstCommonWidth,dite_eq_left h]
  exact ⟨(Nat.find_spec h).1,(Nat.find_spec h).2,fun j hj hjpos hc => Nat.find_min h hj ⟨hjpos,hc⟩⟩

lemma firstCommonWidth_zero_iff {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α) :
    firstCommonWidth L Z = 0 ↔ ¬∃ H, 0 < H ∧ Z ∈ commonCut L H := by
  constructor
  · intro hz h
    have hh := (firstCommonWidth_spec L Z h).1
    omega
  · intro h; simp [firstCommonWidth,h]

lemma firstCommonWidth_eq_pos_iff {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α)
    {H : ℕ} (hH : 0 < H) :
    firstCommonWidth L Z = H ↔ Z ∈ commonCut L H ∧ Z ∈ noCommonThrough L (H-1) := by
  classical
  constructor
  · intro he
    have hex : ∃ n, 0 < n ∧ Z ∈ commonCut L n := by
      by_contra hn
      have := (firstCommonWidth_zero_iff L Z).mpr hn
      omega
    have hh := firstCommonWidth_spec L Z hex
    rw [he] at hh
    exact ⟨hh.2.1,fun j hj hjH => hh.2.2 j (by omega) hj⟩
  · rintro ⟨hc,hl⟩
    have he : ∃ n, 0 < n ∧ Z ∈ commonCut L n := ⟨H,hH,hc⟩
    simp only [firstCommonWidth,dite_eq_left he]
    apply (Nat.find_eq_iff he).mpr
    exact ⟨⟨hH,hc⟩,fun j hj hm => hl j hm.1 (by omega) hm.2⟩

lemma measurable_firstCommonWidth {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (L : Bool → α → ℕ) : Measurable (firstCommonWidth L) := by
  apply measurable_to_countable'
  intro H
  by_cases hH : H = 0
  · subst H
    have he : firstCommonWidth L ⁻¹' {0} = (⋃ n, ⋃ (_ : 0 < n), commonCut L n)ᶜ := by
      ext Z
      simp only [Set.mem_preimage,Set.mem_singleton_iff,firstCommonWidth_zero_iff,
        Set.mem_compl_iff,Set.mem_iUnion,not_exists,not_and]
    rw [he]
    exact (MeasurableSet.iUnion (fun n => MeasurableSet.iUnion (fun _ => measurableSet_commonCut L n))).compl
  · have he : firstCommonWidth L ⁻¹' {H} = commonCut L H ∩ noCommonThrough L (H-1) := by
      ext Z;exact firstCommonWidth_eq_pos_iff L Z (Nat.pos_of_ne_zero hH)
    rw [he]
    exact (measurableSet_commonCut L H).inter (measurableSet_noCommonThrough L _)

lemma firstCommonWidth_tail_subset {α : Type*} (L : Bool → α → ℕ) (N : ℕ) :
    {Z | N < firstCommonWidth L Z} ⊆ noCommonThrough L N := by
  intro Z hZ j hj hjN hc
  have he := firstCommonWidth_spec L Z ⟨j,hj,hc⟩
  exact he.2.2 j (lt_of_le_of_lt hjN hZ) hj hc

lemma ae_exists_commonCut {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a) (c : ℝ≥0∞) (hcpos : c ≠ 0)
    (hc : ∀ H, c ≤ twoTapeLaw ν (commonCut L H)) :
    ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H := by
  have hb := common_renewal_tail_sum_bound ν L hL c hc
  have hn : (∑' N, twoTapeLaw ν (noCommonThrough L N)) ≠ ∞ :=
    (ENNReal.lt_top_of_mul_ne_top_right (ne_top_of_le_ne_top ENNReal.one_ne_top hb) hcpos).ne
  filter_upwards [ae_eventually_notMem hn] with Z hZ
  obtain ⟨N,hN⟩ := hZ.exists
  by_contra h
  apply hN
  intro j hj _ hc
  exact h ⟨j,hj,hc⟩

lemma lintegral_firstCommonWidth_le {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a) (c : ℝ≥0∞) (hcpos : c ≠ 0)
    (hc : ∀ H, c ≤ twoTapeLaw ν (commonCut L H)) :
    (∫⁻ Z, (firstCommonWidth L Z : ℝ≥0∞) ∂twoTapeLaw ν) ≤ c⁻¹ := by
  have hctop : c ≠ ∞ := ne_top_of_le_ne_top (measure_ne_top _ _) (hc 0)
  have hb := (ENNReal.mul_le_iff_le_inv hcpos hctop).mp (common_renewal_tail_sum_bound ν L hL c hc)
  rw [lintegral_nat_tail _ _ (measurable_firstCommonWidth L)]
  exact (ENNReal.tsum_le_tsum (fun N => measure_mono (firstCommonWidth_tail_subset L N))).trans (by simpa using hb)

lemma integrable_firstCommonWidth {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a) (c : ℝ≥0∞) (hcpos : c ≠ 0)
    (hc : ∀ H, c ≤ twoTapeLaw ν (commonCut L H)) :
    Integrable (fun Z => (firstCommonWidth L Z : ℝ)) (twoTapeLaw ν) := by
  have hm : Measurable (fun Z => (firstCommonWidth L Z : ℝ)) :=
    (measurable_of_countable Nat.cast).comp (measurable_firstCommonWidth L)
  refine ⟨hm.aestronglyMeasurable,?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun Z => Nat.cast_nonneg (firstCommonWidth L Z)))).mpr
  simp_rw [ENNReal.ofReal_natCast]
  exact (lintegral_firstCommonWidth_le ν L hL c hcpos hc).trans_lt (ENNReal.inv_lt_top.mpr (pos_iff_ne_zero.mpr hcpos))

def listHasCut {α : Type*} (L : α → ℕ) (a : TapeList α) (H : ℕ) : Prop :=
  ∃ n, ∃ hn : n ≤ a.1, (∑ i : Fin n, L (a.2 (i.castLE hn))) = H

lemma listHasCut_prefix {α : Type*} (L : α → ℕ) (Z : ℕ → α) (n H : ℕ) :
    listHasCut L (tapePrefix n Z) H ↔ ∃ j ≤ n, tapeHeight L Z j = H := by
  change (∃ j, ∃ hj : j ≤ n, (∑ i : Fin j, L (Z (i : ℕ))) = H) ↔ _
  simp only [Fin.sum_univ_eq_sum_range (fun i => L (Z i)),tapeHeight,exists_prop]

lemma renewalCut_iff_listHasCut {α : Type*} (L : α → ℕ) (Z : ℕ → α)
    (hZ : ∀ i, 0 < L (Z i)) (H j : ℕ) (hH : Z ∈ renewalCut L H) (hj : j ≤ H) :
    Z ∈ renewalCut L j ↔ listHasCut L (cutList L H Z) j := by
  obtain ⟨n,hn⟩ := hH
  rw [cutList,cutListIndex_eq L H Z hZ hn,listHasCut_prefix]
  constructor
  · rintro ⟨k,hk⟩
    refine ⟨k,?_,hk⟩
    exact (tapeHeight_strictMono L Z hZ).le_iff_le.mp (by omega)
  · rintro ⟨k,_,hk⟩;exact ⟨k,hk⟩

lemma commonCut_iff_listHasCut {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α)
    (hZ : ∀ b i, 0 < L b (Z (b,i))) (H j : ℕ) (hH : Z ∈ commonCut L H) (hj : j ≤ H) :
    Z ∈ commonCut L j ↔ ∀ b, listHasCut (L b) (commonCutList L H Z b) j := by
  exact forall_congr' (fun b => renewalCut_iff_listHasCut (L b) _ (hZ b) H j (hH b) hj)

noncomputable def firstCommonBlock {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α) : TwoTapeList α :=
  commonCutList L (firstCommonWidth L Z) Z

noncomputable def commonRestart {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α) : TwoTape α :=
  afterCommonCut L (firstCommonWidth L Z) Z

lemma measurable_firstCommonBlock {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (L : Bool → α → ℕ) : Measurable (firstCommonBlock L) := by
  have hm : Measurable (fun p : TwoTape α × ℕ => commonCutList L p.2 p.1) :=
    measurable_from_prod_countable_left (measurable_commonCutList L)
  exact hm.comp (measurable_id.prodMk (measurable_firstCommonWidth L))

lemma measurable_commonRestart {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (L : Bool → α → ℕ) : Measurable (commonRestart L) := by
  have hm : Measurable (fun p : TwoTape α × ℕ => afterCommonCut L p.2 p.1) :=
    measurable_from_prod_countable_left (measurable_afterCommonCut L)
  exact hm.comp (measurable_id.prodMk (measurable_firstCommonWidth L))

def IsFirstCommonList {α : Type*} (L : Bool → α → ℕ) (a : TwoTapeList α) : Prop :=
  0 < listHeight (L false) (a false) ∧
    (∀ b, listHeight (L b) (a b) = listHeight (L false) (a false)) ∧
    ∀ j, 0 < j → j < listHeight (L false) (a false) → ¬∀ b, listHasCut (L b) (a b) j

lemma firstCommonBlock_spec {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α)
    (hZ : ∀ b i, 0 < L b (Z (b,i))) (he : ∃ H, 0 < H ∧ Z ∈ commonCut L H) :
    IsFirstCommonList L (firstCommonBlock L Z) ∧
      listHeight (L false) (firstCommonBlock L Z false) = firstCommonWidth L Z := by
  have hK := firstCommonWidth_spec L Z he
  have hh := (commonCutList_atom_iff L (firstCommonWidth L Z) Z hZ
    (firstCommonBlock L Z)).mp ⟨hK.2.1,rfl⟩
  refine ⟨⟨by rw [hh.1 false];exact hK.1,fun b => (hh.1 b).trans (hh.1 false).symm,?_⟩,hh.1 false⟩
  intro j hj hjK hc
  rw [hh.1 false] at hjK
  exact hK.2.2 j hjK hj ((commonCut_iff_listHasCut L Z hZ _ j hK.2.1 hjK.le).mpr hc)

lemma firstCommonBlock_atom_iff {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α)
    (hZ : ∀ b i, 0 < L b (Z (b,i))) (he : ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (a : TwoTapeList α) (ha : IsFirstCommonList L a) :
    firstCommonBlock L Z = a ↔ Z ∈ twoCylinder a := by
  let H := listHeight (L false) (a false)
  constructor
  · intro h
    have hK := firstCommonWidth_spec L Z he
    exact ((commonCutList_atom_iff L _ Z hZ a).mp ⟨hK.2.1,h⟩).2
  · intro hcyl
    have hc := (commonCutList_atom_iff L H Z hZ a).mpr ⟨ha.2.1,hcyl⟩
    have heq : firstCommonWidth L Z = H := by
      apply (firstCommonWidth_eq_pos_iff L Z ha.1).mpr
      refine ⟨hc.1,fun j hj hjH hcut => ?_⟩
      apply ha.2.2 j hj (by change j < H;omega)
      rw [← hc.2]
      exact (commonCut_iff_listHasCut L Z hZ H j hc.1 (by omega)).mp hcut
    simp only [firstCommonBlock,heq,hc.2]

lemma commonRestart_eq_shift {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α)
    (a : TwoTapeList α) (ha : firstCommonBlock L Z = a) :
    commonRestart L Z = twoShift (fun b => (a b).1) Z := by
  unfold commonRestart afterCommonCut
  rw [commonCutIndices_eq_lengths L _ Z a ha]

noncomputable def commonBlockLaw {α : Type*} [MeasurableSpace α]
    (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) : Measure (TwoTapeList α) :=
  (twoTapeLaw ν).map (firstCommonBlock L)

lemma firstCommonBlock_suffix_factorization {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (a : TwoTapeList α) (E : Set (TwoTape α)) (hE : MeasurableSet E) :
    twoTapeLaw ν {Z | firstCommonBlock L Z = a ∧ commonRestart L Z ∈ E} =
      commonBlockLaw ν L {a} * twoTapeLaw ν E := by
  classical
  have hZ := ae_twoTape_prop ν (fun b a => 0 < L b a)
    (fun b => measurableSet_lt measurable_const (measurable_of_countable (L b))) hL
  rw [commonBlockLaw,Measure.map_apply (measurable_firstCommonBlock L) (measurableSet_singleton a)]
  by_cases ha : IsFirstCommonList L a
  · have hmass : twoTapeLaw ν (firstCommonBlock L ⁻¹' {a}) = twoTapeLaw ν (twoCylinder a) := by
      apply measure_congr
      filter_upwards [hZ,he] with Z hZ he
      exact propext (firstCommonBlock_atom_iff L Z hZ he a ha)
    have hevent : twoTapeLaw ν {Z | firstCommonBlock L Z = a ∧ commonRestart L Z ∈ E} =
        twoTapeLaw ν {Z | Z ∈ twoCylinder a ∧ twoShift (fun b => (a b).1) Z ∈ E} := by
      apply measure_congr
      filter_upwards [hZ,he] with Z hZ he
      apply propext
      constructor
      · rintro ⟨h,ht⟩
        exact ⟨(firstCommonBlock_atom_iff L Z hZ he a ha).mp h,
          by simpa only [commonRestart_eq_shift L Z a h] using ht⟩
      · rintro ⟨h,ht⟩
        have hb := (firstCommonBlock_atom_iff L Z hZ he a ha).mpr h
        exact ⟨hb,by simpa only [commonRestart_eq_shift L Z a hb] using ht⟩
    rw [hmass,hevent,twoCylinder_suffix_factorization ν a E hE,twoCylinder_mass]
  · have hzero : twoTapeLaw ν (firstCommonBlock L ⁻¹' {a}) = 0 := by
      apply measure_eq_zero_iff_ae_notMem.mpr
      filter_upwards [hZ,he] with Z hZ he h
      exact ha (h ▸ (firstCommonBlock_spec L Z hZ he).1)
    rw [hzero,zero_mul]
    exact measure_mono_null (fun _ h => h.1) hzero

lemma commonRestart_measurePreserving {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H) :
    MeasurePreserving (commonRestart L) (twoTapeLaw ν) (twoTapeLaw ν) := by
  refine ⟨measurable_commonRestart L,Measure.ext (fun E hE => ?_)⟩
  rw [Measure.map_apply (measurable_commonRestart L) hE,
    measure_eq_tsum_fibres (twoTapeLaw ν) (firstCommonBlock L) (measurable_firstCommonBlock L)
      (hE.preimage (measurable_commonRestart L))]
  simp_rw [show ∀ a, {Z | firstCommonBlock L Z = a} ∩ commonRestart L ⁻¹' E =
      {Z | firstCommonBlock L Z = a ∧ commonRestart L Z ∈ E} from fun _ => rfl,
    firstCommonBlock_suffix_factorization ν L hL he _ E hE,ENNReal.tsum_mul_right]
  have hp : IsProbabilityMeasure (commonBlockLaw ν L) :=
    probabilityMeasure_map (μ := twoTapeLaw ν) (measurable_firstCommonBlock L).aemeasurable
  have hsum := measure_eq_tsum_fibres (commonBlockLaw ν L) id measurable_id MeasurableSet.univ
  simp only [id_eq,Set.inter_univ,Set.ofPred_eq_eq_singleton,measure_univ] at hsum
  rw [← hsum,one_mul]

def commonNeeds {α : Type*} (L : Bool → α → ℕ) (b : Bool) (i : ℕ) : Set (TwoTape α) :=
  {Z | ∀ j, 0 < j → j ≤ i → ¬∃ n,
    tapeHeight (L (!b)) (fun k => Z (!b,k)) n = tapeHeight (L b) (fun k => Z (b,k)) j}

lemma commonNeeds_iff {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α)
    (hZ : ∀ b i, 0 < L b (Z (b,i))) (he : ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (b : Bool) (i : ℕ) :
    Z ∈ commonNeeds L b i ↔ i < (firstCommonBlock L Z b).1 := by
  have hK := firstCommonWidth_spec L Z he
  obtain ⟨n,hn⟩ := hK.2.1 b
  have hnblock : (firstCommonBlock L Z b).1 = n := by
    exact cutListIndex_eq (L b) _ _ (hZ b) hn
  rw [hnblock]
  have hnpos : 0 < n := by
    by_contra h
    have hn0 : n = 0 := by omega
    rw [hn0] at hn
    have hz : firstCommonWidth L Z = 0 := hn.symm
    omega
  have h0 (j : ℕ) (hj : 0 < j) : 0 < tapeHeight (L b) (fun k => Z (b,k)) j :=
    lt_of_lt_of_le hj (le_tapeHeight (L b) _ (hZ b) j)
  constructor
  · intro hc
    by_contra hin
    obtain ⟨m,hm⟩ := hK.2.1 (!b)
    exact hc n hnpos (by omega) ⟨m,hm.trans hn.symm⟩
  · intro hin j hj hji ⟨m,hm⟩
    have hjn : j < n := lt_of_le_of_lt hji hin
    have hcut : Z ∈ commonCut L (tapeHeight (L b) (fun k => Z (b,k)) j) := by
      intro c
      by_cases hcb : c = b
      · subst c;exact ⟨j,rfl⟩
      · have hco : c = !b := by cases b <;> cases c <;> simp_all
        subst c;exact ⟨m,hm⟩
    apply hK.2.2 _ _ (h0 j hj) hcut
    rw [← hn]
    exact (tapeHeight_strictMono (L b) _ (hZ b)) hjn

lemma coordSigma_le {ι α : Type*} [MeasurableSpace α] (s : Set ι) :
    coordSigma (α := α) s ≤ inferInstanceAs (MeasurableSpace (ι → α)) :=
  iSup₂_le (fun i _ => (measurable_pi_apply (X := fun _ => α) i).comap_le)

lemma measurableSet_commonNeeds_rest {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (L : Bool → α → ℕ) (b : Bool) (i : ℕ) :
    @MeasurableSet (TwoTape α) (coordSigma {p | p ≠ (b,i)}) (commonNeeds L b i) := by
  let : MeasurableSpace (TwoTape α) := coordSigma {p | p ≠ (b,i)}
  have hother (n : ℕ) : Measurable (fun Z : TwoTape α => tapeHeight (L (!b)) (fun k => Z (!b,k)) n) := by
    apply Finset.measurable_sum
    intro k _
    apply (measurable_of_countable (L (!b))).comp
    apply measurable_coordEval
    intro hp
    have hb := congrArg Prod.fst hp
    cases b <;> simp at hb
  have hprev (j : ℕ) (hj : j ≤ i) : Measurable (fun Z : TwoTape α => tapeHeight (L b) (fun k => Z (b,k)) j) := by
    apply Finset.measurable_sum
    intro k hk
    apply (measurable_of_countable (L b)).comp
    apply measurable_coordEval
    intro hp
    have hi := congrArg Prod.snd hp
    have hk := Finset.mem_range.mp hk
    change k = i at hi
    omega
  simp only [commonNeeds,Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro j
  apply MeasurableSet.iInter
  intro _
  apply MeasurableSet.iInter
  intro hj
  change MeasurableSet ({Z : TwoTape α | ∃ n, tapeHeight (L (!b)) (fun k => Z (!b,k)) n =
      tapeHeight (L b) (fun k => Z (b,k)) j}ᶜ)
  apply MeasurableSet.compl
  simp only [Set.ofPred_exists]
  exact MeasurableSet.iUnion (fun n => measurableSet_eq_fun (hother n) (hprev j hj))

lemma measurableSet_commonNeeds {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (L : Bool → α → ℕ) (b : Bool) (i : ℕ) :
    MeasurableSet (commonNeeds L b i) :=
  coordSigma_le _ _ (measurableSet_commonNeeds_rest L b i)

lemma commonNeeds_next_independent {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (b : Bool) (i : ℕ) (R : α → ℝ≥0∞) :
    IndepFun ((commonNeeds L b i).indicator (fun _ => (1 : ℝ≥0∞)))
      (fun Z : TwoTape α => R (Z (b,i))) (twoTapeLaw ν) := by
  classical
  have hS : @Measurable (TwoTape α) ℝ≥0∞ (coordSigma {p | p ≠ (b,i)}) _
      ((commonNeeds L b i).indicator (fun _ => (1 : ℝ≥0∞))) := by
    let : MeasurableSpace (TwoTape α) := coordSigma {p | p ≠ (b,i)}
    exact measurable_const.indicator (measurableSet_commonNeeds_rest L b i)
  have hT : @Measurable (TwoTape α) ℝ≥0∞ (coordSigma {(b,i)}) _
      (fun Z => R (Z (b,i))) := by
    let : MeasurableSpace (TwoTape α) := coordSigma {(b,i)}
    exact (measurable_of_countable R).comp (measurable_coordEval rfl)
  have hd : Disjoint {p : Bool × ℕ | p ≠ (b,i)} {(b,i)} := by
    apply Set.disjoint_left.mpr
    exact fun p hp hq => hp hq
  have hind := indep_iSup_of_disjoint (fun i : Bool × ℕ =>
    (measurable_pi_apply (X := fun _ => α) i).comap_le)
    (iIndepFun_infinitePi (P := fun i : Bool × ℕ => ν i.1) (X := fun _ x => x) (fun _ => measurable_id)) hd
  exact (IndepFun_iff_Indep _ _ _).mpr (indep_of_indep_of_le hind hS.comap_le hT.comap_le)

lemma commonNeeds_radius_factorization {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (b : Bool) (i : ℕ) (R : α → ℝ≥0∞) :
    (∫⁻ Z, (commonNeeds L b i).indicator (fun Z => R (Z (b,i))) Z ∂twoTapeLaw ν) =
      twoTapeLaw ν (commonNeeds L b i) * ∫⁻ a, R a ∂ν b := by
  classical
  have he : (commonNeeds L b i).indicator (fun Z => R (Z (b,i))) =
      fun Z => (commonNeeds L b i).indicator (fun _ => (1 : ℝ≥0∞)) Z * R (Z (b,i)) := by
    funext Z
    by_cases h : Z ∈ commonNeeds L b i <;> simp [h]
  rw [he]
  have hx := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
    (measurable_const.indicator (measurableSet_commonNeeds L b i))
    ((measurable_of_countable R).comp (measurable_pi_apply (b,i)))
    (commonNeeds_next_independent ν L b i R)
  simp only [Pi.mul_apply,Function.comp_apply] at hx
  rw [hx]
  have hm : (twoTapeLaw ν).map (fun Z => Z (b,i)) = ν b := by
    exact Measure.infinitePi_map_eval (fun p : Bool × ℕ => ν p.1) (b,i)
  rw [lintegral_indicator (measurableSet_commonNeeds L b i)]
  simp only [lintegral_const,Measure.restrict_apply_univ,one_mul]
  rw [← lintegral_map (measurable_of_countable R) (measurable_pi_apply (b,i)),hm]

noncomputable def listCost {α : Type*} (R : α → ℝ≥0∞) (a : TapeList α) : ℝ≥0∞ :=
  ∑ i : Fin a.1, R (a.2 i)

lemma firstCommonBlock_length_le {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α)
    (hZ : ∀ b i, 0 < L b (Z (b,i))) (he : ∃ H, 0 < H ∧ Z ∈ commonCut L H) (b : Bool) :
    (firstCommonBlock L Z b).1 ≤ firstCommonWidth L Z := by
  obtain ⟨n,hn⟩ := (firstCommonWidth_spec L Z he).2.1 b
  have hindex := cutListIndex_eq (L b) _ _ (hZ b) hn
  change cutListIndex (L b) (firstCommonWidth L Z) (fun i => Z (b,i)) ≤ _
  rw [hindex,← hn]
  exact le_tapeHeight (L b) _ (hZ b) n

lemma firstCommonBlock_cost_eq {α : Type*} (L : Bool → α → ℕ) (Z : TwoTape α)
    (hZ : ∀ b i, 0 < L b (Z (b,i))) (he : ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (b : Bool) (R : α → ℝ≥0∞) :
    listCost R (firstCommonBlock L Z b) =
      ∑' i, (commonNeeds L b i).indicator (fun Z => R (Z (b,i))) Z := by
  classical
  have hsum (i : ℕ) : (commonNeeds L b i).indicator (fun Z => R (Z (b,i))) Z =
      if i < (firstCommonBlock L Z b).1 then R (Z (b,i)) else 0 := by
    simp only [Set.indicator_apply,commonNeeds_iff L Z hZ he b i]
  simp_rw [hsum]
  rw [tsum_eq_sum (s := Finset.range (firstCommonBlock L Z b).1)]
  · change (∑ i : Fin (firstCommonBlock L Z b).1, R (Z (b,i))) = _
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => R (Z (b,i)))]
    apply Finset.sum_congr rfl
    intro i hi
    rw [ite_eq_left (Finset.mem_range.mp hi)]
  · intro i hi
    simp only [Finset.mem_range] at hi
    exact ite_eq_right hi

lemma commonBlock_Wald {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (b : Bool) (R : α → ℝ≥0∞) :
    (∫⁻ Z, listCost R (firstCommonBlock L Z b) ∂twoTapeLaw ν) =
      (∫⁻ Z, ((firstCommonBlock L Z b).1 : ℝ≥0∞) ∂twoTapeLaw ν) * ∫⁻ a, R a ∂ν b := by
  classical
  have hZ := ae_twoTape_prop ν (fun b a => 0 < L b a)
    (fun b => measurableSet_lt measurable_const (measurable_of_countable (L b))) hL
  have hN : Measurable (fun Z => (firstCommonBlock L Z b).1) :=
    (measurable_of_countable (fun a : TwoTapeList α => (a b).1)).comp (measurable_firstCommonBlock L)
  have hcost : (∫⁻ Z, listCost R (firstCommonBlock L Z b) ∂twoTapeLaw ν) =
      ∫⁻ Z, ∑' i, (commonNeeds L b i).indicator (fun Z => R (Z (b,i))) Z ∂twoTapeLaw ν := by
    apply lintegral_congr_ae
    filter_upwards [hZ,he] with Z hZ he
    exact firstCommonBlock_cost_eq L Z hZ he b R
  have ht : (∫⁻ Z, ∑' i, (commonNeeds L b i).indicator (fun Z => R (Z (b,i))) Z ∂twoTapeLaw ν) =
      ∑' i, ∫⁻ Z, (commonNeeds L b i).indicator (fun Z => R (Z (b,i))) Z ∂twoTapeLaw ν :=
    lintegral_tsum (fun i => (((measurable_of_countable R).comp (measurable_pi_apply (b,i))).indicator
      (measurableSet_commonNeeds L b i)).aemeasurable)
  rw [hcost,ht]
  simp_rw [commonNeeds_radius_factorization ν L b _ R]
  rw [ENNReal.tsum_mul_right,lintegral_nat_tail _ _ hN]
  congr 1
  apply tsum_congr
  intro i
  apply measure_congr
  filter_upwards [hZ,he] with Z hZ he
  exact propext (commonNeeds_iff L Z hZ he b i)

lemma commonBlock_cost_bound {α : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (b : Bool) (R : α → ℝ≥0∞) :
    (∫⁻ Z, listCost R (firstCommonBlock L Z b) ∂twoTapeLaw ν) ≤
      (∫⁻ Z, (firstCommonWidth L Z : ℝ≥0∞) ∂twoTapeLaw ν) * ∫⁻ a, R a ∂ν b := by
  rw [commonBlock_Wald ν L hL he b R]
  apply mul_le_mul' _ le_rfl
  apply lintegral_mono_ae
  filter_upwards [ae_twoTape_prop ν (fun b a => 0 < L b a)
    (fun b => measurableSet_lt measurable_const (measurable_of_countable (L b))) hL,he] with Z hZ he
  exact_mod_cast firstCommonBlock_length_le L Z hZ he b

end DirectionalZeroOne

end OAI

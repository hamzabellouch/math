import OAI.Probability.DirectionalWalk.ThreeLists

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

open scoped Classical

section SumLaws
variable {G : Type*} [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [AddCommGroup G]

noncomputable def sumLaw (ν : Measure G) : ℕ → Measure G
  | 0 => Measure.dirac 0
  | n+1 => ν.conv (sumLaw ν n)

instance conv_probability (μ ν : Measure G) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (μ.conv ν) :=
  probabilityMeasure_map (measurable_of_countable _).aemeasurable

instance sumLaw_probability (ν : Measure G) [IsProbabilityMeasure ν] (n : ℕ) :
    IsProbabilityMeasure (sumLaw ν n) := by
  induction n with
  | zero => exact inferInstanceAs (IsProbabilityMeasure (Measure.dirac (0 : G)))
  | succ n ih =>
    let := ih
    exact inferInstanceAs (IsProbabilityMeasure (ν.conv (sumLaw ν n)))

lemma sumLaw_add (ν : Measure G) [IsProbabilityMeasure ν] (m n : ℕ) :
    sumLaw ν (m+n) = (sumLaw ν m).conv (sumLaw ν n) := by
  induction m with
  | zero => simp only [Nat.zero_add,sumLaw,Measure.dirac_zero_conv]
  | succ m ih =>
    rw [Nat.succ_add,sumLaw,ih,sumLaw,Measure.conv_assoc]

lemma entropy_conv_ge_left (μ ν : Measure G) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hi : Integrable (informationOf (μ.conv ν) id) (μ.conv ν)) :
    entropyOf μ id ≤ entropyOf (μ.conv ν) id := by
  have hs : Integrable (informationOf (μ.prod ν) (fun p => p.1+p.2)) (μ.prod ν) := by
    rw [Measure.conv,integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
      (measurable_of_countable _).aemeasurable] at hi
    rw [informationOf_map] at hi
    exact hi
  have hh := conditionedEntropy_le_entropyOf (μ.prod ν) (fun p => p.1+p.2) Prod.snd hs
  have he := conditionedInformation_fiberwise_injective (μ.prod ν) Prod.fst Prod.snd
    (fun y x => x+y) (fun _ _ _ h => add_right_cancel h)
  have hce : conditionedEntropy (μ.prod ν) (fun p => p.1+p.2) Prod.snd = entropyOf μ id := by
    change (∫ p, conditionedInformation (μ.prod ν) (fun p => p.1+p.2) Prod.snd p ∂μ.prod ν) = _
    rw [he]
    change conditionedEntropy (μ.prod ν) Prod.fst Prod.snd = _
    have hind : IndepFun (Prod.fst : G × G → G) Prod.snd (μ.prod ν) :=
      indepFun_prod measurable_id measurable_id
    rw [conditionedEntropy_indep _ _ _ hind]
    exact entropyOf_prod_fst μ ν id
  rw [hce] at hh
  simpa only [Measure.conv,entropyOf_map,Function.id_comp] using hh

lemma sumLaw_entropy_monotone (ν : Measure G) [IsProbabilityMeasure ν]
    (hi : ∀ n, Integrable (informationOf (sumLaw ν n) id) (sumLaw ν n)) :
    Monotone (fun n => entropyOf (sumLaw ν n) id) := by
  intro m n hmn
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hmn
  dsimp only
  rw [sumLaw_add]
  apply entropy_conv_ge_left
  rw [← sumLaw_add]
  exact hi _
end SumLaws

lemma sumLaw_lattice_moment {q : ℕ} (ν : Measure (Fin q → ℤ)) [IsProbabilityMeasure ν]
    (hi : ∀ i, Integrable (fun x => |(x i : ℝ)|) ν) (a : ℝ)
    (hm : ∀ i, (∫ x, |(x i : ℝ)| ∂ν) ≤ a) (n : ℕ) :
    ∀ i, Integrable (fun x => |(x i : ℝ)|) (sumLaw ν n) ∧
      (∫ x, |(x i : ℝ)| ∂sumLaw ν n) ≤ n*a := by
  induction n with
  | zero =>
    intro i
    refine ⟨integrable_dirac (by simp),?_⟩
    simp only [sumLaw,integral_dirac,Pi.zero_apply,Int.cast_zero,abs_zero,Nat.cast_zero,zero_mul,le_refl]
  | succ n ih =>
    intro i
    have ha : Integrable (fun p : (Fin q → ℤ) × (Fin q → ℤ) => |(p.1 i : ℝ)|+|(p.2 i : ℝ)|)
        (ν.prod (sumLaw ν n)) := (hi i).comp_fst _ |>.add ((ih i).1.comp_snd _)
    have hb : Integrable (fun p : (Fin q → ℤ) × (Fin q → ℤ) => |((p.1 i+p.2 i : ℤ) : ℝ)|)
        (ν.prod (sumLaw ν n)) := by
      apply ha.mono' (measurable_of_countable _).aestronglyMeasurable
      filter_upwards [] with p
      simpa only [Real.norm_eq_abs,abs_abs,Int.cast_add] using abs_add_le (p.1 i : ℝ) (p.2 i : ℝ)
    constructor
    · rw [sumLaw,Measure.conv,integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
        (measurable_of_countable _).aemeasurable]
      exact hb
    · rw [sumLaw,Measure.conv,integral_map_of_stronglyMeasurable (measurable_of_countable _)
        (measurable_of_countable _).stronglyMeasurable]
      calc
        _ ≤ ∫ p : (Fin q → ℤ) × (Fin q → ℤ), |(p.1 i : ℝ)|+|(p.2 i : ℝ)| ∂ν.prod (sumLaw ν n) :=
          integral_mono hb ha (fun p => by simpa only [Pi.add_apply,Int.cast_add] using abs_add_le (p.1 i : ℝ) (p.2 i : ℝ))
        _ = (∫ x, |(x i : ℝ)| ∂ν) + ∫ x, |(x i : ℝ)| ∂sumLaw ν n := by
          rw [integral_add ((hi i).comp_fst _) ((ih i).1.comp_snd _),integral_fun_fst (fun x : Fin q → ℤ => |(x i : ℝ)|),
            integral_fun_snd (fun x : Fin q → ℤ => |(x i : ℝ)|)]
          simp only [measureReal_def,measure_univ,ENNReal.toReal_one,one_smul]
        _ ≤ _ := by have := hm i;have := (ih i).2;push_cast; nlinarith

lemma sumLaw_lattice_entropy {q : ℕ} (ν : Measure (Fin q → ℤ)) [IsProbabilityMeasure ν]
    (hi : ∀ i, Integrable (fun x => |(x i : ℝ)|) ν) (a : ℝ) (ha : 0 < a)
    (hm : ∀ i, (∫ x, |(x i : ℝ)| ∂ν) ≤ a) (n : ℕ) :
    Integrable (informationOf (sumLaw ν n) id) (sumLaw ν n) ∧
      entropyOf (sumLaw ν n) id ≤ q*(1+Real.log 2+Real.log (a+1)+Real.log (n+1)) := by
  have h := sumLaw_lattice_moment ν hi a hm n
  have hb := entropyOf_lattice_moment (sumLaw ν n) q id (fun i => (h i).1)
    ((n+1)*a) (mul_pos (by positivity) ha) (fun i => (h i).2.trans (by nlinarith))
  refine ⟨hb.1,hb.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg q)
  have hl : Real.log ((n+1)*a+1) ≤ Real.log ((a+1)*(n+1)) := by
    apply Real.log_le_log (by positivity)
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  rw [Real.log_mul (by positivity) (by positivity)] at hl
  linarith
section ListTotals
variable {α G : Type*} [AddCommMonoid G]

noncomputable def listTotal (D : α → G) (a : TapeList α) : G := ∑ i, D (a.2 i)
noncomputable def pairTotal (D : Bool → α → G) (a : TwoTapeList α) : G :=
  listTotal (D false) (a false) + listTotal (D true) (a true)

lemma listTotal_prefix (D : α → G) (Z : ℕ → α) (n : ℕ) :
    listTotal D (tapePrefix n Z) = ∑ i ∈ Finset.range n, D (Z i) := by
  exact Fin.sum_univ_eq_sum_range (fun i => D (Z i)) n

lemma commonCutIndices_add (L : Bool → α → ℕ) (H J : ℕ) (Z : TwoTape α)
    (hZ : ∀ b i, 0 < L b (Z (b,i))) (hH : Z ∈ commonCut L H)
    (hJ : afterCommonCut L H Z ∈ commonCut L J) (b : Bool) :
    commonCutIndices L (H+J) Z b =
      commonCutIndices L H Z b + commonCutIndices L J (afterCommonCut L H Z) b := by
  apply cutListIndex_eq (L b) (H+J) _ (hZ b)
  rw [tapeHeight_add]
  have h1 : tapeHeight (L b) (fun i => Z (b,i)) (commonCutIndices L H Z b) = H :=
    cutListIndex_spec (L b) H _ (hZ b) (hH b)
  have h2 : tapeHeight (L b) (fun i => Z (b,commonCutIndices L H Z b+i))
      (commonCutIndices L J (afterCommonCut L H Z) b) = J :=
    cutListIndex_spec (L b) J _ (fun i => hZ b _) (hJ b)
  rw [h1,h2]

lemma listTotal_commonCut_add (L : Bool → α → ℕ) (D : α → G) (H J : ℕ) (Z : TwoTape α)
    (hZ : ∀ b i, 0 < L b (Z (b,i))) (hH : Z ∈ commonCut L H)
    (hJ : afterCommonCut L H Z ∈ commonCut L J) (b : Bool) :
    listTotal D (commonCutList L (H+J) Z b) = listTotal D (commonCutList L H Z b) +
      listTotal D (commonCutList L J (afterCommonCut L H Z) b) := by
  change listTotal D (tapePrefix (commonCutIndices L (H+J) Z b) (fun i => Z (b,i))) =
    listTotal D (tapePrefix (commonCutIndices L H Z b) (fun i => Z (b,i))) +
    listTotal D (tapePrefix (commonCutIndices L J (afterCommonCut L H Z) b) (fun i => afterCommonCut L H Z (b,i)))
  simp only [listTotal_prefix]
  rw [commonCutIndices_add L H J Z hZ hH hJ b,Finset.sum_range_add]
  rfl

lemma nthCommonList_total (L : Bool → α → ℕ) (D : α → G) (Z : TwoTape α)
    (hZ : ∀ b i, 0 < L b (Z (b,i)))
    (he : ∀ r, ∃ H, 0 < H ∧ ((commonRestart L)^[r] Z) ∈ commonCut L H) (r : ℕ) (b : Bool) :
    listTotal D (nthCommonList L r Z b) =
      ∑ i ∈ Finset.range r, listTotal D (commonBlocks L Z i b) := by
  induction r with
  | zero =>
    have hi : commonCutIndices L 0 Z b = 0 := cutListIndex_eq (L b) 0 _ (hZ b) rfl
    change listTotal D (tapePrefix (commonCutIndices L (commonDepth L Z 0) Z b) (fun i => Z (b,i))) = _
    simp only [commonDepth_zero,hi,listTotal_prefix,Finset.range_zero,Finset.sum_empty]
  | succ r ih =>
    obtain ⟨_,hc,_⟩ := firstCommonWidth_spec L ((commonRestart L)^[r] Z) (he r)
    have hspec := commonDepth_spec L Z hZ he r
    have hc' : afterCommonCut L (commonDepth L Z r) Z ∈
        commonCut L (firstCommonWidth L ((commonRestart L)^[r] Z)) := by rw [hspec.2.1];exact hc
    rw [Finset.sum_range_succ,← ih]
    unfold nthCommonList
    rw [commonDepth_succ,listTotal_commonCut_add L D _ _ Z hZ hspec.1 hc' b,hspec.2.1]
    rfl

lemma nthCommonList_pairTotal (L : Bool → α → ℕ) (D : Bool → α → G) (Z : TwoTape α)
    (hZ : ∀ b i, 0 < L b (Z (b,i)))
    (he : ∀ r, ∃ H, 0 < H ∧ ((commonRestart L)^[r] Z) ∈ commonCut L H) (r : ℕ) :
    pairTotal D (nthCommonList L r Z) = ∑ i ∈ Finset.range r, pairTotal D (commonBlocks L Z i) := by
  simp only [pairTotal,nthCommonList_total L _ Z hZ he,Finset.sum_add_distrib]
end ListTotals
section SumCommon
variable {G : Type*} [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [AddCommGroup G]

lemma iid_sum_law (ν : Measure G) [IsProbabilityMeasure ν] (n : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => ν)).map (fun Z => ∑ i ∈ Finset.range n, Z i) = sumLaw ν n := by
  induction n with
  | zero => simp only [Finset.range_zero,Finset.sum_empty,sumLaw,Measure.map_const,measure_univ,one_smul]
  | succ n ih =>
    have hind := (iid_prefix_suffix_independent ν n).comp
      (measurable_of_countable (fun Z : Fin n → G => ∑ i, Z i)) (measurable_pi_apply 0)
    have heq : (fun Z : ℕ → G => ∑ i : Fin n, Z i) = (fun Z => ∑ i ∈ Finset.range n, Z i) := by
      funext Z
      exact Fin.sum_univ_eq_sum_range Z n
    simp only [Function.comp_def,Nat.add_zero] at hind
    rw [heq] at hind
    have hm := hind.map_add_eq_map_conv_map (by fun_prop) (by fun_prop)
    change (Measure.infinitePi (fun _ : ℕ => ν)).map
      (fun Z => (∑ i ∈ Finset.range n, Z i)+Z n) = _ at hm
    simp only [Finset.sum_range_succ]
    rw [hm,ih,Measure.infinitePi_map_eval,Measure.conv_comm]
    rfl

variable {α : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]

noncomputable def commonGapLaw (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (D : Bool → α → G) : Measure G :=
  (commonBlockLaw ν L).map (pairTotal D)

instance commonBlockLaw_probability (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) : IsProbabilityMeasure (commonBlockLaw ν L) :=
  probabilityMeasure_map (μ := twoTapeLaw ν) (measurable_firstCommonBlock L).aemeasurable

instance commonGapLaw_probability (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (D : Bool → α → G) : IsProbabilityMeasure (commonGapLaw ν L D) :=
  probabilityMeasure_map (measurable_of_countable _).aemeasurable

lemma nthCommonLaw_pairTotal (ν : Bool → Measure α) [∀ b, IsProbabilityMeasure (ν b)]
    (L : Bool → α → ℕ) (hL : ∀ b, ∀ᵐ a ∂ν b, 0 < L b a)
    (he : ∀ᵐ Z ∂twoTapeLaw ν, ∃ H, 0 < H ∧ Z ∈ commonCut L H)
    (D : Bool → α → G) (r : ℕ) :
    (nthCommonLaw ν L r).map (pairTotal D) = sumLaw (commonGapLaw ν L D) r := by
  rw [nthCommonLaw,Measure.map_map (measurable_of_countable _) (measurable_nthCommonList L r)]
  have hae : (fun Z => pairTotal D (nthCommonList L r Z)) =ᵐ[twoTapeLaw ν]
      (fun Z => ∑ i ∈ Finset.range r, pairTotal D (commonBlocks L Z i)) := by
    filter_upwards [ae_twoTape_prop ν (fun b a => 0 < L b a)
      (fun b => measurableSet_lt measurable_const (measurable_of_countable (L b))) hL,
      ae_common_iterates ν L hL he] with Z hZ hiter
    exact nthCommonList_pairTotal L D Z hZ hiter r
  change (twoTapeLaw ν).map (fun Z => pairTotal D (nthCommonList L r Z)) = _
  rw [Measure.map_congr hae]
  have hm := Measure.infinitePi_map_pi (μ := fun _ : ℕ => commonBlockLaw ν L)
    (f := fun _ => pairTotal D) (fun _ => measurable_of_countable _)
  have hb := commonBlocks_map ν L hL he
  have hmb : Measurable (commonBlocks L) := measurable_regenerativeSequence _ _
    (measurable_firstCommonBlock L) (measurable_commonRestart L)
  let : IsProbabilityMeasure ((commonBlockLaw ν L).map (pairTotal D)) :=
    probabilityMeasure_map (measurable_of_countable _).aemeasurable
  calc
    _ = ((twoTapeLaw ν).map (commonBlocks L)).map
        (fun Z => ∑ i ∈ Finset.range r, pairTotal D (Z i)) := by
      rw [Measure.map_map (by fun_prop) hmb]
      rfl
    _ = _ := by
      rw [hb]
      have hh := congrArg (fun μ : Measure (ℕ → G) => μ.map (fun Z => ∑ i ∈ Finset.range r, Z i)) hm
      rw [Measure.map_map (by fun_prop) (by fun_prop),iid_sum_law] at hh
      exact hh
end SumCommon

end DirectionalZeroOne

end OAI

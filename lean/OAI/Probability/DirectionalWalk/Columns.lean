import OAI.Probability.DirectionalWalk.Escape

namespace OAI

open MeasureTheory ProbabilityTheory Filter Preorder
open scoped ENNReal BigOperators Topology

namespace DirectionalZeroOne

def axialRay {d : ℕ} (x : Site d) (e : Step d) : Path d :=
  fun n => x + n • stepVector e

lemma axialRay_zero {d : ℕ} (x : Site d) (e : Step d) : axialRay x e 0 = x := by
  simp [axialRay]

lemma axialRay_succ {d : ℕ} (x : Site d) (e : Step d) (n : ℕ) :
    axialRay x e (n+1) = axialRay x e n + stepVector e := by
  simp only [axialRay, succ_nsmul, add_assoc]

lemma axialRay_injective {d : ℕ} (x : Site d) (e : Step d) :
    Function.Injective (axialRay x e) := by
  intro n m h
  have hh := congr_fun h e.1
  cases hb : e.2 <;> simpa [axialRay, stepVector, hb] using hh

lemma height_nsmul {d : ℕ} (v : Fin d → ℝ) (x : Site d) (n : ℕ) :
    height v (n • x) = n * height v x := by
  induction n with
  | zero => simp [height_zero]
  | succ n hn => rw [succ_nsmul, height_add, hn, Nat.cast_add, Nat.cast_one]; ring

lemma height_axialRay {d : ℕ} (v : Fin d → ℝ) (x : Site d) (e : Step d) (n : ℕ) :
    height v (axialRay x e n) = height v x + n * height v (stepVector e) := by
  rw [axialRay, height_add, height_nsmul]

lemma pathWeight_axialRay {d : ℕ} (x : Site d) (e : Step d) (n : ℕ) (ω : Environment d) :
    pathWeight n (axialRay x e) ω =
      quenchedWeight (fun j : Fin n => axialRay x e j) (fun _ => e) ω := by
  simp only [pathWeight, axialRay_succ, entryWeight_step, quenchedWeight]
  exact (Fin.prod_univ_eq_prod_range (fun j => ENNReal.ofReal ((ω (axialRay x e j)).val e)) n).symm

lemma quenched_axialRay_pos {d : ℕ} (ω : Environment d)
    (hω : ∀ x e, 0 < (ω x).val e) (x : Site d) (e : Step d) (m : ℕ) :
    0 < quenchedKernel d (ω,x) (pathCylinder m (axialRay x e)) := by
  rw [quenchedKernel_cylinder, axialRay_zero, ite_eq_left rfl, pathWeight_axialRay]
  apply pos_iff_ne_zero.mpr
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  exact ne_of_gt (ENNReal.ofReal_pos.mpr (hω _ _))

lemma annealed_axialRay {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (x : Site d) (e : Step d) (m : ℕ) :
    annealed μ x (pathCylinder m (axialRay x e)) = meanStep μ e ^ m := by
  rw [annealed_cylinder, axialRay_zero, ite_eq_left rfl]
  simp_rw [pathWeight_axialRay]
  change wordWeight μ (fun j : Fin m => axialRay x e j) (fun _ => e) = _
  rw [fresh_word_weight μ (fun j : Fin m => axialRay x e j) (fun _ => e)
    ((axialRay_injective x e).comp Fin.val_injective)]
  simp

lemma quenched_prefix_tail_factor {d : ℕ} (ω : Environment d) (x : Site d)
    (n : ℕ) (γ : Path d) {E : Set (Path d)} (hE : MeasurableSet E) :
    quenchedKernel d (ω,x) (pathCylinder n γ ∩ tailPath n ⁻¹' E) =
      quenchedKernel d (ω,x) (pathCylinder n γ) * quenchedKernel d (ω,γ n) E := by
  rw [quenched_prefix_tail_apply _ _ _ _ hE, quenchedKernel_cylinder]

lemma annealed_disjoint_prefix_tail {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (x : Site d) (n m : ℕ) (γ δ : Path d) (hjoin : γ n = δ 0)
    (hdis : ∀ i < n, ∀ j < m, γ i ≠ δ j) :
    annealed μ x (pathCylinder n γ ∩ tailPath n ⁻¹' pathCylinder m δ) =
      annealed μ x (pathCylinder n γ) * annealed μ (γ n) (pathCylinder m δ) := by
  classical
  rw [annealed_apply μ x ((measurableSet_pathCylinder n γ).inter
    ((measurable_tailPath n) (measurableSet_pathCylinder m δ)))]
  simp_rw [quenched_prefix_tail_apply _ _ _ _ (measurableSet_pathCylinder m δ),
    quenchedKernel_cylinder, ite_eq_left hjoin]
  rw [annealed_cylinder, annealed_cylinder, ite_eq_left hjoin]
  by_cases hx : x = γ 0
  · simp only [ite_eq_left hx]
    exact path_weights_disjoint μ n m γ δ hdis
  · simp only [ite_eq_right hx, zero_mul, lintegral_zero]

def alwaysBelow {d : ℕ} (v : Fin d → ℝ) (b : ℝ) : Set (Path d) :=
  {X | ∀ n, height v (X n) ≤ b}

lemma measurableSet_alwaysBelow {d : ℕ} (v : Fin d → ℝ) (b : ℝ) :
    MeasurableSet (alwaysBelow v b) := by
  simp only [alwaysBelow, Set.ofPred_forall]
  exact MeasurableSet.iInter (fun n => measurableSet_le
    ((measurable_of_countable (height v)).comp (measurable_pi_apply n)) measurable_const)

def infiniteVisits {d : ℕ} (x : Site d) : Set (Path d) :=
  {X | ∀ N, ∃ n, N ≤ n ∧ X n = x}

lemma measurableSet_infiniteVisits {d : ℕ} (x : Site d) : MeasurableSet (infiniteVisits x) := by
  simp only [infiniteVisits, Set.ofPred_forall, Set.ofPred_exists, Set.ofPred_and]
  exact MeasurableSet.iInter (fun N => MeasurableSet.iUnion (fun n =>
    (MeasurableSet.const _).inter (measurableSet_eq_fun (measurable_pi_apply n) measurable_const)))

lemma quenched_bounded_infiniteVisits_null {d : ℕ} (ω : Environment d)
    (hω : ∀ x e, 0 < (ω x).val e) (y x : Site d) (v : Fin d → ℝ)
    (e : Step d) (he : 0 < height v (stepVector e)) (b : ℝ) :
    quenchedKernel d (ω,y) (alwaysBelow v b ∩ infiniteVisits x) = 0 := by
  obtain ⟨m,hm⟩ := exists_nat_gt ((b-height v x) / height v (stepVector e))
  have hcross : b < height v (axialRay x e m) := by
    rw [height_axialRay]
    have ht := (div_lt_iff₀ he).mp hm
    linarith
  let ν := quenchedKernel d (ω,y)
  let S := pathCylinder m (axialRay x e)
  let q := (quenchedKernel d (ω,x) S).toReal
  have hq : 0 < q := ENNReal.toReal_pos
    (ne_of_gt (quenched_axialRay_pos ω hω x e m)) (measure_ne_top _ _)
  apply null_of_prefix_contraction ν
    ((measurableSet_alwaysBelow v b).inter (measurableSet_infiniteVisits x)) (1-q) (by linarith)
  intro X hX
  apply (frequently_atTop.mpr hX.2).mono
  intro n hn
  refine real_contraction_of_disjoint_success ν (measurableSet_pathCylinder n X)
    ((measurable_tailPath n) (measurableSet_pathCylinder m (axialRay x e))) ?_ q ?_
  · apply Set.disjoint_left.mpr
    rintro Y ⟨hY,_⟩ ⟨_,hS⟩
    have hs := hS m le_rfl
    have hbound := hY.1 (n+m)
    change Y (n+m) = axialRay x e m at hs
    rw [hs] at hbound
    exact (not_le_of_gt hcross) hbound
  · change (ν (pathCylinder n X ∩ tailPath n ⁻¹' S)).toReal = _
    rw [quenched_prefix_tail_factor _ _ _ _ (measurableSet_pathCylinder m (axialRay x e)), hn,
      ENNReal.toReal_mul, mul_comm]
    rfl

lemma annealed_bounded_infiniteVisits_null {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (y x : Site d) (v : Fin d → ℝ)
    (e : Step d) (he : 0 < height v (stepVector e)) (b : ℝ) :
    annealed μ y (alwaysBelow v b ∩ infiniteVisits x) = 0 := by
  rw [annealed_apply μ y ((measurableSet_alwaysBelow v b).inter (measurableSet_infiniteVisits x))]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [all_rows_strictly_positive μ hell] with ω hω
  exact quenched_bounded_infiniteVisits_null ω hω y x v e he b

def column {d : ℕ} (c : Fin d) (x : Site d) : Site d := Function.update x c 0

lemma column_axialRay {d : ℕ} (x : Site d) (e : Step d) (n : ℕ) :
    column e.1 (axialRay x e n) = column e.1 x := by
  funext j
  by_cases hj : j = e.1
  · subst j; simp [column]
  · simp [column, hj, axialRay, stepVector]

lemma height_eq_column {d : ℕ} (v : Fin d → ℝ) (c : Fin d) (x : Site d) :
    height v x = height v (column c x) + (x c : ℝ) * v c := by
  have h : height v x - height v (column c x) = (x c : ℝ) * v c := by
    unfold height
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single c]
    · simp [column]
    · intro j _ hj; simp [column, hj]
    · simp
  linarith

lemma finite_column_band {d : ℕ} (v : Fin d → ℝ) (c : Fin d) (hv : v c ≠ 0)
    (y : Site d) (a b : ℝ) :
    {x : Site d | column c x = column c y ∧ a ≤ height v x ∧ height v x ≤ b}.Finite := by
  let S := {x : Site d | column c x = column c y ∧ a ≤ height v x ∧ height v x ≤ b}
  have hi : Set.InjOn (fun x : Site d => x c) S := by
    intro x hx z hz h
    funext j
    by_cases hj : j = c
    · simpa [hj] using h
    · have hh := congr_fun (hx.1.trans hz.1.symm) j
      simpa [column, hj] using hh
  apply Set.Finite.of_finite_image (hi := hi)
  rcases lt_or_gt_of_ne hv with hneg | hpos
  · apply (Set.finite_Icc ⌈(b-height v (column c y))/v c⌉ ⌊(a-height v (column c y))/v c⌋).subset
    rintro _ ⟨x,hx,rfl⟩
    have hh := height_eq_column v c x
    rw [hx.1] at hh
    constructor
    · apply Int.ceil_le.mpr
      apply (div_le_iff_of_neg hneg).mpr
      linarith [hx.2.2]
    · apply Int.le_floor.mpr
      apply (le_div_iff_of_neg hneg).mpr
      linarith [hx.2.1]
  · apply (Set.finite_Icc ⌈(a-height v (column c y))/v c⌉ ⌊(b-height v (column c y))/v c⌋).subset
    rintro _ ⟨x,hx,rfl⟩
    have hh := height_eq_column v c x
    rw [hx.1] at hh
    constructor
    · apply Int.ceil_le.mpr
      apply (div_le_iff₀ hpos).mpr
      linarith [hx.2.1]
    · apply Int.le_floor.mpr
      apply (le_div_iff₀ hpos).mpr
      linarith [hx.2.2]

def freshColumnTime {d : ℕ} (v : Fin d → ℝ) (e : Step d) (a : ℝ) (X : Path d) (n : ℕ) : Prop :=
  a ≤ height v (X n) ∧ ∀ i < n, column e.1 (X i) = column e.1 (X n) → height v (X i) < a

lemma measurableSet_freshColumnTime {d : ℕ} (v : Fin d → ℝ) (e : Step d) (a : ℝ) (n : ℕ) :
    MeasurableSet {X : Path d | freshColumnTime v e a X n} := by
  unfold freshColumnTime
  simp only [Set.ofPred_and, Set.ofPred_forall]
  refine (measurableSet_le measurable_const
    ((measurable_of_countable (height v)).comp (measurable_pi_apply n))).inter ?_
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro _
  simp only [imp_iff_not_or, Set.ofPred_or]
  exact ((measurableSet_eq_fun
    ((measurable_of_countable (column e.1)).comp (measurable_pi_apply i))
    ((measurable_of_countable (column e.1)).comp (measurable_pi_apply n))).compl).union
    (measurableSet_lt ((measurable_of_countable (height v)).comp (measurable_pi_apply i)) measurable_const)

lemma measurableSet_frequently_nat {Ω : Type*} [MeasurableSpace Ω] (P : ℕ → Ω → Prop)
    (hP : ∀ n, MeasurableSet {x | P n x}) :
    MeasurableSet {x | ∃ᶠ n in atTop, P n x} := by
  simp only [frequently_atTop, Set.ofPred_forall, Set.ofPred_exists, Set.ofPred_and]
  exact MeasurableSet.iInter (fun N => MeasurableSet.iUnion (fun n =>
    (MeasurableSet.const _).inter (hP n)))

lemma annealed_bounded_freshColumns_null {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (y : Site d) (v : Fin d → ℝ)
    (e : Step d) (he : 0 < height v (stepVector e)) (a b : ℝ) :
    annealed μ y (alwaysBelow v b ∩ {X | ∃ᶠ n in atTop, freshColumnTime v e a X n}) = 0 := by
  obtain ⟨m,hm⟩ := exists_nat_gt ((b-a) / height v (stepVector e))
  let q := (meanStep μ e ^ m).toReal
  have hq : 0 < q := ENNReal.toReal_pos
    (pow_ne_zero _ (ne_of_gt (meanStep_pos μ hell e)))
    (ne_of_lt (lt_of_le_of_lt (pow_le_one₀ zero_le (meanStep_le_one μ e)) ENNReal.one_lt_top))
  apply null_of_prefix_contraction (annealed μ y)
    ((measurableSet_alwaysBelow v b).inter (measurableSet_frequently_nat _
      (measurableSet_freshColumnTime v e a))) (1-q) (by linarith)
  intro X hX
  apply hX.2.mono
  intro n hn
  have hcross : b < height v (axialRay (X n) e m) := by
    rw [height_axialRay]
    have ht := (div_lt_iff₀ he).mp hm
    linarith [hn.1]
  have hdis : ∀ i < n, ∀ j < m, X i ≠ axialRay (X n) e j := by
    intro i hi j _ hij
    have hcol : column e.1 (X i) = column e.1 (X n) := by rw [hij, column_axialRay]
    have hlow := hn.2 i hi hcol
    rw [hij, height_axialRay] at hlow
    have hnonneg : 0 ≤ (j : ℝ) * height v (stepVector e) := mul_nonneg (Nat.cast_nonneg _) he.le
    linarith [hn.1]
  refine real_contraction_of_disjoint_success (annealed μ y) (measurableSet_pathCylinder n X)
    ((measurable_tailPath n) (measurableSet_pathCylinder m (axialRay (X n) e))) ?_ q ?_
  · apply Set.disjoint_left.mpr
    rintro Y ⟨hY,_⟩ ⟨_,hS⟩
    have hs := hS m le_rfl
    have hbound := hY.1 (n+m)
    change Y (n+m) = axialRay (X n) e m at hs
    rw [hs] at hbound
    exact (not_le_of_gt hcross) hbound
  · change (annealed μ y (pathCylinder n X ∩ tailPath n ⁻¹'
        pathCylinder m (axialRay (X n) e))).toReal = _
    rw [annealed_disjoint_prefix_tail μ y n m X (axialRay (X n) e)
      (axialRay_zero (X n) e).symm hdis, annealed_axialRay, ENNReal.toReal_mul, mul_comm]
    rfl

lemma recurrent_or_freshColumns {d : ℕ} (v : Fin d → ℝ) (e : Step d) (hv : v e.1 ≠ 0)
    (a b : ℝ) (X : Path d) (hb : X ∈ alwaysBelow v b)
    (ha : ∃ᶠ n in atTop, a ≤ height v (X n)) :
    (∃ x, X ∈ infiniteVisits x) ∨ ∃ᶠ n in atTop, freshColumnTime v e a X n := by
  classical
  by_cases hf : ∃ᶠ n in atTop, freshColumnTime v e a X n
  · exact Or.inr hf
  left
  obtain ⟨N,hN⟩ := eventually_atTop.mp (not_frequently.mp hf)
  let F : Set (Site d) := ⋃ i ∈ Finset.range N,
    {x | column e.1 x = column e.1 (X i) ∧ a ≤ height v x ∧ height v x ≤ b}
  have hF : F.Finite := (Finset.finite_toSet (Finset.range N)).biUnion
    (fun i _ => finite_column_band v e.1 hv (X i) a b)
  have hmem (n : ℕ) (hn : a ≤ height v (X n)) : X n ∈ F := by
    have hex : ∃ i, a ≤ height v (X i) ∧ column e.1 (X i) = column e.1 (X n) := ⟨n,hn,rfl⟩
    let k := Nat.find hex
    have hk := Nat.find_spec hex
    have helig : freshColumnTime v e a X k := by
      refine ⟨hk.1, fun i hi hcol => ?_⟩
      by_contra h
      exact Nat.find_min hex hi ⟨le_of_not_gt h, hcol.trans hk.2⟩
    have hkN : k < N := lt_of_not_ge (fun h => hN k h helig)
    exact Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr
      ⟨Finset.mem_range.mpr hkN, hk.2.symm, hn, hb n⟩⟩
  have hfreq : ∃ᶠ n in atTop, ∃ x ∈ F, X n = x := ha.mono (fun n hn => ⟨X n,hmem n hn,rfl⟩)
  obtain ⟨x,_,hx⟩ := hF.frequently_exists.mp hfreq
  exact ⟨x, frequently_atTop.mp hx⟩

lemma height_stepVector {d : ℕ} (v : Fin d → ℝ) (e : Step d) :
    height v (stepVector e) = if e.2 then v e.1 else -v e.1 := by
  classical
  simp [height, stepVector, ite_mul]

lemma annealed_bounded_band_null {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (y : Site d) (v : Fin d → ℝ)
    (e : Step d) (he : 0 < height v (stepVector e)) (a b : ℝ) :
    annealed μ y (alwaysBelow v b ∩ {X | ∃ᶠ n in atTop, a ≤ height v (X n)}) = 0 := by
  have hv : v e.1 ≠ 0 := by
    intro hz
    rw [height_stepVector, hz] at he
    split_ifs at he <;> simp_all
  apply measure_mono_null (t := (⋃ x, alwaysBelow v b ∩ infiniteVisits x) ∪
    (alwaysBelow v b ∩ {X | ∃ᶠ n in atTop, freshColumnTime v e a X n}))
  · rintro X ⟨hX,hfreq⟩
    rcases recurrent_or_freshColumns v e hv a b X hX hfreq with ⟨x,hx⟩ | hf
    · exact Or.inl (Set.mem_iUnion.mpr ⟨x,hX,hx⟩)
    · exact Or.inr ⟨hX,hf⟩
  · rw [measure_union_null_iff]
    exact ⟨measure_iUnion_null (fun x => annealed_bounded_infiniteVisits_null μ hell y x v e he b),
      annealed_bounded_freshColumns_null μ hell y v e he a b⟩

lemma exists_positive_step {d : ℕ} (v : Fin d → ℝ) (hv : v ≠ 0) :
    ∃ e : Step d, 0 < height v (stepVector e) := by
  have hex : ∃ c, v c ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  obtain ⟨c,hc⟩ := hex
  rcases lt_or_gt_of_ne hc with hneg | hpos
  · exact ⟨(c,false), by simpa [height_stepVector] using neg_pos.mpr hneg⟩
  · exact ⟨(c,true), by simpa [height_stepVector] using hpos⟩

lemma finite_supremum {d : ℕ} (μ : Measure (Row d)) [IsProbabilityMeasure μ]
    (hell : StrictEllipticity μ) (y : Site d) (v : Fin d → ℝ) (hv : v ≠ 0) :
    ∀ᵐ X ∂annealed μ y, (∃ b : ℝ, ∀ n, height v (X n) ≤ b) →
      Tendsto (fun n => height v (X n)) atTop atBot := by
  obtain ⟨e,he⟩ := exists_positive_step v hv
  have hnull (b a : ℤ) : ∀ᵐ X ∂annealed μ y,
      ¬(X ∈ alwaysBelow v (b : ℝ) ∧ ∃ᶠ n in atTop, (a : ℝ) ≤ height v (X n)) := by
    exact (measure_eq_zero_iff_ae_notMem).mp (annealed_bounded_band_null μ hell y v e he a b)
  filter_upwards [ae_all_iff.mpr (fun b => ae_all_iff.mpr (hnull b))] with X hX
  rintro ⟨b,hb⟩
  have hb' : X ∈ alwaysBelow v (⌈b⌉ : ℝ) := fun n => (hb n).trans (Int.le_ceil b)
  apply tendsto_atBot.mpr
  intro a
  have hnf : ¬∃ᶠ n in atTop, (⌊a⌋ : ℝ) ≤ height v (X n) := fun h => hX ⌈b⌉ ⌊a⌋ ⟨hb',h⟩
  filter_upwards [not_frequently.mp hnf] with n hn
  exact (lt_of_not_ge hn).le.trans (Int.floor_le a)

end DirectionalZeroOne

end OAI

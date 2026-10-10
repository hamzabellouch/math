import OAI.Analysis.RotationWeights.Thresholds

namespace OAI

noncomputable section

namespace CircleSampling

universe uX

open MeasureTheory
open scoped ENNReal NNReal ComplexInnerProductSpace BigOperators
open MeasureTheory Filter Set Submodule
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexInnerProductSpace
open MeasureTheory Filter Set
open scoped ComplexInnerProductSpace
open MeasureTheory Filter Set
open Set
open scoped ComplexInnerProductSpace
open Set
open scoped ComplexInnerProductSpace
open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexConjugate
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
open Filter Set
open scoped Topology
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped BigOperators ENNReal Classical
open Filter Set
open scoped Topology
open Set MeasureTheory
open scoped ENNReal Classical
open Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Topology
open scoped BigOperators
open scoped BigOperators
open Set
open Set
open Set
open Set MeasureTheory Filter
open scoped BigOperators ENNReal Topology Classical
open MeasureTheory Set Filter
open scoped ENNReal Topology
open MeasureTheory Set
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction
open MeasureTheory Set Filter Topology TopologicalSpace
open MeasureTheory Set
open scoped ENNReal BigOperators Classical
open MeasureTheory Set
open scoped BigOperators ENNReal Classical
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
open Set MeasureTheory Topology
open scoped symmDiff
open MeasureTheory Set
open scoped ENNReal BigOperators
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Set
open scoped BigOperators ENNReal

section
open CircleModel Set
open scoped BigOperators

lemma sum_drop_prefix (j : ℕ) : (∑ i∈Finset.range (blockEnd j),coordinateDrop i)=(scaleState j).1.E := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change (∑ i∈Finset.range (blockEnd j+blockLength j),coordinateDrop i)=(scaleState j).1.E+dropSize j*blockLength j
    rw [Finset.sum_range_add,ih]
    congr 1
    have he (i : ℕ) (hi : i∈Finset.range (blockLength j)) : coordinateDrop (blockEnd j+i)=dropSize j := by
      change dropSize (blocks.number (blockEnd j+i))=dropSize j
      congr 1
      apply blocks.number_eq (by change blockEnd j ≤ blockEnd j+i; omega)
      change blockEnd j+i<blockEnd j+blockLength j
      exact Nat.add_lt_add_left (Finset.mem_range.mp hi) _
    rw [Finset.sum_congr rfl he]
    simp [mul_comm]

lemma floor_abs_bound (k : ℤ) (K : ℕ) (hk : |(k:ℝ)| ≤ (K:ℝ)) (x : CircleX) (i : ℕ) :
    |(floorTerm modelFrequency modelAngle k x i:ℝ)| ≤ (K:ℝ)+1 := by
  let z := Xi modelFrequency i x+(k:ℝ)*beta modelFrequency modelAngle i
  have hx := repr_mem (modelFrequency i • x)
  have hb := repr_mem (modelFrequency i • modelAngle)
  change 0 ≤ Xi modelFrequency i x ∧ Xi modelFrequency i x<1 at hx
  change 0 ≤ beta modelFrequency modelAngle i ∧ beta modelFrequency modelAngle i<1 at hb
  have hp : |(k:ℝ)*beta modelFrequency modelAngle i| ≤ (K:ℝ) := by
    rw [abs_mul,abs_of_nonneg hb.1]
    exact (mul_le_mul_of_nonneg_left hb.2.le (abs_nonneg _)).trans (by simpa using hk)
  have hzlo : -(K:ℝ) ≤ z := by have hh := (abs_le.mp hp).1; dsimp [z]; linarith
  have hzhi : z ≤ (K:ℝ)+1 := by have hh := (abs_le.mp hp).2; dsimp [z]; linarith
  change |(⌊z⌋:ℝ)| ≤ _
  exact abs_le.mpr ⟨by linarith [Int.lt_floor_add_one z],(Int.floor_le z).trans hzhi⟩

lemma exponent_prefix_bound (j : ℕ) (k : ℤ) (x : CircleX) (hk : |(k:ℝ)| ≤ (polynomialWindow j:ℝ))
    (ht : ∀ i,blockEnd j ≤ i → floorTerm modelFrequency modelAngle k x i=0) :
    |exponent modelFrequency modelAngle coordinateDrop k x| ≤ ((polynomialWindow j:ℝ)+1)*(scaleState j).1.E := by
  have he : exponent modelFrequency modelAngle coordinateDrop k x =
      ∑ i∈Finset.range (blockEnd j),coordinateDrop i*(floorTerm modelFrequency modelAngle k x i:ℝ) := by
    apply tsum_eq_sum
    intro i hi
    rw [ht i (by simpa using hi),Int.cast_zero,mul_zero]
  rw [he]
  calc
    _ ≤ ∑ i∈Finset.range (blockEnd j),|coordinateDrop i*(floorTerm modelFrequency modelAngle k x i:ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i∈Finset.range (blockEnd j),coordinateDrop i*((polynomialWindow j:ℝ)+1) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul,abs_of_nonneg (show 0 ≤ coordinateDrop i from dropSize_nonneg (coordinateBlock i))]
      exact mul_le_mul_of_nonneg_left (floor_abs_bound k _ hk x i) (dropSize_nonneg (coordinateBlock i))
    _ = _ := by rw [←Finset.sum_mul,sum_drop_prefix]; ring

def coefficientCap (j : ℕ) : ℝ := Real.exp (((polynomialWindow j:ℝ)+1)*(scaleState j).1.E)
lemma coefficientCap_ge_one (j : ℕ) : 1 ≤ coefficientCap j := Real.one_le_exp (mul_nonneg (by positivity) (scaleState j).2.Ege)
lemma modelF_prefix_bound (j : ℕ) (k : ℤ) {x : CircleX} (hx : x∈modelGood)
    (hk : |(k:ℝ)| ≤ (polynomialWindow j:ℝ))
    (ht : ∀ i,blockEnd j ≤ i → floorTerm modelFrequency modelAngle k x i=0) :
    modelF k x≤coefficientCap j ∧ 1/modelF k x≤coefficientCap j := by
  have hb := exponent_prefix_bound j k x hk ht
  change x∈good modelFrequency modelAngle at hx
  simp only [modelF,cocycle,ite_eq_left hx]
  constructor
  · apply Real.exp_le_exp.mpr
    have hh := (abs_le.mp hb).1
    linarith
  · rw [one_div,←Real.exp_neg,neg_neg]
    apply Real.exp_le_exp.mpr
    exact le_of_abs_le hb
end

section
open CircleModel MeasureTheory Set Filter
open scoped Topology ENNReal BigOperators

def futureBad (j : ℕ) (e : Bool) : Set CircleX := ⋃ s : ℕ, ⋃ a : Fin (blockLength (j+1+s)),
  {x | if e then Xi modelFrequency (blocks.equiv ⟨j+1+s,a⟩) x < 2*(polynomialWindow j:ℝ)/blockScale (j+1+s)
  else 1-2*(polynomialWindow j:ℝ)/blockScale (j+1+s) ≤ Xi modelFrequency (blocks.equiv ⟨j+1+s,a⟩) x}
lemma futureBad_measurable (j : ℕ) (e : Bool) : MeasurableSet (futureBad j e) := by
  apply MeasurableSet.iUnion; intro s
  apply MeasurableSet.iUnion; intro a
  cases e
  · exact measurableSet_le measurable_const (measurable_Xi _ _)
  · exact measurableSet_lt (measurable_Xi _ _) measurable_const
lemma futureBad_bound (j : ℕ) (e : Bool) : volume.real (futureBad j e) ≤ 4*(polynomialWindow j:ℝ)/(polynomialWindow (j+1):ℝ) := by
  have hq : ∀ i,modelFrequency i≠0 := fun i => (frequency_pos (i+1)).ne'
  have hblock (s : ℕ) : volume (⋃ a : Fin (blockLength (j+1+s)),
      {x : CircleX | if e then Xi modelFrequency (blocks.equiv ⟨j+1+s,a⟩) x < 2*(polynomialWindow j:ℝ)/blockScale (j+1+s)
      else 1-2*(polynomialWindow j:ℝ)/blockScale (j+1+s) ≤ Xi modelFrequency (blocks.equiv ⟨j+1+s,a⟩) x}) ≤ ENNReal.ofReal (2*(polynomialWindow j:ℝ)/(polynomialWindow (j+1+s):ℝ)) := by
    have hm : (blockLength (j+1+s):ℝ)≠0 := (Nat.cast_pos.mpr (scaleStep (j+1+s)).mpos).ne'
    apply (measure_iUnion_le_ofReal_tsum volume _ (fun _ => 2*(polynomialWindow j:ℝ)/blockScale (j+1+s))
      (fun _ => div_nonneg (by positivity) (blockScale_pos _).le) (Summable.of_finite) ?_).trans
    · apply ENNReal.ofReal_le_ofReal
      rw [tsum_fintype]
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,blockScale]
      field_simp
      rfl
    · intro a
      cases e
      · exact measure_Xi_upper hq _ _
      · exact measure_Xi_lower hq _ _
  have hs : Summable (fun s => 2*(polynomialWindow j:ℝ)/(polynomialWindow (j+1+s):ℝ)) := by
    simpa only [div_eq_mul_inv,one_mul] using (summable_window_inverse (j+1)).mul_left (2*(polynomialWindow j:ℝ))
  have hm := measure_iUnion_le_ofReal_tsum volume _ _ (fun s => by positivity) hs hblock
  apply (ENNReal.toReal_le_of_le_ofReal (tsum_nonneg (fun _ => by positivity)) hm).trans
  simp_rw [div_eq_mul_inv]
  rw [tsum_mul_left]
  calc
    _ ≤ 2*(polynomialWindow j:ℝ)*(2/(polynomialWindow (j+1):ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [one_div] using tsum_window_inverse (j+1)
    _ = _ := by ring
lemma window_div_next (j : ℕ) : (polynomialWindow j:ℝ)/(polynomialWindow (j+1):ℝ) ≤ 1/(blockLength j:ℝ) := by
  apply le_trans _ (sampleBound_div_window j)
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have hm : (1:ℝ) ≤ blockLength j := by exact_mod_cast (scaleStep j).mpos
  have hm200 : (200:ℝ) ≤ blockLength j := by exact_mod_cast blockLength_ge j
  apply (Nat.cast_le.mpr (polynomialWindow_le_length j)).trans
  calc
    (blockLength j:ℝ) = (blockLength j:ℝ)^(1:ℝ) := (Real.rpow_one _).symm
    _ ≤ sampleBound j := Real.rpow_le_rpow_of_exponent_le hm (by linarith)
lemma futureBad_tendsto (e : Bool) : Tendsto (fun j => volume.real (futureBad j e)) atTop (𝓝 0) := by
  have hupper (j : ℕ) : volume.real (futureBad j e) ≤ 4/(blockLength j:ℝ) := by
    apply (futureBad_bound j e).trans
    have h := mul_le_mul_of_nonneg_left (window_div_next j) (by norm_num : (0:ℝ) ≤ 4)
    simpa only [div_eq_mul_inv,mul_assoc,mul_one,one_mul] using h
  apply squeeze_zero (fun _ => measureReal_nonneg) hupper
  simpa only [div_eq_mul_inv,one_mul,mul_zero,Function.comp_def] using
    ((tendsto_one_div_atTop_nhds_zero_nat (𝕜:=ℝ)).comp blockLength_strictMono.tendsto_atTop).const_mul 4

lemma measure_small_positive_tendsto {X : Type uX} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (r : X → ℝ) (hr : Measurable r) (hp : ∀ᵐ x ∂μ,0<r x) :
    Tendsto (fun j : ℕ => μ.real {x | r x<1/((j:ℝ)+1)}) atTop (𝓝 0) := by
  have hm : Antitone (fun j : ℕ => {x | r x<1/((j:ℝ)+1)}) := by
    intro j k hjk x hx
    change r x<1/((k:ℝ)+1) at hx
    change r x<1/((j:ℝ)+1)
    exact hx.trans_le (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hjk 1))
  have hi : μ (⋂ j : ℕ,{x | r x<1/((j:ℝ)+1)})=0 := by
    apply measure_mono_null _ (ae_iff.mp hp)
    intro x hx
    simp only [mem_iInter,mem_ofPred_eq] at hx ⊢
    by_contra! hp'
    have he : ∀ᶠ j : ℕ in atTop,1/((j:ℝ)+1)<r x := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).eventually (gt_mem_nhds hp')
    obtain ⟨j,hj⟩ := he.exists
    exact (hx j).not_gt hj
  have hh := tendsto_measure_iInter_atTop (μ:=μ) (fun j => (measurableSet_lt hr measurable_const).nullMeasurableSet) hm ⟨0,measure_ne_top _ _⟩
  rw [hi] at hh
  simpa only [Function.comp_def,ENNReal.toReal_zero,Measure.real] using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hh
end

section
open MeasureTheory Set Filter CircleCoupling
open scoped Topology ENNReal

def endpointBad (r : CircleX → ℝ) (j : ℕ) (e : Bool) : Set CircleX :=
  futureBad j e ∪ {x | (if e then 1-r x else r x)<1/((j:ℝ)+1)}
def projectionEvent (r : CircleX → ℝ) (j : ℕ) : Set ActualSamples :=
  stageTagEvent j \ (firstEndpoint ⁻¹' endpointBad r j false ∪ lastEndpoint ⁻¹' endpointBad r j true)
lemma endpointBad_measurable {r : CircleX → ℝ} (hr : Measurable r) (j : ℕ) (e : Bool) : MeasurableSet (endpointBad r j e) := by
  apply (futureBad_measurable j e).union
  apply measurableSet_lt _ measurable_const
  cases e
  · exact hr
  · exact measurable_const.sub hr
lemma projectionEvent_measurable {r : CircleX → ℝ} (hr : Measurable r) (j : ℕ) : MeasurableSet (projectionEvent r j) :=
  (stageTagEvent_measurable j).diff (((endpointBad_measurable hr j false).preimage firstEndpoint_measurable).union
    ((endpointBad_measurable hr j true).preimage lastEndpoint_measurable))
lemma endpointBad_tendsto {r : CircleX → ℝ} (hr : Measurable r) (hp : ∀ᵐ x,0<r x ∧ r x<1) (e : Bool) :
    Tendsto (fun j => volume.real (endpointBad r j e)) atTop (𝓝 0) := by
  have hpos : ∀ᵐ x,0<(if e then 1-r x else r x) := by
    filter_upwards [hp] with x hx
    cases e <;> simp only [Bool.false_eq_true,↓reduceIte] <;> linarith [hx.1,hx.2]
  have hm : Measurable (fun x => if e then 1-r x else r x) := by cases e <;> first | exact hr | exact measurable_const.sub hr
  apply squeeze_zero (fun _ => measureReal_nonneg) (fun j => measureReal_union_le _ _) ?_
  simpa using (futureBad_tendsto e).add (measure_small_positive_tendsto volume _ hm hpos)
lemma endpointBad_loss_tendsto {r : CircleX → ℝ} (hr : Measurable r) (hp : ∀ᵐ x,0<r x ∧ r x<1) (e : Bool) :
    Tendsto (fun j => (actualSystem.probability (stageTagged j)).real ((actualSystem.endpoint (fun _ => e)) ⁻¹' endpointBad r j e)) atTop (𝓝 0) := by
  apply squeeze_zero (fun _ => measureReal_nonneg) (fun j => actual_hybrid_bound j (fun _ => e) _ (endpointBad_measurable hr j e)) ?_
  simpa using ((Real.continuous_sqrt.tendsto 0).comp (endpointBad_tendsto hr hp e)).const_mul marginalConstant
lemma projectionEvent_mass {r : CircleX → ℝ} (hr : Measurable r) (hp : ∀ᵐ x,0<r x ∧ r x<1) :
    ∀ᶠ j in atTop, Real.exp (-86)/2 ≤ (actualSystem.probability (stageTagged j)).real (projectionEvent r j) := by
  have hl : Tendsto (fun j => (actualSystem.probability (stageTagged j)).real (firstEndpoint ⁻¹' endpointBad r j false)+
      (actualSystem.probability (stageTagged j)).real (lastEndpoint ⁻¹' endpointBad r j true)) atTop (𝓝 0) := by
    simpa only [add_zero,firstEndpoint,lastEndpoint] using (endpointBad_loss_tendsto hr hp false).add (endpointBad_loss_tendsto hr hp true)
  have he := hl.eventually (gt_mem_nhds (by positivity : (0:ℝ)<Real.exp (-86)/2))
  filter_upwards [he] with j hj
  have hm := stageTagEvent_mass j
  have hd : (actualSystem.probability (stageTagged j)).real (stageTagEvent j)-
      (actualSystem.probability (stageTagged j)).real (firstEndpoint ⁻¹' endpointBad r j false ∪ lastEndpoint ⁻¹' endpointBad r j true) ≤
      (actualSystem.probability (stageTagged j)).real (projectionEvent r j) := le_measureReal_sdiff
  have hu := measureReal_union_le (μ:=actualSystem.probability (stageTagged j))
    (firstEndpoint ⁻¹' endpointBad r j false) (lastEndpoint ⁻¹' endpointBad r j true)
  linarith
lemma projectionEvent_mem {r : CircleX → ℝ} {j : ℕ} {ω : ActualSamples} (hω : ω∈projectionEvent r j) :
    ω∈stageTagEvent j ∧ firstEndpoint ω∉futureBad j false ∧ lastEndpoint ω∉futureBad j true ∧
    1/((j:ℝ)+1) ≤ r (firstEndpoint ω) ∧ 1/((j:ℝ)+1) ≤ 1-r (lastEndpoint ω) := by
  have h := hω.2
  simp only [Set.mem_union,Set.mem_preimage,endpointBad,Set.mem_ofPred_eq,Bool.false_eq_true,↓reduceIte,not_or,not_lt] at h
  exact ⟨hω.1,h.1.1,h.2.1,h.1.2,h.2.2⟩
end

open MeasureTheory Set CircleCoupling CircleDigits CircleModel
open scoped ENNReal

lemma not_futureBad_iff (j s : ℕ) (hjs : j<s) (a : Fin (blockLength s)) (x : CircleX) (e : Bool)
    (hx : x∉futureBad j e) :
    if e then 2*(polynomialWindow j:ℝ)/blockScale s ≤ Xi modelFrequency (blocks.equiv ⟨s,a⟩) x
    else Xi modelFrequency (blocks.equiv ⟨s,a⟩) x<1-2*(polynomialWindow j:ℝ)/blockScale s := by
  obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le (by omega : j+1 ≤ s)
  have hh : ¬(if e then Xi modelFrequency (blocks.equiv ⟨j+1+t,a⟩) x<2*(polynomialWindow j:ℝ)/blockScale (j+1+t)
      else 1-2*(polynomialWindow j:ℝ)/blockScale (j+1+t) ≤ Xi modelFrequency (blocks.equiv ⟨j+1+t,a⟩) x) := by
    intro h
    apply hx
    exact mem_iUnion.mpr ⟨t,mem_iUnion.mpr ⟨a,h⟩⟩
  cases e <;> simpa only [Bool.false_eq_true,↓reduceIte,not_lt,not_le] using hh

lemma event_tail_margins {r : CircleX → ℝ} (j : ℕ) {ω : ActualSamples}
    (hω : ω∈regularSamples) (he : ω∈projectionEvent r j) (s : ℕ) (hjs : j ≤ s) (a : Fin (blockLength s)) :
    Xi modelFrequency (blocks.equiv ⟨s,a⟩) (firstEndpoint ω)<1-2*(polynomialWindow j:ℝ)/blockScale s ∧
    2*(polynomialWindow j:ℝ)/blockScale s ≤ Xi modelFrequency (blocks.equiv ⟨s,a⟩) (lastEndpoint ω) := by
  have hh := projectionEvent_mem he
  rcases hjs.eq_or_lt with rfl | hjs
  · have hi : blocks.equiv ⟨j,a⟩+1∈blockCoordinates j := by
      simp only [blockCoordinates,Finset.mem_Ico]
      change blockEnd j+1 ≤ blockEnd j+a.val+1 ∧ blockEnd j+a.val+1<blockEnd (j+1)+1
      have hs := blocks.step j
      change blockEnd (j+1)=blockEnd j+blockLength j at hs
      have ha := a.isLt
      omega
    have hm := (stageTagEvent_margins j hω.1 hh.1).2 _ hi
    have hx := (digit_interval actualSystem.radix_ge_two (fun i => (ω i).2.1) hω.2.2.2.1 (blocks.equiv ⟨j,a⟩+1)).2
    have hy := (digit_interval actualSystem.radix_ge_two (fun i => (ω i).2.2) hω.2.2.2.2 (blocks.equiv ⟨j,a⟩+1)).1
    rw [(actual_Xi_tail hω _).1,(actual_Xi_tail hω _).2]
    have hr : 2*(polynomialWindow j:ℝ)/blockScale j=2/(blockLength j:ℝ) := by
      have hK : (polynomialWindow j:ℝ)≠0 := (Nat.cast_pos.mpr (polynomialWindow_pos j)).ne'
      unfold blockScale; field_simp
    rw [hr]
    exact ⟨hx.trans_le hm.1,hm.2.trans hy⟩
  · exact ⟨not_futureBad_iff j s hjs a _ false hh.2.1,not_futureBad_iff j s hjs a _ true hh.2.2.1⟩

lemma event_floor_tail {r : CircleX → ℝ} (j : ℕ) {ω : ActualSamples}
    (hω : ω∈regularSamples) (he : ω∈projectionEvent r j) (k : ℤ)
    (hk0 : 0 ≤ k) (hk : k ≤ (polynomialWindow j:ℤ)) (n : ℕ) (hn : blockEnd j ≤ n) :
    floorTerm modelFrequency modelAngle k (firstEndpoint ω) n=0 ∧
    floorTerm modelFrequency modelAngle (-k) (lastEndpoint ω) n=0 := by
  obtain ⟨⟨s,a⟩,rfl⟩ := blocks.equiv.surjective n
  change Fin (blockLength s) at a
  have hjs : j ≤ s := by
    by_contra! hsj
    have hs := blocks.strictMono.monotone (by omega : s+1 ≤ j)
    have ha := a.isLt
    have ht := blocks.step s
    change blockEnd (s+1) ≤ blockEnd j at hs
    change blockEnd (s+1)=blockEnd s+blockLength s at ht
    change blockEnd j ≤ blockEnd s+a.val at hn
    omega
  have hm := event_tail_margins j hω he s hjs a
  have hb := coordinatePhase_bounds (blocks.equiv ⟨s,a⟩)
  rw [block_number_equiv s a] at hb
  have hk0' : (0:ℝ) ≤ k := by exact_mod_cast hk0
  have hk' : (k:ℝ) ≤ polynomialWindow j := by exact_mod_cast hk
  have hmul0 : 0 ≤ (k:ℝ)*coordinatePhase (blocks.equiv ⟨s,a⟩) := mul_nonneg hk0' (coordinatePhase_pos _).le
  have hmul : (k:ℝ)*coordinatePhase (blocks.equiv ⟨s,a⟩) ≤ 2*(polynomialWindow j:ℝ)/blockScale s := by
    calc
      _ ≤ (polynomialWindow j:ℝ)*(2/blockScale s) := mul_le_mul hk' hb.2.le (coordinatePhase_pos _).le (Nat.cast_nonneg _)
      _ = _ := by ring
  have hx := repr_mem (modelFrequency (blocks.equiv ⟨s,a⟩) • firstEndpoint ω)
  have hy := repr_mem (modelFrequency (blocks.equiv ⟨s,a⟩) • lastEndpoint ω)
  change 0 ≤ Xi modelFrequency _ (firstEndpoint ω) ∧ Xi modelFrequency _ (firstEndpoint ω)<1 at hx
  change 0 ≤ Xi modelFrequency _ (lastEndpoint ω) ∧ Xi modelFrequency _ (lastEndpoint ω)<1 at hy
  simp only [floorTerm,model_beta,Int.cast_neg]
  constructor <;> apply Int.floor_eq_iff.mpr <;> norm_num only [Int.cast_zero,zero_add] <;>
    constructor <;> nlinarith [hm.1,hm.2]

lemma event_window_bounds {r : CircleX → ℝ} (j : ℕ) {ω : ActualSamples}
    (hω : ω∈regularSamples) (he : ω∈projectionEvent r j) (k : ℤ)
    (hk : |k| ≤ (polynomialWindow j:ℤ)) :
    1/modelF k (firstEndpoint ω) ≤ coefficientCap j ∧ modelF (-k) (lastEndpoint ω) ≤ coefficientCap j := by
  have hk' : |(k:ℝ)| ≤ (polynomialWindow j:ℝ) := by exact_mod_cast hk
  by_cases hk0 : 0 ≤ k
  · have hb := event_floor_tail j hω he k hk0 (le_trans (le_abs_self _) hk)
    exact ⟨(modelF_prefix_bound j k hω.2.1 hk' (fun i hi => (hb i hi).1)).2,
      (modelF_prefix_bound j (-k) hω.2.2.1 (by simpa using hk') (fun i hi => (hb i hi).2)).1⟩
  · have hx : 1 ≤ modelF k (firstEndpoint ω) := by
      rw [←modelF_zero (firstEndpoint ω)]
      exact modelF_antitone _ (by omega)
    have hy : modelF (-k) (lastEndpoint ω) ≤ 1 := by
      rw [←modelF_zero (lastEndpoint ω)]
      exact modelF_antitone _ (by omega)
    exact ⟨((div_le_one (modelF_pos _ _)).mpr hx).trans (coefficientCap_ge_one j),hy.trans (coefficientCap_ge_one j)⟩


end CircleSampling

end

end OAI

import OAI.Analysis.RotationWeights.TaggedEvents

namespace OAI

noncomputable section

namespace CircleSampling

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
open Set Filter
open scoped Topology

def blockScale (s : ℕ) : ℝ := (blockLength s:ℝ)*polynomialWindow s
def blockRange (s : ℕ) : ℝ := (blockLength s:ℝ)^((4:ℝ)/5*blockLength s)
lemma blockScale_pos (s : ℕ) : 0<blockScale s := mul_pos (Nat.cast_pos.mpr (scaleStep s).mpos) (Nat.cast_pos.mpr (polynomialWindow_pos s))
lemma blockRange_ge_length (s : ℕ) : (blockLength s:ℝ) ≤ blockRange s := by
  have hm : (200:ℝ) ≤ blockLength s := by exact_mod_cast blockLength_ge s
  calc
    _ = (blockLength s:ℝ)^(1:ℝ) := (Real.rpow_one _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
lemma bridge_overlap (s : ℕ) : bridgeSize (s+1)*(polynomialWindow (s+1):ℝ)<blockRange s := by
  exact (scaleStep s).numeric.2.2.2.2.2.1
lemma bridge_below_scale (s : ℕ) : bridgeSize s*(polynomialWindow s:ℝ) ≤ blockScale s/4 := by
  have h := (scaleStep s).numeric.2.2.2.1
  change 4*bridgeSize s ≤ (blockLength s:ℝ) at h
  have hK : (0:ℝ) ≤ polynomialWindow s := Nat.cast_nonneg _
  unfold blockScale
  nlinarith
lemma scale_below_range (s : ℕ) : blockScale s/4<blockRange s := by
  have hm : (200:ℝ) ≤ blockLength s := by exact_mod_cast blockLength_ge s
  have hK : (polynomialWindow s:ℝ) ≤ blockLength s := by exact_mod_cast polynomialWindow_le_length s
  have hexp : (blockLength s:ℝ)^2 ≤ blockRange s := by
    rw [←Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num; linarith)
  unfold blockScale
  nlinarith
lemma exists_large_range (j : ℕ) {t : ℝ} (ht : blockScale j/4<t) :
    (∃ s : ℕ, j ≤ s ∧ blockScale s/4≤t ∧ t≤blockRange s) ∨
    (∃ s : ℕ, j < s ∧ bridgeSize s*(polynomialWindow s:ℝ)≤t ∧ t≤blockScale s/4) := by
  have hex : ∃ n : ℕ,t≤blockRange (j+n) := by
    obtain ⟨n,hn⟩ := exists_nat_ge t
    refine ⟨n,hn.trans ?_⟩
    have hmn : n≤blockLength (j+n) := (by omega : n≤j+n).trans (blockLength_strictMono.id_le _)
    exact (show (n:ℝ) ≤ (blockLength (j+n):ℝ) by exact_mod_cast hmn).trans (blockRange_ge_length _)
  let n := Nat.find hex
  have htop : t≤blockRange (j+n) := Nat.find_spec hex
  cases hn : n with
  | zero => exact Or.inl ⟨j,le_rfl,ht.le,by simpa [hn] using htop⟩
  | succ a =>
    have hprev : blockRange (j+a)<t := lt_of_not_ge (Nat.find_min hex (by omega : a<Nat.find hex))
    by_cases hscale : blockScale (j+n)/4≤t
    · exact Or.inl ⟨j+n,by omega,hscale,htop⟩
    · refine Or.inr ⟨j+n,by omega,?_,(lt_of_not_ge hscale).le⟩
      have hb : bridgeSize (j+n)*(polynomialWindow (j+n):ℝ) ≤ blockRange (j+a) := by
        simpa only [hn,Nat.add_succ] using (bridge_overlap (j+a)).le
      exact hb.trans hprev.le
end

section
open Set CircleCoupling CircleCoupling.CoordinateParameters ContinuousCircleWeight.Sampling
open scoped BigOperators

def crossingThreshold (k : ℤ) (i : ℕ) : ℝ := 1-Int.fract ((k:ℝ)*coordinatePhase (i-1))
def stageCrossingWidth (s : ℕ) (e : Bool) : ℝ := if e then rangeWidth s else bridgeWidth s
def stageCrossingProbability (s : ℕ) (e : Bool) : ℝ := crossingProbability (kappa s) (stageCrossingWidth s e) (blockLength s)

lemma coordinatePhase_bounds (i : ℕ) : coordinatePhase i ∈ Ioo (1/blockScale (coordinateBlock i)) (2/blockScale (coordinateBlock i)) := by
  obtain ⟨⟨j,k⟩,rfl⟩ := blocks.equiv.surjective i
  rw [coordinateBlock_equiv]
  exact coordinatePhase_block j k
lemma stageCrossingProbability_eq (s n : ℕ) (hn : n+1 ∈ blockCoordinates s) (e : Bool) :
    (actualSystem.coord n).prob e=stageCrossingProbability s e := by
  cases e <;> simp only [CoordinateParameters.prob,CoordinateParameters.ρ,CoordinateParameters.σ,
    actualSystem,actualCoordinate,stageCrossingProbability,stageCrossingWidth,Bool.false_eq_true,↓reduceIte,blockCoordinates_block s n hn]
lemma stageCrossingWidth_eq (s n : ℕ) (hn : n+1 ∈ blockCoordinates s) (e : Bool) :
    actualSystem.crossingWidth e (n+1)=stageCrossingWidth s e := by
  cases e <;> simp only [DigitSystem.crossingWidth,CoordinateParameters.width,
    actualSystem,actualCoordinate,stageCrossingWidth,Bool.false_eq_true,↓reduceIte,blockCoordinates_block s n hn]
lemma stageCrossingProbability_nonneg (s : ℕ) (e : Bool) : 0 ≤ stageCrossingProbability s e :=
  crossingProbability_nonneg (kappa_pos s).le
lemma stageCrossingProbability_le_one (s : ℕ) (e : Bool) : stageCrossingProbability s e ≤ 1 := by
  have hi : blockEnd s+1 ∈ blockCoordinates s := Finset.mem_Ico.mpr ⟨le_rfl,by have hm : 0 < blockLength s := (scaleStep s).mpos; change blockEnd s+1<blockEnd s+blockLength s+1; omega⟩
  rw [←stageCrossingProbability_eq s (blockEnd s) hi e]
  exact (actualSystem.coord (blockEnd s)).prob_le_one e
lemma stage_range_strength (s : ℕ) : crossingBudget s ≤ (blockLength s:ℝ)*stageCrossingProbability s true := by
  have hm : 0<(blockLength s:ℝ) := Nat.cast_pos.mpr (scaleStep s).mpos
  have hroot : Real.sqrt (rangeWidth s/(blockLength s:ℝ))=(blockLength s:ℝ)^(-(39:ℝ)/40) := by
    rw [Real.sqrt_eq_rpow,rangeWidth]
    conv_lhs => arg 1; rhs; rw [←Real.rpow_one (blockLength s:ℝ)]
    rw [←Real.rpow_sub hm,←Real.rpow_mul hm.le]
    norm_num
  have he : (blockLength s:ℝ)*stageCrossingProbability s true=kappa s*(blockLength s:ℝ)^((1:ℝ)/40) := by
    change (blockLength s:ℝ)*(kappa s*Real.sqrt (rangeWidth s/(blockLength s:ℝ)))=_
    rw [hroot]
    calc
      _ = kappa s*((blockLength s:ℝ)^(1:ℝ)*(blockLength s:ℝ)^(-(39:ℝ)/40)) := by rw [Real.rpow_one]; ring
      _ = _ := by rw [←Real.rpow_add hm]; norm_num
  rw [he]
  exact (scaleStep s).numeric.2.2.2.2.1
lemma stage_bridge_strength (s : ℕ) : crossingBudget s ≤ (blockLength (s+1):ℝ)*stageCrossingProbability (s+1) false := by
  have hm : 0<(blockLength (s+1):ℝ) := Nat.cast_pos.mpr (scaleStep (s+1)).mpos
  have hroot : Real.sqrt (bridgeWidth (s+1)/(blockLength (s+1):ℝ))=Real.sqrt (bridgeSize (s+1))/(blockLength (s+1):ℝ) := by
    rw [bridgeWidth,div_div,←pow_two,Real.sqrt_div (le_trans (by norm_num) (bridgeSize_ge_one _)),Real.sqrt_sq hm.le]
  have he : (blockLength (s+1):ℝ)*stageCrossingProbability (s+1) false=kappa (s+1)*Real.sqrt (bridgeSize (s+1)) := by
    change (blockLength (s+1):ℝ)*(kappa (s+1)*Real.sqrt (bridgeWidth (s+1)/(blockLength (s+1):ℝ)))=_
    rw [hroot]; field_simp
  rw [he]
  exact (scaleStep s).bridge

lemma threshold_bounds_of_abs {k : ℤ} {β a : ℝ} (ha : 0<a) (hat : a≤|(k:ℝ)| *β)
    (ht : |(k:ℝ)| *β<1/2) : a≤1-Int.fract ((k:ℝ)*β) ∧ 1-Int.fract ((k:ℝ)*β)≤1-a := by
  have hp : 0 < |(k:ℝ)| *β := ha.trans_le hat
  by_cases hk : 0≤k
  · rw [abs_of_nonneg ((by exact_mod_cast hk))] at hat ht hp
    rw [Int.fract_eq_self.mpr ⟨hp.le,by linarith⟩]
    constructor <;> linarith
  · have hk' : (k:ℝ)<0 := (by exact_mod_cast (lt_of_not_ge hk))
    rw [abs_of_neg hk'] at hat ht hp
    have hf : Int.fract (-((k:ℝ)*β))=-((k:ℝ)*β) := Int.fract_eq_self.mpr ⟨by nlinarith,by nlinarith⟩
    have hne : Int.fract (-((k:ℝ)*β))≠0 := by rw [hf]; nlinarith
    have hn := Int.fract_neg hne
    rw [neg_neg,hf] at hn
    rw [hn]
    constructor <;> nlinarith

lemma bridge_thresholds (s : ℕ) (k : ℤ)
    (hklo : bridgeSize s*(polynomialWindow s:ℝ)≤|(k:ℝ)|) (hkhi : |(k:ℝ)| ≤blockScale s/4) :
    ∀ i∈blockCoordinates s, bridgeWidth s ≤ crossingThreshold k i ∧ crossingThreshold k i≤1-bridgeWidth s := by
  intro i hi
  have hi0 : i ≠ 0 := by intro hz; subst i; exact blockCoordinates_zero s hi
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
  have hn := blockCoordinates_block s n hi
  have hβ := coordinatePhase_bounds n
  rw [hn] at hβ
  have hm : 0<(blockLength s:ℝ) := Nat.cast_pos.mpr (scaleStep s).mpos
  have hK : 0<(polynomialWindow s:ℝ) := Nat.cast_pos.mpr (polynomialWindow_pos s)
  have hN := blockScale_pos s
  have hG : 0<bridgeSize s := lt_of_lt_of_le (by norm_num) (bridgeSize_ge_one s)
  have hka : 0 < |(k:ℝ)| := lt_of_lt_of_le (mul_pos hG hK) hklo
  apply threshold_bounds_of_abs (lt_of_lt_of_le (by positivity) (bridgeWidth_bounds s).1)
  · change bridgeWidth s ≤ |(k:ℝ)| *coordinatePhase n
    calc
      _ = bridgeSize s*(polynomialWindow s:ℝ)*(1/blockScale s) := by unfold bridgeWidth blockScale; field_simp
      _ ≤ |(k:ℝ)| *(1/blockScale s) := mul_le_mul_of_nonneg_right hklo (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hβ.1.le hka.le
  · change |(k:ℝ)| *coordinatePhase n<1/2
    calc
      _ < |(k:ℝ)| *(2/blockScale s) := mul_lt_mul_of_pos_left hβ.2 hka
      _ ≤ (blockScale s/4)*(2/blockScale s) := mul_le_mul_of_nonneg_right hkhi (by positivity)
      _ = 1/2 := by field_simp; ring

lemma large_thresholds (s : ℕ) (k : ℤ) (hklo : blockScale s/4≤|(k:ℝ)|) (hkhi : |(k:ℝ)| ≤blockRange s) :
    ∃ I : Finset ℕ, I⊆blockCoordinates s ∧ (blockLength s:ℝ)/20≤(I.card:ℝ) ∧
      ∀ i∈I, rangeWidth s≤crossingThreshold k i ∧ crossingThreshold k i≤1-rangeWidth s := by
  let emb : Fin (blockLength s) ↪ ℕ := ⟨fun i => blockEnd s+i.val+1,by intro a b h; apply Fin.ext; dsimp at h; omega⟩
  let J := Finset.univ.filter fun i : Fin (blockLength s) => coordinatePhase (blockEnd s+i.val) ∉ phaseFailure (rangeWidth s) k
  refine ⟨J.map emb,?_,?_,?_⟩
  · intro i hi
    obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hi
    exact Finset.mem_Ico.mpr ⟨by change blockEnd s+1≤blockEnd s+a.val+1; omega,by change blockEnd s+a.val+1<blockEnd s+blockLength s+1; have := a.isLt; omega⟩
  · rw [Finset.card_map]
    have hc := (scaleStep s).cover parameterAngle (parameterAngle_spec.2.2.2 s) k hklo hkhi
    have hJ : J=Finset.univ.filter (fun i : Fin (blockLength s) => Int.fract (((scaleStep s).q (i+1):ℝ)*parameterAngle) ∉ phaseFailure (rangeWidth s) k) := by
      ext i
      simp only [J,Finset.mem_filter,Finset.mem_univ,true_and]
      change (Int.fract (((frequency (blockEnd s+i.val+1)):ℝ)*parameterAngle) ∉ _) ↔ _
      rw [show blockEnd s+i.val+1=blockEnd s+(i.val+1) by omega,frequency_block s (by omega)]
    rw [hJ]
    exact hc
  · intro i hi
    obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hi
    have hh := (Finset.mem_filter.mp ha).2
    have hh' : rangeWidth s < 1-Int.fract ((k:ℝ)*coordinatePhase (blockEnd s+a.val)) ∧
        1-Int.fract ((k:ℝ)*coordinatePhase (blockEnd s+a.val))<1-rangeWidth s := by
      have hr (x : ℝ) : repr (x:CircleX)=Int.fract x := by
        change (AddCircle.equivIco 1 0 (x:CircleX)).val=_
        simpa only [div_one,mul_one] using AddCircle.coe_equivIco_mk_apply (p:=(1:ℝ)) x
      simpa only [phaseFailure,Set.mem_ofPred_eq,not_not,hr] using hh
    change rangeWidth s ≤ 1-Int.fract ((k:ℝ)*coordinatePhase (blockEnd s+a.val+1-1)) ∧ 1-Int.fract ((k:ℝ)*coordinatePhase (blockEnd s+a.val+1-1))≤1-rangeWidth s
    simpa only [Nat.add_sub_cancel] using And.intro hh'.1.le hh'.2.le
end

section
open MeasureTheory Set Filter CircleCoupling CircleDigits
open scoped ENNReal

def regularSamples : Set ActualSamples := {ω | ω∈actualSystem.supported ∧
  firstEndpoint ω∈modelGood ∧ lastEndpoint ω∈modelGood ∧
  firstEndpoint ω∈gridFree actualSystem.radix ∧ lastEndpoint ω∈gridFree actualSystem.radix}
lemma ae_regularSamples (j : ℕ) : ∀ᵐ ω ∂actualSystem.probability (stageTagged j),ω∈regularSamples := by
  filter_upwards [actualSystem.ae_supported (stageTagged j),ae_endpoint_good j (fun _ => false),
    ae_endpoint_good j (fun _ => true),actualSystem.ae_hybrid_gridFree (stageTagged j) (fun _ => false) (summable_actual_error j),
    actualSystem.ae_hybrid_gridFree (stageTagged j) (fun _ => true) (summable_actual_error j)] with ω hs hx hy hfx hfy
  exact ⟨hs,hx,hy,hfx,hfy⟩
lemma actual_Xi_tail {ω : ActualSamples} (hω : ω∈regularSamples) (n : ℕ) :
    CircleModel.Xi modelFrequency n (firstEndpoint ω)=scaledTail actualSystem.radix (fun i => (ω i).2.1) (n+1) ∧
    CircleModel.Xi modelFrequency n (lastEndpoint ω)=scaledTail actualSystem.radix (fun i => (ω i).2.2) (n+1) := by
  constructor
  · change (AddCircle.measurableEquivIco 1 0 (frequency (n+1) • firstEndpoint ω)).val=_
    rw [←actual_denominator]
    exact scaledTail_repr actualSystem.radix_ge_two _ hω.2.2.2.1 _
  · change (AddCircle.measurableEquivIco 1 0 (frequency (n+1) • lastEndpoint ω)).val=_
    rw [←actual_denominator]
    exact scaledTail_repr actualSystem.radix_ge_two _ hω.2.2.2.2 _
lemma regular_order {ω : ActualSamples} (hω : ω∈regularSamples) (n : ℕ) :
    CircleModel.Xi modelFrequency n (firstEndpoint ω) ≤ CircleModel.Xi modelFrequency n (lastEndpoint ω) := by
  rw [(actual_Xi_tail hω n).1,(actual_Xi_tail hω n).2]
  exact scaledTail_mono actualSystem.radix_ge_two hω.1.1 _
lemma crossing_decay {ω : ActualSamples} (hω : ω∈regularSamples) (k : ℤ) (n : ℕ)
    (hlo : scaledTail actualSystem.radix (fun i => (ω i).2.1) (n+1)<crossingThreshold k (n+1))
    (hhi : crossingThreshold k (n+1) ≤ scaledTail actualSystem.radix (fun i => (ω i).2.2) (n+1)) :
    modelF k (lastEndpoint ω)/modelF k (firstEndpoint ω) ≤ Real.exp (-coordinateDrop n) := by
  apply CircleModel.cocycle_ratio_crossing coordinateDrop (fun i => dropSize_nonneg (coordinateBlock i)) k hω.2.1 hω.2.2.1 (regular_order hω) n
  · simpa only [model_beta,(actual_Xi_tail hω n).1,crossingThreshold,Nat.add_sub_cancel] using hlo
  · simpa only [model_beta,(actual_Xi_tail hω n).2,crossingThreshold,Nat.add_sub_cancel] using hhi

lemma stage_masks (j s : ℕ) (hjs : j ≤ s) (e : Bool) (k : ℤ) (I : Finset ℕ)
    (hI : I⊆blockCoordinates s) (hcard : (blockLength s:ℝ)/20 ≤ (I.card:ℝ))
    (hstrength : crossingBudget j ≤ (blockLength s:ℝ)*stageCrossingProbability s e)
    (hu : ∀ i∈I,stageCrossingWidth s e ≤ crossingThreshold k i ∧ crossingThreshold k i ≤ 1-stageCrossingWidth s e) :
    ∃ H₁ H₂ : Set ActualSamples,MeasurableSet H₁ ∧ MeasurableSet H₂ ∧
      Measure.map firstEndpoint ((actualSystem.probability (stageTagged j)).restrict H₁) ≤ ENNReal.ofReal (Real.exp (-crossingBudget j/400)) • Measure.map firstEndpoint (actualSystem.probability (stageTagged j)) ∧
      Measure.map lastEndpoint ((actualSystem.probability (stageTagged j)).restrict H₂) ≤ ENNReal.ofReal (Real.exp (-crossingBudget j/400)) • Measure.map lastEndpoint (actualSystem.probability (stageTagged j)) ∧
      ∀ ω∈regularSamples,ω∉H₁ → ω∉H₂ → modelF k (lastEndpoint ω)/modelF k (firstEndpoint ω) ≤ Real.exp (-crossingBudget j) := by
  have hzero : 0∉I := fun h => blockCoordinates_zero s (hI h)
  have hwidth : ∀ i∈I,actualSystem.crossingWidth e i ≤ crossingThreshold k i ∧ crossingThreshold k i ≤ 1-actualSystem.crossingWidth e i := by
    intro i hi
    have hi0 : i≠0 := fun hz => hzero (hz ▸ hi)
    obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
    rw [stageCrossingWidth_eq s n (hI hi) e]
    exact hu _ hi
  obtain ⟨H₁,H₂,hm₁,hm₂,hd,he,_,hd₁,hd₂⟩ := actualSystem.actual_crossing_estimates (stageTagged j) e I hzero (crossingThreshold k)
    (blockLength s) (stageCrossingProbability s e) (stageCrossingProbability_nonneg s e) (stageCrossingProbability_le_one s e)
    hcard (fun n hn => stageCrossingProbability_eq s n (hI hn) e) hwidth
  have hδ : ENNReal.ofReal (Real.exp (-(blockLength s:ℝ)*stageCrossingProbability s e/400)) ≤ ENNReal.ofReal (Real.exp (-crossingBudget j/400)) := by
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    linarith
  refine ⟨H₁,H₂,hm₁,hm₂,hd₁.trans (by gcongr; exact le_rfl),hd₂.trans (by gcongr; exact le_rfl),?_⟩
  intro ω hω h₁ h₂
  have hn : ω∉noCross actualSystem.radix I (crossingThreshold k) := by rw [←he]; exact fun h => h.elim h₁ h₂
  simp only [noCross,Set.mem_ofPred_eq,not_forall,Classical.not_not] at hn
  obtain ⟨i,hi,hcross⟩ := hn
  have hi0 : i≠0 := fun hz => hzero (hz ▸ hi)
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
  have hc := crossing_decay hω k n hcross.1 hcross.2
  apply hc.trans
  apply Real.exp_le_exp.mpr
  change -dropSize (coordinateBlock n) ≤ -crossingBudget j
  rw [blockCoordinates_block s n (hI hi)]
  exact neg_le_neg ((crossingBudget_mono hjs).trans (dropSize_ge_budget s))

lemma large_masks (j : ℕ) (k : ℤ) (hk : blockScale j/4< |(k:ℝ)|) :
    ∃ H₁ H₂ : Set ActualSamples,MeasurableSet H₁ ∧ MeasurableSet H₂ ∧
      Measure.map firstEndpoint ((actualSystem.probability (stageTagged j)).restrict H₁) ≤ ENNReal.ofReal (Real.exp (-crossingBudget j/400)) • Measure.map firstEndpoint (actualSystem.probability (stageTagged j)) ∧
      Measure.map lastEndpoint ((actualSystem.probability (stageTagged j)).restrict H₂) ≤ ENNReal.ofReal (Real.exp (-crossingBudget j/400)) • Measure.map lastEndpoint (actualSystem.probability (stageTagged j)) ∧
      ∀ ω∈regularSamples,ω∉H₁ → ω∉H₂ → modelF k (lastEndpoint ω)/modelF k (firstEndpoint ω) ≤ Real.exp (-crossingBudget j) := by
  rcases exists_large_range j hk with ⟨s,hjs,hlo,hhi⟩ | ⟨s,hjs,hlo,hhi⟩
  · obtain ⟨I,hI,hcard,hu⟩ := large_thresholds s k hlo hhi
    exact stage_masks j s hjs true k I hI hcard ((crossingBudget_mono hjs).trans (stage_range_strength s)) hu
  · have hs0 : s≠0 := by omega
    obtain ⟨a,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs0
    apply stage_masks j (a+1) (by omega) false k (blockCoordinates (a+1)) (fun _ h => h)
    · rw [blockCoordinates_card]; nlinarith [show (0:ℝ) ≤ blockLength (a+1) from Nat.cast_nonneg _]
    · exact (crossingBudget_mono (by omega : j ≤ a)).trans (stage_bridge_strength a)
    · exact bridge_thresholds (a+1) k hlo hhi
end

open MeasureTheory Set CircleCoupling CircleDigits
open scoped ENNReal

lemma tagged_coordinate_extreme {ω : ActualSamples} (hω : ω∈regularSamples) {n : ℕ}
    (ht : (ω (n+1)).1=some (4:Fin 5)) :
    scaledTail actualSystem.radix (fun i => (ω i).2.1) (n+1)<1/(blockLength (coordinateBlock n):ℝ) ∧
    1-1/(blockLength (coordinateBlock n):ℝ) ≤ scaledTail actualSystem.radix (fun i => (ω i).2.2) (n+1) := by
  let P := actualSystem.coord n
  have hs := hω.1.2 n
  change supportCondition P.l (roundedWidth P.l P.a) (roundedWidth P.l P.b) (roundedTag P.l P.m) (ω (n+1)) at hs
  simp only [supportCondition,ht] at hs
  norm_num at hs
  have hl : (0:ℝ)<P.l := Nat.cast_pos.mpr (NeZero.pos P.l)
  have hm : (0:ℝ)<P.m := P.m_pos
  have hx := (digit_interval actualSystem.radix_ge_two (fun i => (ω i).2.1) hω.2.2.2.1 (n+1)).2
  have hy := (digit_interval actualSystem.radix_ge_two (fun i => (ω i).2.2) hω.2.2.2.2 (n+1)).1
  change _ < (((ω (n+1)).2.1.val:ℝ)+1)/(P.l:ℝ) at hx
  change ((ω (n+1)).2.2.val:ℝ)/(P.l:ℝ) ≤ _ at hy
  have ha : ((ω (n+1)).2.1.val:ℝ)+1 ≤ roundedTag P.l P.m := by exact_mod_cast hs.1
  have hb : (P.l:ℝ)-(roundedTag P.l P.m:ℝ) ≤ ((ω (n+1)).2.2.val:ℝ) := by
    have hh : (P.l:ℝ) ≤ ((ω (n+1)).2.2.val:ℝ)+(roundedTag P.l P.m:ℝ) := by
      exact_mod_cast (show P.l ≤ (ω (n+1)).2.2.val+roundedTag P.l P.m from hs.2)
    linarith
  have hr := P.tag_bounds.2.2.2
  change (roundedTag P.l P.m:ℝ) ≤ (P.l:ℝ)/P.m at hr
  constructor
  · change _ < 1/(P.m:ℝ)
    apply hx.trans_le
    rw [div_le_iff₀ hl]
    convert ha.trans hr using 1; ring
  · change 1-1/(P.m:ℝ) ≤ _
    apply le_trans _ hy
    rw [le_div_iff₀ hl]
    calc
      _ = (P.l:ℝ)-(P.l:ℝ)/P.m := by ring
      _ ≤ (P.l:ℝ)-(roundedTag P.l P.m:ℝ) := sub_le_sub_left hr _
      _ ≤ _ := hb

lemma short_ratio (j : ℕ) (k : ℤ) (hklo : (polynomialWindow j:ℝ)< |(k:ℝ)|) (hkhi : |(k:ℝ)| ≤ blockScale j/4)
    {ω : ActualSamples} (hω : ω∈regularSamples) (htag : ω∈stageTagEvent j) :
    modelF k (lastEndpoint ω)/modelF k (firstEndpoint ω) ≤ Real.exp (-crossingBudget j) := by
  obtain ⟨⟨n,hn,ht⟩,_⟩ := stageTagEvent_margins j hω.1 htag
  have hphase := coordinatePhase_bounds n
  have hblock := blockCoordinates_block j n hn
  rw [hblock] at hphase
  have hm : (0:ℝ)<blockLength j := Nat.cast_pos.mpr (scaleStep j).mpos
  have hK : (0:ℝ)<polynomialWindow j := Nat.cast_pos.mpr (polynomialWindow_pos j)
  have hk : 0< |(k:ℝ)| := hK.trans hklo
  have hlow : 1/(blockLength j:ℝ) ≤ |(k:ℝ)| * coordinatePhase n := by
    calc
      _ = (polynomialWindow j:ℝ)*(1/blockScale j) := by unfold blockScale; field_simp
      _ ≤ |(k:ℝ)| * (1/blockScale j) := mul_le_mul_of_nonneg_right hklo.le (by have := (blockScale_pos j).le; positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left hphase.1.le hk.le
  have hhigh : |(k:ℝ)| * coordinatePhase n<1/2 := by
    calc
      _ < |(k:ℝ)| * (2/blockScale j) := mul_lt_mul_of_pos_left hphase.2 hk
      _ ≤ (blockScale j/4)*(2/blockScale j) := mul_le_mul_of_nonneg_right hkhi (by have := (blockScale_pos j).le; positivity)
      _ = 1/2 := by have := (blockScale_pos j).ne'; field_simp; ring
  have hu := threshold_bounds_of_abs (by positivity : (0:ℝ)<1/(blockLength j:ℝ)) hlow hhigh
  have he := tagged_coordinate_extreme hω ht
  rw [hblock] at he
  have hc := crossing_decay hω k n (he.1.trans_le hu.1) (hu.2.trans he.2)
  apply hc.trans
  apply Real.exp_le_exp.mpr
  change -dropSize (coordinateBlock n) ≤ -crossingBudget j
  rw [hblock]
  exact neg_le_neg (dropSize_ge_budget j)


end CircleSampling

end

end OAI

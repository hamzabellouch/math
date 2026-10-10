import OAI.Analysis.RotationWeights.CrossingEstimates

namespace OAI

noncomputable section

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

namespace CircleSampling

section

section
open Set Filter MeasureTheory
open scoped Topology BigOperators

def coordinateRadix (i : ℕ) : ℕ := frequency (i+2)/frequency (i+1)
def bridgeWidth (j : ℕ) : ℝ := bridgeSize j/(blockLength j:ℝ)
def rangeWidth (j : ℕ) : ℝ := (blockLength j:ℝ)^(-(19:ℝ)/20)

lemma coordinateRadix_mul (i : ℕ) : coordinateRadix i*frequency (i+1)=frequency (i+2) :=
  Nat.div_mul_cancel (frequency_dvd (i+1))
lemma coordinateRadix_cast (i : ℕ) : (coordinateRadix i:ℝ)=(frequency (i+2):ℝ)/frequency (i+1) := by
  unfold coordinateRadix
  exact Nat.cast_div (frequency_dvd (i+1)) (Nat.cast_ne_zero.mpr (frequency_pos _).ne')
lemma coordinateBlock_equiv (x : Σ j, Fin (blocks.m j)) : coordinateBlock (blocks.equiv x)=x.1 := by
  exact blocks.number_eq (by change blockEnd x.1≤blockEnd x.1+x.2.val; omega)
    (by change blockEnd x.1+x.2.val<blockEnd x.1+blockLength x.1; exact Nat.add_lt_add_left x.2.isLt _)

lemma coordinateRadix_bound (i : ℕ) : 100*blockLength (coordinateBlock i)≤coordinateRadix i := by
  obtain ⟨⟨j,k⟩,rfl⟩ := blocks.equiv.surjective i
  rw [coordinateBlock_equiv]
  have hk : k.val<blockLength j := k.isLt
  have hh := frequency_radix_bound j (k:=k.val+1) (by omega)
  have he : blocks.equiv ⟨j,k⟩=blockEnd j+k.val := rfl
  have hc : (100*blockLength j:ℝ)≤coordinateRadix (blocks.equiv ⟨j,k⟩) := by
    rw [coordinateRadix_cast,he,show blockEnd j+k.val+2=blockEnd j+(k.val+1)+1 by omega,
      show blockEnd j+k.val+1=blockEnd j+(k.val+1) by omega]
    exact hh.le
  exact_mod_cast hc

lemma blockLength_ge_twoHundred (j : ℕ) : 200≤blockLength j := (scaleStep j).numeric.1
lemma bridgeSize_ge_one (j : ℕ) : 1≤bridgeSize j := (scaleState j).2.Gge
lemma bridgeWidth_bounds (j : ℕ) : 1/(blockLength j:ℝ)≤bridgeWidth j ∧ bridgeWidth j≤1/4 := by
  have hm : 0<(blockLength j:ℝ) := Nat.cast_pos.mpr (scaleStep j).mpos
  refine ⟨div_le_div_of_nonneg_right (bridgeSize_ge_one j) hm.le,?_⟩
  exact (div_le_iff₀ hm).mpr (by
    have hg := (scaleStep j).numeric.2.2.2.1
    change 4*bridgeSize j≤(blockLength j:ℝ) at hg
    linarith)
lemma rangeWidth_bounds (j : ℕ) : 1/(blockLength j:ℝ)≤rangeWidth j ∧ rangeWidth j≤1/4 := by
  refine ⟨?_,(scaleStep j).numeric.2.2.2.2.2.2.2.2⟩
  have hm : (1:ℝ)≤blockLength j := by exact_mod_cast (scaleStep j).mpos
  change _≤(blockLength j:ℝ)^(-(19:ℝ)/20)
  rw [one_div,←Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le hm (by norm_num)

def stageTagged (j i : ℕ) : Bool := decide (coordinateBlock i=j)
lemma stageTagged_finite (j : ℕ) : {i | stageTagged j i=true}.Finite := by
  apply (finite_Iio (blockEnd (j+1))).subset
  intro i hi
  have hb : coordinateBlock i=j := of_decide_eq_true hi
  have hr := (blocks.number_spec i).2
  change i<blockEnd (j+1)
  change i<blockEnd (coordinateBlock i)+blockLength (coordinateBlock i) at hr
  have he (t : ℕ) : blockEnd t+blockLength t=blockEnd (t+1) := rfl
  rw [he] at hr
  exact hr.trans_le (blockEnd_strictMono.monotone (by omega))
lemma summable_stageTagError (j : ℕ) :
    Summable (fun i => (if stageTagged j i then (10:ℝ) else 0)/(blockLength (coordinateBlock i):ℝ)) := by
  apply summable_of_hasFiniteSupport
  apply (stageTagged_finite j).subset
  intro i hi
  simp only [Function.mem_support] at hi
  cases h : stageTagged j i
  · simp [h] at hi
  · exact h

lemma summable_kappa_sq : Summable (fun j => (kappa j)^2) := by
  have hs : Summable (fun j : ℕ => (1:ℝ)/(j:ℝ)^2) := by
    exact Real.summable_one_div_nat_pow.mpr (by norm_num : 1<2)
  have ht := (summable_nat_add_iff 1).mpr hs
  have he : (fun j => (kappa j)^2)=(fun j => (1/(100:ℝ)^2)*(1/((j+1:ℕ):ℝ)^2)) := by
    funext j
    dsimp [kappa]
    push_cast
    field_simp
  rw [he]
  exact ht.mul_left (1/(100:ℝ)^2)

lemma summable_coordinateKappaError :
    Summable (fun i => 60*(kappa (coordinateBlock i))^2/(blockLength (coordinateBlock i):ℝ)) := by
  apply blocks.equiv.summable_iff.mp
  apply (summable_sigma_of_nonneg (fun x : Σ j, Fin (blocks.m j) => (by positivity :
    0≤60*(kappa (coordinateBlock (blocks.equiv x)))^2/(blockLength (coordinateBlock (blocks.equiv x)):ℝ)))).mpr
  refine ⟨fun _ => Summable.of_finite,?_⟩
  have he (j : ℕ) : (∑' i : Fin (blocks.m j),60*(kappa (coordinateBlock (blocks.equiv ⟨j,i⟩)))^2/
    (blockLength (coordinateBlock (blocks.equiv ⟨j,i⟩)):ℝ))=60*(kappa j)^2 := by
    simp_rw [coordinateBlock_equiv]
    rw [tsum_fintype]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    change (blockLength j:ℝ)*(_/(blockLength j:ℝ))=_
    have hm : (blockLength j:ℝ)≠0 := Nat.cast_ne_zero.mpr (scaleStep j).mpos.ne'
    field_simp
  simp_rw [he]
  exact summable_kappa_sq.mul_left 60
end

open MeasureTheory Set Filter CircleCoupling
open scoped BigOperators ENNReal Topology

def actualCoordinate (i : ℕ) : CoordinateParameters where
  l := coordinateRadix i
  m := blockLength (coordinateBlock i)
  κ := kappa (coordinateBlock i)
  a := bridgeWidth (coordinateBlock i)
  b := rangeWidth (coordinateBlock i)
  hm := blockLength_ge_twoHundred _
  hl := coordinateRadix_bound i
  hκ0 := (kappa_pos _).le
  hκ := kappa_le _
  ha := bridgeWidth_bounds _
  hb := rangeWidth_bounds _
def actualSystem : DigitSystem where
  b₀ := frequency 1
  hb₀ := frequency_one_gt
  coord := actualCoordinate

lemma actual_radix_zero : actualSystem.radix 0=frequency 1 := rfl
lemma actual_radix_succ (i : ℕ) : actualSystem.radix (i+1)=coordinateRadix i := rfl
lemma actual_denominator (i : ℕ) : CircleDigits.denominator actualSystem.radix i=frequency i := by
  induction i with
  | zero => exact frequency_zero.symm
  | succ i ih =>
    rw [CircleDigits.denominator_succ,ih]
    cases i with
    | zero => simp only [actual_radix_zero,frequency_zero,one_mul]
    | succ i =>
      rw [actual_radix_succ,mul_comm]
      exact coordinateRadix_mul i

lemma actual_error_succ (j i : ℕ) : actualSystem.error (stageTagged j) (i+1)=
    60*(kappa (coordinateBlock i))^2/(blockLength (coordinateBlock i):ℝ)+
    (if stageTagged j i then 10 else 0)/(blockLength (coordinateBlock i):ℝ) := by
  dsimp [DigitSystem.error,actualSystem,actualCoordinate]
  split <;> ring
lemma summable_actual_error (j : ℕ) : Summable (actualSystem.error (stageTagged j)) := by
  apply (summable_nat_add_iff 1).mp
  simp_rw [actual_error_succ]
  exact summable_coordinateKappaError.add (summable_stageTagError j)

lemma ae_actual_order (j : ℕ) : ∀ᵐ ω ∂actualSystem.probability (stageTagged j), ∀ i,
    (AddCircle.measurableEquivIco 1 0 (modelFrequency i • actualSystem.endpoint (fun _ => false) ω)).val ≤
    (AddCircle.measurableEquivIco 1 0 (modelFrequency i • actualSystem.endpoint (fun _ => true) ω)).val := by
  filter_upwards [actualSystem.ae_coordinate_order (stageTagged j) (summable_actual_error j)] with ω hω
  intro i
  simpa only [actual_denominator,modelFrequency] using hω (i+1)
end

open MeasureTheory Set Filter CircleCoupling
open scoped BigOperators ENNReal Topology

lemma actual_error_sum (j : ℕ) : (∑' i,actualSystem.error (stageTagged j) i)=
    60*(∑' s,(kappa s)^2)+10 := by
  rw [tsum_eq_zero_add' ((summable_nat_add_iff 1).mpr (summable_actual_error j)),show actualSystem.error (stageTagged j) 0=0 by rfl,zero_add]
  simp_rw [actual_error_succ]
  rw [summable_coordinateKappaError.tsum_add (summable_stageTagError j)]
  have hκ : (∑' i,60*(kappa (coordinateBlock i))^2/(blockLength (coordinateBlock i):ℝ))=
      60*(∑' s,(kappa s)^2) := by
    rw [←blocks.equiv.tsum_eq]
    have hs := blocks.equiv.summable_iff.mpr summable_coordinateKappaError
    simp only [Function.comp_def] at hs
    rw [hs.tsum_sigma]
    have he (s : ℕ) : (∑' i : Fin (blocks.m s),60*(kappa (coordinateBlock (blocks.equiv ⟨s,i⟩)))^2/
        (blockLength (coordinateBlock (blocks.equiv ⟨s,i⟩)):ℝ))=60*(kappa s)^2 := by
      simp_rw [coordinateBlock_equiv]
      rw [tsum_fintype]
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      change (blockLength s:ℝ)*(_/(blockLength s:ℝ))=_
      have hm : (blockLength s:ℝ)≠0 := Nat.cast_ne_zero.mpr (scaleStep s).mpos.ne'
      field_simp
    simp_rw [he]
    exact tsum_mul_left
  have ht : (∑' i,(if stageTagged j i then (10:ℝ) else 0)/(blockLength (coordinateBlock i):ℝ))=10 := by
    rw [←blocks.equiv.tsum_eq]
    have hs := blocks.equiv.summable_iff.mpr (summable_stageTagError j)
    simp only [Function.comp_def] at hs
    rw [hs.tsum_sigma]
    have he (s : ℕ) : (∑' i : Fin (blocks.m s),
        (if stageTagged j (blocks.equiv ⟨s,i⟩) then (10:ℝ) else 0)/
        (blockLength (coordinateBlock (blocks.equiv ⟨s,i⟩)):ℝ))=if s=j then 10 else 0 := by
      simp only [stageTagged,coordinateBlock_equiv,decide_eq_true_eq]
      split_ifs with hs
      · rw [tsum_fintype]
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
        change (blockLength s:ℝ)*(10/(blockLength s:ℝ))=10
        have hm : (blockLength s:ℝ)≠0 := Nat.cast_ne_zero.mpr (scaleStep s).mpos.ne'
        field_simp
      · simp
    simp_rw [he]
    exact tsum_ite_eq j (fun _ => 10)
  rw [hκ,ht]

def marginalConstant : ℝ := Real.exp (30*(∑' s,(kappa s)^2)+5)
lemma marginalConstant_pos : 0 < marginalConstant := Real.exp_pos _
lemma actual_hybrid_bound (j : ℕ) (e : ℕ → Bool) (A : Set CircleDigits.CircleX) (hA : MeasurableSet A) :
    (actualSystem.probability (stageTagged j)).real (actualSystem.endpoint e ⁻¹' A) ≤
      marginalConstant*Real.sqrt (volume.real A) := by
  have hh := actualSystem.hybrid_sqrt_bound (stageTagged j) e (summable_actual_error j) A hA
  rw [actual_error_sum] at hh
  convert hh using 1
  unfold marginalConstant
  congr 2
  ring
end CircleSampling

namespace CircleDigits
open Filter Set
open scoped Topology BigOperators

def hybrid {b : ℕ → ℕ} (d e : Digits b) (D : ℕ) : Digits b := fun i => if i<D then e i else d i
lemma hybrid_order {b : ℕ → ℕ} {d e : Digits b} (h : ∀ i,d i ≤ e i) (D i : ℕ) : d i ≤ hybrid d e D i := by
  unfold hybrid
  split_ifs <;> first | exact h i | rfl
lemma hybrid_tail {b : ℕ → ℕ} (hb : ∀ i,2 ≤ b i) (d e : Digits b) (D : ℕ) :
    scaledTail b (hybrid d e D) D=scaledTail b d D := by
  rw [scaledTail_tsum hb,scaledTail_tsum hb]
  congr 1
  apply tsum_congr
  intro i
  simp only [digitTerm,hybrid,show ¬i+D<D by omega,ite_false]
lemma hybrid_grid {b : ℕ → ℕ} (hb : ∀ i,2 ≤ b i) (d e : Digits b) (D : ℕ) :
    ∃ a : Fin (denominator b D), endpoint b (hybrid d e D)-endpoint b d=(((a.val:ℝ)/(denominator b D:ℝ):ℝ):CircleX) := by
  have hz : denominator b D • (endpoint b (hybrid d e D)-endpoint b d)=0 := by
    rw [nsmul_sub,←scaledTail_coe,←scaledTail_coe,hybrid_tail hb,sub_self]
  obtain ⟨a,ha,he⟩ := (AddCircle.nsmul_eq_zero_iff (denominator_pos hb D)).mp hz
  exact ⟨⟨a,ha⟩,by simpa only [mul_one] using he.symm⟩
lemma hybrid_expansion_tendsto {b : ℕ → ℕ} (hb : ∀ i,2 ≤ b i) (d e : Digits b) :
    Tendsto (fun D => expansion b (hybrid d e D)) atTop (𝓝 (expansion b e)) := by
  have hprefix (D : ℕ) : ∑ i∈Finset.range D,digitTerm b (hybrid d e D) i = ∑ i∈Finset.range D,digitTerm b e i := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [digitTerm,hybrid,Finset.mem_range.mp hi,ite_true]
  have hbound (D : ℕ) : |expansion b (hybrid d e D)-expansion b e| ≤ (denominator b D:ℝ)⁻¹ := by
    have hh := expansion_tail_bound hb (hybrid d e D) D
    have he := expansion_tail_bound hb e D
    rw [hprefix] at hh
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun D => dist_nonneg) (fun D => ?_) (denominator_inv_tendsto hb)
  simpa only [Real.dist_eq] using hbound D
lemma hybrid_endpoint_tendsto {b : ℕ → ℕ} (hb : ∀ i,2 ≤ b i) (d e : Digits b) :
    Tendsto (fun D => endpoint b (hybrid d e D)) atTop (𝓝 (endpoint b e)) :=
  ((AddCircle.continuous_mk' 1).tendsto _).comp (hybrid_expansion_tendsto hb d e)
end CircleDigits

namespace CircleSampling
open MeasureTheory Set Filter ContinuousCircleWeight CircleCoupling
open scoped Topology ENNReal ComplexInnerProductSpace
local instance : MeasurableSpace FiberHilbert := borel FiberHilbert
local instance : BorelSpace FiberHilbert := ⟨rfl⟩

abbrev ActualSamples := actualSystem.Samples
def hybridChoice (D : ℕ) (i : ℕ) : Bool := decide (i<D+1)
def firstEndpoint : ActualSamples → CircleX := actualSystem.endpoint (fun _ => false)
def lastEndpoint : ActualSamples → CircleX := actualSystem.endpoint (fun _ => true)
def hybridEndpoint (D : ℕ) : ActualSamples → CircleX := actualSystem.endpoint (hybridChoice D)
lemma firstEndpoint_measurable : Measurable firstEndpoint := actualSystem.measurable_endpoint _
lemma lastEndpoint_measurable : Measurable lastEndpoint := actualSystem.measurable_endpoint _
lemma hybridEndpoint_measurable (D : ℕ) : Measurable (hybridEndpoint D) := actualSystem.measurable_endpoint _
lemma hybrid_observe (D : ℕ) (ω : ActualSamples) :
    actualSystem.observe (hybridChoice D) ω = CircleDigits.hybrid
      (actualSystem.observe (fun _ => false) ω) (actualSystem.observe (fun _ => true) ω) (D+1) := by
  funext i
  simp only [DigitSystem.observe,CircleDigits.hybrid,hybridChoice]
  by_cases hi : i<D+1 <;> simp [hi]
lemma actual_hybrid_grid (D : ℕ) (ω : ActualSamples) :
    ∃ a : Fin (frequency (D+1)), hybridEndpoint D ω=firstEndpoint ω+rationalPoint D a := by
  have hh := CircleDigits.hybrid_grid actualSystem.radix_ge_two
    (actualSystem.observe (fun _ => false) ω) (actualSystem.observe (fun _ => true) ω) (D+1)
  rw [←hybrid_observe,actual_denominator] at hh
  obtain ⟨a,ha⟩ := hh
  exact ⟨a,by simpa [hybridEndpoint,firstEndpoint,DigitSystem.endpoint,rationalPoint] using (sub_eq_iff_eq_add.mp ha).trans (add_comm _ _)⟩
lemma actual_hybrid_tendsto (ω : ActualSamples) : Tendsto (fun D => hybridEndpoint D ω) atTop (𝓝 (lastEndpoint ω)) := by
  have hh := (CircleDigits.hybrid_endpoint_tendsto actualSystem.radix_ge_two
    (actualSystem.observe (fun _ => false) ω) (actualSystem.observe (fun _ => true) ω)).comp (tendsto_add_atTop_nat 1)
  simpa only [hybridEndpoint,lastEndpoint,DigitSystem.endpoint,hybrid_observe,Function.comp_def] using hh

lemma ae_endpoint_good (j : ℕ) (e : ℕ → Bool) :
    ∀ᵐ ω ∂actualSystem.probability (stageTagged j), actualSystem.endpoint e ω∈modelGood :=
  ae_of_ae_map (actualSystem.measurable_endpoint e).aemeasurable
    ((actualSystem.hybrid_ac (stageTagged j) e (summable_actual_error j)).ae_le model_good_ae)
lemma ae_hybrid_coordinate_order (j D : ℕ) :
    ∀ᵐ ω ∂actualSystem.probability (stageTagged j), ∀ i,
      CircleModel.Xi modelFrequency i (firstEndpoint ω) ≤ CircleModel.Xi modelFrequency i (hybridEndpoint D ω) := by
  filter_upwards [actualSystem.ae_digit_order (stageTagged j),
    actualSystem.ae_hybrid_gridFree (stageTagged j) (fun _ => false) (summable_actual_error j),
    actualSystem.ae_hybrid_gridFree (stageTagged j) (hybridChoice D) (summable_actual_error j)] with ω hω hx hy
  intro i
  change (AddCircle.measurableEquivIco 1 0 (frequency (i+1) • actualSystem.endpoint (fun _ => false) ω)).val ≤
    (AddCircle.measurableEquivIco 1 0 (frequency (i+1) • actualSystem.endpoint (hybridChoice D) ω)).val
  rw [←actual_denominator]
  dsimp only [DigitSystem.endpoint] at hx hy ⊢
  rw [CircleDigits.scaledTail_repr actualSystem.radix_ge_two _ hx,CircleDigits.scaledTail_repr actualSystem.radix_ge_two _ hy]
  apply CircleDigits.scaledTail_mono actualSystem.radix_ge_two
  intro k
  rw [hybrid_observe]
  exact CircleDigits.hybrid_order hω (D+1) k

lemma cappedDiagonal_eq_of_ratio_le {X : Type uX} (F : ℤ → X → ℝ) (hF : ∀ k x,0<F k x)
    {x y : X} (B C : ℝ≥0) (hB : ∀ k,F k y/F k x≤B) (hC : ∀ k,F k y/F k x≤C) :
    cappedDiagonal F B x y=cappedDiagonal F C x y := by
  ext u k
  simp only [cappedDiagonal,lpDiagonal_apply,cappedRatio,max_eq_right (div_pos (hF _ _) (hF _ _)).le,
    min_eq_right (hB _),min_eq_right (hC _)]

lemma ae_hybrid_pair (P : ModelProjectionField) (j D : ℕ) :
    ∀ᵐ ω ∂actualSystem.probability (stageTagged j),
      (1-P.p (hybridEndpoint D ω))*cappedDiagonal modelF 1 (firstEndpoint ω) (hybridEndpoint D ω)*P.p (firstEndpoint ω)=0 := by
  have hg : ∀ᵐ x : CircleX, ∀ a : Fin (frequency (D+1)),
      (1-P.p (x+rationalPoint D a))*cappedDiagonal modelF (rationalCap D) x (x+rationalPoint D a)*P.p x=0 :=
    ae_all_iff.mpr (rational_pair P D)
  have hh := ae_of_ae_map firstEndpoint_measurable.aemeasurable
    ((actualSystem.hybrid_ac (stageTagged j) (fun _ => false) (summable_actual_error j)).ae_le hg)
  filter_upwards [hh,ae_endpoint_good j (fun _ => false),ae_endpoint_good j (hybridChoice D),ae_hybrid_coordinate_order j D] with ω hω hx hy hord
  obtain ⟨a,ha⟩ := actual_hybrid_grid D ω
  have hb (k : ℤ) : modelF k (hybridEndpoint D ω)/modelF k (firstEndpoint ω) ≤ 1 := modelF_ratio_ordered hx hy hord k
  have he := cappedDiagonal_eq_of_ratio_le modelF modelF_pos (rationalCap D) 1
    (fun k => (hb k).trans (rationalCap_ge_one D)) hb
  rw [←he,ha]
  exact hω a

def actualPairLaw (j : ℕ) (e : ℕ → Bool) : FiniteMeasure (CircleX×CircleX) :=
  ⟨Measure.map (fun ω => (firstEndpoint ω,actualSystem.endpoint e ω)) (actualSystem.probability (stageTagged j)),inferInstance⟩
lemma actualPairLaw_uc (j : ℕ) (e : ℕ → ℕ → Bool) :
    ∀ ε : ℝ≥0∞, ε≠0 → ∃ δ : ℝ≥0∞, δ≠0 ∧ ∀ A : Set CircleX, volume A<δ → ∀ D,
      (actualPairLaw j (e D):Measure (CircleX×CircleX)) (Prod.fst ⁻¹' A) ≤ ε ∧
      (actualPairLaw j (e D):Measure (CircleX×CircleX)) (Prod.snd ⁻¹' A) ≤ ε := by
  have hf := finiteMeasure_sqrt_uc volume (fun D => (actualPairLaw j (e D):Measure (CircleX×CircleX))) Prod.fst measurable_fst marginalConstant_pos
    (by
      intro D A hA
      change (Measure.map (fun ω => (firstEndpoint ω,actualSystem.endpoint (e D) ω)) (actualSystem.probability (stageTagged j)) (Prod.fst ⁻¹' A)).toReal ≤ _
      rw [Measure.map_apply (firstEndpoint_measurable.prodMk (actualSystem.measurable_endpoint _)) (hA.preimage measurable_fst)]
      exact actual_hybrid_bound j (fun _ => false) A hA)
  have hs := finiteMeasure_sqrt_uc volume (fun D => (actualPairLaw j (e D):Measure (CircleX×CircleX))) Prod.snd measurable_snd marginalConstant_pos
    (by
      intro D A hA
      change (Measure.map (fun ω => (firstEndpoint ω,actualSystem.endpoint (e D) ω)) (actualSystem.probability (stageTagged j)) (Prod.snd ⁻¹' A)).toReal ≤ _
      rw [Measure.map_apply (firstEndpoint_measurable.prodMk (actualSystem.measurable_endpoint _)) (hA.preimage measurable_snd)]
      exact actual_hybrid_bound j (e D) A hA)
  intro ε hε
  obtain ⟨δ,hδ,hf⟩ := hf ε hε
  obtain ⟨η,hη,hs⟩ := hs ε hε
  refine ⟨min δ η,ne_of_gt (lt_min (pos_iff_ne_zero.mpr hδ) (pos_iff_ne_zero.mpr hη)),?_⟩
  intro A hA D
  exact ⟨hf A (lt_of_lt_of_le hA (min_le_left _ _)) D,hs A (lt_of_lt_of_le hA (min_le_right _ _)) D⟩

lemma actualPairLaw_tendsto (j : ℕ) : Tendsto (fun D => actualPairLaw j (hybridChoice D)) atTop (𝓝 (actualPairLaw j (fun _ => true))) := by
  apply FiniteMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro φ
  have he (e : ℕ → Bool) : (∫ z,φ z ∂(actualPairLaw j e:Measure (CircleX×CircleX)))=
      ∫ ω,φ (firstEndpoint ω,actualSystem.endpoint e ω) ∂actualSystem.probability (stageTagged j) :=
    integral_map (firstEndpoint_measurable.prodMk (actualSystem.measurable_endpoint e)).aemeasurable φ.continuous.measurable.aestronglyMeasurable
  simp_rw [he]
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖φ‖)
  · intro D; exact (φ.continuous.measurable.comp (firstEndpoint_measurable.prodMk (hybridEndpoint_measurable D))).aestronglyMeasurable
  · exact integrable_const _
  · intro D; exact ae_of_all _ (fun ω => φ.norm_coe_le_norm _)
  · exact ae_of_all _ (fun ω => (φ.continuous.tendsto _).comp (tendsto_const_nhds.prodMk_nhds (actual_hybrid_tendsto ω)))

lemma actual_pair_identity (P : ModelProjectionField) (j : ℕ) :
    ∀ᵐ ω ∂actualSystem.probability (stageTagged j),
      (1-P.p (lastEndpoint ω))*cappedDiagonal modelF 1 (firstEndpoint ω) (lastEndpoint ω)*P.p (firstEndpoint ω)=0 := by
  have hg (D : ℕ) : ∀ᵐ z ∂(actualPairLaw j (hybridChoice D):Measure (CircleX×CircleX)),
      (1-P.p z.2)*cappedDiagonal modelF 1 z.1 z.2*P.p z.1=0 := by
    have hm : MeasurableSet {z : CircleX×CircleX | (1-P.p z.2)*cappedDiagonal modelF 1 z.1 z.2*P.p z.1=0} := by
      convert measurableSet_cappedPairRelation P.p P.measurable modelF modelF_measurable 1 using 1
      ext z; exact (cappedPairRelation_iff P.p modelF 1 z.1 z.2).symm
    exact (ae_map_iff (firstEndpoint_measurable.prodMk (hybridEndpoint_measurable D)).aemeasurable hm).mpr (ae_hybrid_pair P j D)
  have hh := capped_pair_identity_transfer (μ := volume) (νs := fun D => actualPairLaw j (hybridChoice D))
    P.p P.norm_le P.measurable modelF modelF_measurable modelF_pos 1 (actualPairLaw_tendsto j) hg (actualPairLaw_uc j hybridChoice)
  exact ae_of_ae_map (firstEndpoint_measurable.prodMk lastEndpoint_measurable).aemeasurable hh
end CircleSampling

end

end OAI

import OAI.Analysis.RotationWeights.TailBounds

namespace OAI

noncomputable section

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

namespace ContinuousCircleWeight

section
open MeasureTheory
open scoped ENNReal

lemma fiber_squares (ξ : FiberHilbert) : (∑' i,‖ξ i‖ₑ^2)=ENNReal.ofReal (‖ξ‖^2) := by
  have hs : HasSum (fun i => ‖ξ i‖^2) (‖ξ‖^2) := by
    simpa using lp.hasSum_norm (show (0:ℝ)<(2:ℝ≥0∞).toReal by norm_num) ξ
  rw [←hs.tsum_eq,ENNReal.ofReal_tsum_of_nonneg (fun i => sq_nonneg _) hs.summable]
  apply tsum_congr
  intro i
  rw [ENNReal.ofReal_pow (norm_nonneg _),ofReal_norm]
lemma fiber_squares_le {ξ : FiberHilbert} (hξ : ‖ξ‖ ≤ 1) : (∑' i,‖ξ i‖ₑ^2) ≤ 1 := by
  rw [fiber_squares]
  have hh : ‖ξ‖^2 ≤ (1:ℝ) := by nlinarith [norm_nonneg ξ]
  exact (ENNReal.ofReal_le_ofReal hh).trans_eq (by simp)
lemma fiber_product_le {ξ η : FiberHilbert} (hξ : ‖ξ‖ ≤ 1) (hη : ‖η‖ ≤ 1) :
    (∑' i,‖ξ i‖ₑ*‖η i‖ₑ) ≤ 1 := by
  have hc : (2:ℝ≥0∞).toReal.HolderConjugate (2:ℝ≥0∞).toReal := by norm_num [Real.holderConjugate_iff]
  have hh := lp.tsum_mul_le_mul_norm hc ξ η
  have ht : ∑' i,‖ξ i‖*‖η i‖ ≤ 1 := hh.2.trans (by nlinarith [norm_nonneg ξ,norm_nonneg η])
  have he : (∑' i,‖ξ i‖ₑ*‖η i‖ₑ)=ENNReal.ofReal (∑' i,‖ξ i‖*‖η i‖) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun i => mul_nonneg (norm_nonneg _) (norm_nonneg _)) hh.1]
    simp only [ENNReal.ofReal_mul (norm_nonneg _),ofReal_norm]
  rw [he]
  exact (ENNReal.ofReal_le_ofReal ht).trans_eq (by simp)
lemma projection_vector_norm (q : FiberOperator) (hq : IsStarProjection q) (k : ℤ) :
    ‖q (lp.single 2 k 1)‖ ≤ 1 := by
  have hh := q.le_opNorm (lp.single 2 k 1)
  have he : ‖(lp.single 2 k (1:ℂ):FiberHilbert)‖=1 := by simp
  rw [he,mul_one] at hh
  exact hh.trans (hq.norm_le q)
end

open scoped BigOperators

def laurentArray (K : ℕ) (a : ℤ → ℂ) (i : Fin (2*K+1)) : ℂ := a ((i.val:ℤ)-(K:ℤ))
def retainedIndices (K n : ℕ) : Finset ℤ := Finset.Icc (-(K:ℤ)) ((K:ℤ)-(n:ℤ))
lemma mem_retainedIndices (K n : ℕ) (v : ℤ) : v∈retainedIndices K n ↔ |v| ≤ (K:ℤ) ∧ |(n:ℤ)+v| ≤ (K:ℤ) := by
  simp only [retainedIndices,Finset.mem_Icc,abs_le]
  omega
lemma laurent_coeff (K : ℕ) (a : ℤ → ℂ) (i : ℕ) (hi : i ≤ 2*K) :
    (shiftedPolynomial K (laurentArray K a)).coeff i=a ((i:ℤ)-(K:ℤ)) := by
  exact coeff_shiftedPolynomial K (laurentArray K a) ⟨i,by omega⟩
lemma lowProduct_convolution (K : ℕ) (a b : ℤ → ℂ) (t : Fin (2*K+1)) :
    lowProduct K (laurentArray K a,laurentArray K b) t =
      ∑ v∈retainedIndices K (2*K-t.val), a v*b (-((2*K-t.val:ℕ):ℤ)-v) := by
  classical
  unfold lowProduct
  rw [Polynomial.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  have ht := t.isLt
  have hs : (∑ i∈Finset.range (t.val+1),
      (shiftedPolynomial K (laurentArray K a)).coeff i*(shiftedPolynomial K (laurentArray K b)).coeff (t.val-i)) =
      ∑ i∈Finset.range (t.val+1), a ((i:ℤ)-(K:ℤ))*b (((t.val-i:ℕ):ℤ)-(K:ℤ)) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hh := Finset.mem_range.mp hi
    rw [laurent_coeff K a i (by omega),laurent_coeff K b (t.val-i) (by omega)]
  rw [hs]
  apply Finset.sum_bij (fun (i:ℕ) _ => (i:ℤ)-(K:ℤ))
  · intro i hi
    simp only [retainedIndices,Finset.mem_Icc]
    have hh := Finset.mem_range.mp hi
    omega
  · intro i hi k hk he
    omega
  · intro v hv
    have hv' := Finset.mem_Icc.mp hv
    refine ⟨(v+(K:ℤ)).toNat,?_,?_⟩
    · simp only [Finset.mem_range]
      omega
    · omega
  · intro i hi
    have hh := Finset.mem_range.mp hi
    congr 2
    omega
end ContinuousCircleWeight

namespace CircleSampling

section

section
open MeasureTheory Set Filter ContinuousCircleWeight
open scoped Topology ENNReal ComplexInnerProductSpace BigOperators
local instance : MeasurableSpace FiberHilbert := borel FiberHilbert
local instance : BorelSpace FiberHilbert := ⟨rfl⟩

def modelColumn (P : ModelProjectionField) (x : CircleX) : FiberHilbert := P.p x (lp.single 2 0 1)
def modelComplement (P : ModelProjectionField) (x : CircleX) : FiberHilbert := (1-P.p x) (lp.single 2 0 1)
def modelDiagonal (P : ModelProjectionField) (x : CircleX) : ℝ := (modelColumn P x 0).re
lemma modelColumn_norm (P : ModelProjectionField) (x : CircleX) : ‖modelColumn P x‖ ≤ 1 := projection_vector_norm _ (P.projection x) 0
lemma modelComplement_norm (P : ModelProjectionField) (x : CircleX) : ‖modelComplement P x‖ ≤ 1 := projection_vector_norm _ (P.projection x).one_sub 0
lemma modelColumn_measurable (P : ModelProjectionField) : Measurable (modelColumn P) := P.measurable 0
lemma modelComplement_measurable (P : ModelProjectionField) : Measurable (modelComplement P) :=
  (measurable_const.sub (modelColumn_measurable P) : Measurable (fun x => (lp.single 2 0 1: FiberHilbert)-modelColumn P x))
lemma modelColumn_coordinate (P : ModelProjectionField) (k : ℤ) : Measurable (fun x => modelColumn P x k) :=
  (lp.evalCLM ℂ (fun _ : ℤ => ℂ) (2:ℝ≥0∞) k).continuous.measurable.comp (modelColumn_measurable P)
lemma modelComplement_coordinate (P : ModelProjectionField) (k : ℤ) : Measurable (fun x => modelComplement P x k) :=
  (lp.evalCLM ℂ (fun _ : ℤ => ℂ) (2:ℝ≥0∞) k).continuous.measurable.comp (modelComplement_measurable P)
lemma modelDiagonal_measurable (P : ModelProjectionField) : Measurable (modelDiagonal P) := (modelColumn_coordinate P 0).re

def modelTerm (P : ModelProjectionField) (n : ℕ) (v : ℤ) (ω : ActualSamples) : ℂ :=
  (modelF ((n:ℤ)+v) (lastEndpoint ω)/modelF v (firstEndpoint ω):ℝ)*modelColumn P (firstEndpoint ω) v*starRingEnd ℂ (modelComplement P (lastEndpoint ω) ((n:ℤ)+v))
def modelRetained (P : ModelProjectionField) (j n : ℕ) (ω : ActualSamples) : ℂ :=
  ∑ v∈retainedIndices (polynomialWindow j) n,modelTerm P n v ω
lemma modelTerm_measurable (P : ModelProjectionField) (n : ℕ) (v : ℤ) : Measurable (modelTerm P n v) := by
  exact (((((modelF_measurable _).comp lastEndpoint_measurable).div
    ((modelF_measurable v).comp firstEndpoint_measurable)).complex_ofReal.mul
    ((modelColumn_coordinate P v).comp firstEndpoint_measurable)).mul
    (Complex.continuous_conj.measurable.comp ((modelComplement_coordinate P _).comp lastEndpoint_measurable)))

lemma modelRetained_measurable (P : ModelProjectionField) (j n : ℕ) : Measurable (modelRetained P j n) :=
  Finset.measurable_sum _ (fun v _ => modelTerm_measurable P n v)

lemma regular_model_order {ω : ActualSamples} (hω : ω∈regularSamples) (k : ℤ) :
    modelF k (lastEndpoint ω) ≤ modelF k (firstEndpoint ω) :=
  (div_le_one (modelF_pos _ _)).mp (modelF_ratio_ordered hω.2.1 hω.2.2.1 (regular_order hω) k)
lemma model_pair_convolution (P : ModelProjectionField) {ω : ActualSamples} (hω : ω∈regularSamples)
    (hpair : (1-P.p (lastEndpoint ω))*cappedDiagonal modelF 1 (firstEndpoint ω) (lastEndpoint ω)*P.p (firstEndpoint ω)=0)
    (hinv : (1-P.p (lastEndpoint ω))*fiberCocycleShift (fun k => modelF k (lastEndpoint ω))
      (fun k => modelF_pos k (lastEndpoint ω)) (modelF_antitone (lastEndpoint ω))*P.p (lastEndpoint ω)=0) (n : ℕ) :
    Summable (fun v => modelTerm P n v ω) ∧ (∑' v,modelTerm P n v ω)=0 := by
  let x := firstEndpoint ω
  let y := lastEndpoint ω
  have ho : ∀ k,modelF k y ≤ modelF k x := regular_model_order hω
  have hd : cappedDiagonal modelF 1 x y=cocycleRatioDiagonal (fun k => modelF k x) (fun k => modelF k y)
      (fun k => modelF_pos k x) (fun k => modelF_pos k y) ho := by
    ext u k
    rw [cappedDiagonal_apply_of_bound modelF modelF_pos 1 x y (fun k => (div_le_one (modelF_pos _ _)).mpr (ho k)),cocycleRatioDiagonal_apply]
  have hf : P.p y (cocycleRatioDiagonal (fun k => modelF k x) (fun k => modelF k y)
      (fun k => modelF_pos k x) (fun k => modelF_pos k y) ho (modelColumn P x))=
      cocycleRatioDiagonal (fun k => modelF k x) (fun k => modelF k y)
      (fun k => modelF_pos k x) (fun k => modelF_pos k y) ho (modelColumn P x) := by
    have hh := congrArg (fun A : FiberOperator => A (lp.single 2 0 1)) hpair
    change cappedDiagonal modelF 1 x y (modelColumn P x)-P.p y (cappedDiagonal modelF 1 x y (modelColumn P x))=0 at hh
    rw [hd] at hh
    exact (sub_eq_zero.mp hh).symm
  exact fiber_full_convolution (fun k => modelF k x) (fun k => modelF k y) (fun k => modelF_pos k x)
    (fun k => modelF_pos k y) (modelF_antitone y) ho (P.p y) (P.projection y) hinv (modelColumn P x) (lp.single 2 0 1) hf n
lemma model_convolution_ae (P : ModelProjectionField) (j : ℕ) :
    ∀ᵐ ω ∂actualSystem.probability (stageTagged j),ω∈regularSamples ∧ ∀ n : ℕ,
      Summable (fun v => modelTerm P n v ω) ∧ (∑' v,modelTerm P n v ω)=0 := by
  have hi : ∀ᵐ ω ∂actualSystem.probability (stageTagged j),
      (1-P.p (lastEndpoint ω))*fiberCocycleShift (fun k => modelF k (lastEndpoint ω)) (fun k => modelF_pos k (lastEndpoint ω)) (modelF_antitone (lastEndpoint ω))*P.p (lastEndpoint ω)=0 :=
    ae_of_ae_map lastEndpoint_measurable.aemeasurable ((actualSystem.hybrid_ac (stageTagged j) (fun _ => true) (summable_actual_error j)).ae_le P.invariant)
  filter_upwards [ae_regularSamples j,actual_pair_identity P j,hi] with ω hω hp hi
  exact ⟨hω,fun n => model_pair_convolution P hω hp hi n⟩

def modelCoefficientPair (P : ModelProjectionField) (j : ℕ) (ω : ActualSamples) : CoefficientPair (polynomialWindow j) :=
  (laurentArray (polynomialWindow j) (fun v => (1/modelF v (firstEndpoint ω):ℝ)*modelColumn P (firstEndpoint ω) v),
   laurentArray (polynomialWindow j) (fun v => (modelF (-v) (lastEndpoint ω):ℂ)*starRingEnd ℂ (modelComplement P (lastEndpoint ω) (-v))))
lemma modelCoefficient_identity (P : ModelProjectionField) (j : ℕ) (ω : ActualSamples) (t : Fin (2*polynomialWindow j+1)) :
    lowProduct (polynomialWindow j) (modelCoefficientPair P j ω) t=modelRetained P j (2*polynomialWindow j-t.val) ω := by
  rw [modelCoefficientPair,lowProduct_convolution]
  apply Finset.sum_congr rfl
  intro v _
  simp only [neg_sub,modelTerm]
  push_cast
  ring_nf
end

open MeasureTheory Set Filter ContinuousCircleWeight
open scoped ENNReal ComplexInnerProductSpace BigOperators

lemma modelColumn_coordinate_bound (P : ModelProjectionField) (x : CircleX) (v : ℤ) :
    ‖modelColumn P x v‖ ≤ 1 := (lp.norm_apply_le_norm (by norm_num) _ _).trans (modelColumn_norm P x)
lemma modelComplement_coordinate_bound (P : ModelProjectionField) (x : CircleX) (v : ℤ) :
    ‖modelComplement P x v‖ ≤ 1 := (lp.norm_apply_le_norm (by norm_num) _ _).trans (modelComplement_norm P x)
lemma modelComplement_zero_re (P : ModelProjectionField) (x : CircleX) :
    (modelComplement P x 0).re=1-modelDiagonal P x := by
  change (((lp.single 2 0 1: FiberHilbert)-modelColumn P x) 0).re=_
  simp [modelDiagonal]

lemma modelCoefficient_bounds (P : ModelProjectionField) (j : ℕ) {ω : ActualSamples}
    (hω : ω∈regularSamples) (he : ω∈projectionEvent (modelDiagonal P) j) :
    (∀ i,‖(modelCoefficientPair P j ω).1 i‖ ≤ coefficientCap j) ∧
    (∀ i,‖(modelCoefficientPair P j ω).2 i‖ ≤ coefficientCap j) := by
  constructor
  · intro i
    have hi : |(i.val:ℤ)-(polynomialWindow j:ℤ)| ≤ (polynomialWindow j:ℤ) := by
      rw [abs_le]; have hh := i.isLt; omega
    have hh := (event_window_bounds j hω he _ hi).1
    change ‖((1/modelF _ (firstEndpoint ω):ℝ):ℂ)*modelColumn P (firstEndpoint ω) _‖ ≤ _
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr (modelF_pos _ _))]
    exact (mul_le_mul_of_nonneg_left (modelColumn_coordinate_bound P _ _) ((one_div_pos.mpr (modelF_pos _ _)).le)).trans (by simpa using hh)
  · intro i
    have hi : |(i.val:ℤ)-(polynomialWindow j:ℤ)| ≤ (polynomialWindow j:ℤ) := by
      rw [abs_le]; have hh := i.isLt; omega
    have hh := (event_window_bounds j hω he _ hi).2
    change ‖(modelF _ (lastEndpoint ω):ℂ)*starRingEnd ℂ (modelComplement P (lastEndpoint ω) _)‖ ≤ _
    rw [norm_mul,Complex.norm_conj,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (modelF_pos _ _)]
    exact (mul_le_mul_of_nonneg_left (modelComplement_coordinate_bound P _ _) (modelF_pos _ _).le).trans (by simpa using hh)

lemma modelCoefficient_centers (P : ModelProjectionField) (j : ℕ) {ω : ActualSamples}
    (he : ω∈projectionEvent (modelDiagonal P) j) :
    1/((j:ℝ)+1) ≤ ‖(modelCoefficientPair P j ω).1 (centerIndex (polynomialWindow j))‖ ∧
    1/((j:ℝ)+1) ≤ ‖(modelCoefficientPair P j ω).2 (centerIndex (polynomialWindow j))‖ := by
  have hh := projectionEvent_mem he
  have ha : (modelCoefficientPair P j ω).1 (centerIndex (polynomialWindow j))=modelColumn P (firstEndpoint ω) 0 := by
    simp [modelCoefficientPair,laurentArray,centerIndex,modelF_zero]
  have hb : (modelCoefficientPair P j ω).2 (centerIndex (polynomialWindow j))=starRingEnd ℂ (modelComplement P (lastEndpoint ω) 0) := by
    simp [modelCoefficientPair,laurentArray,centerIndex,modelF_zero]
  rw [ha,hb,Complex.norm_conj]
  exact ⟨hh.2.2.2.1.trans (Complex.re_le_norm _),hh.2.2.2.2.trans (by rw [←modelComplement_zero_re]; exact Complex.re_le_norm _)⟩

lemma model_coefficient_lower (P : ModelProjectionField) (j : ℕ) {ω : ActualSamples}
    (hω : ω∈regularSamples) (he : ω∈projectionEvent (modelDiagonal P) j) :
    ∃ t : Fin (2*polynomialWindow j+1), (scaleStep j).ε ≤ ‖modelRetained P j (2*polynomialWindow j-t.val) ω‖ := by
  have hb := modelCoefficient_bounds P j hω he
  have hc := modelCoefficient_centers P j he
  obtain ⟨t,ht⟩ := (scaleStep j).coefficients (modelCoefficientPair P j ω) hb.1 hb.2 hc.1 hc.2
  change Fin (2*polynomialWindow j+1) at t
  change (scaleStep j).ε ≤ ‖lowProduct (polynomialWindow j) (modelCoefficientPair P j ω) t‖ at ht
  rw [modelCoefficient_identity] at ht
  exact ⟨t,ht⟩
end

open MeasureTheory Set Filter CircleCoupling CircleDigits
open scoped ENNReal

lemma all_masks (j : ℕ) (k : ℤ) (hk : (polynomialWindow j:ℝ)< |(k:ℝ)|) :
    ∃ H₁ H₂ : Set ActualSamples,MeasurableSet H₁ ∧ MeasurableSet H₂ ∧
      Measure.map firstEndpoint ((actualSystem.probability (stageTagged j)).restrict H₁) ≤ ENNReal.ofReal (Real.exp (-crossingBudget j/400)) • Measure.map firstEndpoint (actualSystem.probability (stageTagged j)) ∧
      Measure.map lastEndpoint ((actualSystem.probability (stageTagged j)).restrict H₂) ≤ ENNReal.ofReal (Real.exp (-crossingBudget j/400)) • Measure.map lastEndpoint (actualSystem.probability (stageTagged j)) ∧
      ∀ ω∈regularSamples,ω∈stageTagEvent j → ω∉H₁ → ω∉H₂ → modelF k (lastEndpoint ω)/modelF k (firstEndpoint ω) ≤ Real.exp (-crossingBudget j) := by
  by_cases hh : blockScale j/4< |(k:ℝ)|
  · obtain ⟨H₁,H₂,hm₁,hm₂,hd₁,hd₂,hc⟩ := large_masks j k hh
    exact ⟨H₁,H₂,hm₁,hm₂,hd₁,hd₂,fun ω hω _ h₁ h₂ => hc ω hω h₁ h₂⟩
  · refine ⟨∅,∅,MeasurableSet.empty,MeasurableSet.empty,by simp; exact bot_le,by simp; exact bot_le,?_⟩
    exact fun ω hω ht _ _ => short_ratio j k hk (le_of_not_gt hh) hω ht

def longIndex (j n : ℕ) (v : ℤ) : ℤ := if (polynomialWindow j:ℤ)< |v| then v else (n:ℤ)+v
lemma longIndex_long (j n : ℕ) (v : ℤ) (hv : v∉ContinuousCircleWeight.retainedIndices (polynomialWindow j) n) :
    (polynomialWindow j:ℝ)< |((longIndex j n v):ℝ)| := by
  rw [ContinuousCircleWeight.mem_retainedIndices] at hv
  have hh : (polynomialWindow j:ℤ)< |longIndex j n v| := by
    unfold longIndex
    split_ifs with h
    · exact h
    · push Not at hv
      exact hv (le_of_not_gt h)
  exact_mod_cast hh
end CircleSampling

end

end OAI

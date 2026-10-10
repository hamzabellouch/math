import OAI.Analysis.RotationWeights.MaskedEstimates

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
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

section
open MeasureTheory Set Filter ContinuousCircleWeight
open scoped ENNReal BigOperators

structure ConvolutionMasks (j n : ℕ) where
  left : ℤ → Set ActualSamples
  right : ℤ → Set ActualSamples
  left_measurable : ∀ v,MeasurableSet (left v)
  right_measurable : ∀ v,MeasurableSet (right v)
  left_dom : ∀ v,Measure.map firstEndpoint ((actualSystem.probability (stageTagged j)).restrict (left v)) ≤
    ENNReal.ofReal (Real.exp (-crossingBudget j/400)) • Measure.map firstEndpoint (actualSystem.probability (stageTagged j))
  right_dom : ∀ v,Measure.map lastEndpoint ((actualSystem.probability (stageTagged j)).restrict (right v)) ≤
    ENNReal.ofReal (Real.exp (-crossingBudget j/400)) • Measure.map lastEndpoint (actualSystem.probability (stageTagged j))
  decay : ∀ v,v∉retainedIndices (polynomialWindow j) n → ∀ ω∈regularSamples,ω∈stageTagEvent j →
    ω∉left v → ω∉right v → modelF (longIndex j n v) (lastEndpoint ω)/modelF (longIndex j n v) (firstEndpoint ω) ≤ Real.exp (-crossingBudget j)

lemma convolutionMasks_nonempty (j n : ℕ) : Nonempty (ConvolutionMasks j n) := by
  classical
  have hex (v : ℤ) : ∃ H₁ H₂ : Set ActualSamples,MeasurableSet H₁ ∧ MeasurableSet H₂ ∧
      Measure.map firstEndpoint ((actualSystem.probability (stageTagged j)).restrict H₁) ≤ ENNReal.ofReal (Real.exp (-crossingBudget j/400)) • Measure.map firstEndpoint (actualSystem.probability (stageTagged j)) ∧
      Measure.map lastEndpoint ((actualSystem.probability (stageTagged j)).restrict H₂) ≤ ENNReal.ofReal (Real.exp (-crossingBudget j/400)) • Measure.map lastEndpoint (actualSystem.probability (stageTagged j)) ∧
      (v∉retainedIndices (polynomialWindow j) n → ∀ ω∈regularSamples,ω∈stageTagEvent j → ω∉H₁ → ω∉H₂ → modelF (longIndex j n v) (lastEndpoint ω)/modelF (longIndex j n v) (firstEndpoint ω) ≤ Real.exp (-crossingBudget j)) := by
    by_cases hv : v∈retainedIndices (polynomialWindow j) n
    · exact ⟨∅,∅,MeasurableSet.empty,MeasurableSet.empty,by simp; exact bot_le,by simp; exact bot_le,fun h => False.elim (h hv)⟩
    · obtain ⟨A,B,hA,hB,hdA,hdB,hc⟩ := all_masks j _ (longIndex_long j n v hv)
      exact ⟨A,B,hA,hB,hdA,hdB,fun _ => hc⟩
  choose A B hA hB hdA hdB hc using hex
  exact ⟨⟨A,B,hA,hB,hdA,hdB,hc⟩⟩
def convolutionMasks (j n : ℕ) : ConvolutionMasks j n := Classical.choice (convolutionMasks_nonempty j n)

lemma model_ratio_bounds {ω : ActualSamples} (hω : ω∈regularSamples) (j n : ℕ) (v : ℤ) :
    0 < modelF ((n:ℤ)+v) (lastEndpoint ω)/modelF v (firstEndpoint ω) ∧
    modelF ((n:ℤ)+v) (lastEndpoint ω)/modelF v (firstEndpoint ω) ≤ 1 ∧
    modelF ((n:ℤ)+v) (lastEndpoint ω)/modelF v (firstEndpoint ω) ≤
      modelF (longIndex j n v) (lastEndpoint ω)/modelF (longIndex j n v) (firstEndpoint ω) := by
  have hh := cocycle_two_ratio_bounds (fun k => modelF k (firstEndpoint ω)) (fun k => modelF k (lastEndpoint ω))
    (fun k => modelF_pos k _) (fun k => modelF_pos k _) (modelF_antitone _) (modelF_antitone _) (regular_model_order hω) n v
  refine ⟨hh.1,hh.2.1.trans hh.2.2.2.1,?_⟩
  unfold longIndex
  split_ifs
  · exact hh.2.1
  · exact hh.2.2.1

lemma model_ratio_masked {ω : ActualSamples} (hω : ω∈regularSamples) (j n : ℕ) (v : ℤ)
    (hv : v∉retainedIndices (polynomialWindow j) n) (ht : ω∈stageTagEvent j) :
    ENNReal.ofReal (modelF ((n:ℤ)+v) (lastEndpoint ω)/modelF v (firstEndpoint ω)) ≤
      ENNReal.ofReal (Real.exp (-crossingBudget j))+
        ((convolutionMasks j n).left v).indicator (fun _ => (1:ℝ≥0∞)) ω+
        ((convolutionMasks j n).right v).indicator (fun _ => (1:ℝ≥0∞)) ω := by
  classical
  have hh := model_ratio_bounds hω j n v
  have hone : ENNReal.ofReal (modelF ((n:ℤ)+v) (lastEndpoint ω)/modelF v (firstEndpoint ω)) ≤ 1 := by
    simpa using ENNReal.ofReal_le_ofReal hh.2.1
  by_cases hl : ω∈(convolutionMasks j n).left v
  · simp only [Set.indicator_of_mem hl]
    exact hone.trans ((le_add_self).trans le_self_add)
  · by_cases hr : ω∈(convolutionMasks j n).right v
    · simp only [Set.indicator_of_notMem hl,Set.indicator_of_mem hr,add_zero]
      exact hone.trans le_add_self
    · simp only [Set.indicator_of_notMem hl,Set.indicator_of_notMem hr,add_zero]
      exact ENNReal.ofReal_le_ofReal (hh.2.2.trans ((convolutionMasks j n).decay v hv ω hω ht hl hr))

lemma shifted_complement_squares (P : ModelProjectionField) (y : CircleX) (n : ℕ) :
    (∑' v : ℤ,‖modelComplement P y ((n:ℤ)+v)‖ₑ^2) ≤ 1 := by
  have hh := fiber_squares_le (modelComplement_norm P y)
  rwa [←(Equiv.addLeft (n:ℤ)).tsum_eq] at hh
lemma shifted_product_bound (P : ModelProjectionField) (x y : CircleX) (n : ℕ) :
    (∑' v : ℤ,‖modelColumn P x v‖ₑ*‖modelComplement P y ((n:ℤ)+v)‖ₑ) ≤ 1 := by
  have hh := fiber_product_le (modelColumn_norm P x) (show ‖fiberShift (-(n:ℤ)) (modelComplement P y)‖ ≤ 1 by simpa using modelComplement_norm P y)
  simpa only [fiberShift_apply,sub_neg_eq_add,add_comm] using hh

lemma modelTerm_enorm (P : ModelProjectionField) (n : ℕ) (v : ℤ) (ω : ActualSamples) :
    ‖modelTerm P n v ω‖ₑ=‖modelColumn P (firstEndpoint ω) v‖ₑ*‖modelComplement P (lastEndpoint ω) ((n:ℤ)+v)‖ₑ*
      ENNReal.ofReal (modelF ((n:ℤ)+v) (lastEndpoint ω)/modelF v (firstEndpoint ω)) := by
  rw [←ofReal_norm,modelTerm,norm_mul,norm_mul,Complex.norm_conj,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (div_pos (modelF_pos _ _) (modelF_pos _ _)),
    ENNReal.ofReal_mul (mul_nonneg (div_pos (modelF_pos _ _) (modelF_pos _ _)).le (norm_nonneg _)),
    ENNReal.ofReal_mul (div_pos (modelF_pos _ _) (modelF_pos _ _)).le,ofReal_norm,ofReal_norm]
  ring

lemma modelRetained_cut (P : ModelProjectionField) (j n : ℕ) {ω : ActualSamples}
    (hω : ω∈regularSamples) (ht : ω∈stageTagEvent j)
    (hc : Summable (fun v => modelTerm P n v ω) ∧ (∑' v,modelTerm P n v ω)=0) :
    ‖modelRetained P j n ω‖ₑ ≤ ENNReal.ofReal (Real.exp (-crossingBudget j))+
      (∑' v, ((convolutionMasks j n).left v).indicator (fun ω => ‖modelColumn P (firstEndpoint ω) v‖ₑ*‖modelComplement P (lastEndpoint ω) ((n:ℤ)+v)‖ₑ) ω)+
      (∑' v, ((convolutionMasks j n).right v).indicator (fun ω => ‖modelColumn P (firstEndpoint ω) v‖ₑ*‖modelComplement P (lastEndpoint ω) ((n:ℤ)+v)‖ₑ) ω) := by
  classical
  have hh := convolution_cut_bound (fun v => modelTerm P n v ω) (retainedIndices (polynomialWindow j) n)
    hc.1 hc.2 (fun v => ‖modelColumn P (firstEndpoint ω) v‖ₑ) (fun v => ‖modelComplement P (lastEndpoint ω) ((n:ℤ)+v)‖ₑ)
    (fun v => ((convolutionMasks j n).left v).indicator (fun _ => (1:ℝ≥0∞)) ω)
    (fun v => ((convolutionMasks j n).right v).indicator (fun _ => (1:ℝ≥0∞)) ω)
    (ENNReal.ofReal (Real.exp (-crossingBudget j))) (shifted_product_bound P _ _ n) (fun v hv => by
      rw [modelTerm_enorm P n v ω]
      exact mul_le_mul' le_rfl (model_ratio_masked hω j n v hv ht))
  have hleft (v : ℤ) : ‖modelColumn P (firstEndpoint ω) v‖ₑ*‖modelComplement P (lastEndpoint ω) ((n:ℤ)+v)‖ₑ*
      ((convolutionMasks j n).left v).indicator (fun _ => (1:ℝ≥0∞)) ω =
      ((convolutionMasks j n).left v).indicator (fun ω => ‖modelColumn P (firstEndpoint ω) v‖ₑ*‖modelComplement P (lastEndpoint ω) ((n:ℤ)+v)‖ₑ) ω := by
    by_cases h : ω∈(convolutionMasks j n).left v <;> simp [h]
  have hright (v : ℤ) : ‖modelColumn P (firstEndpoint ω) v‖ₑ*‖modelComplement P (lastEndpoint ω) ((n:ℤ)+v)‖ₑ*
      ((convolutionMasks j n).right v).indicator (fun _ => (1:ℝ≥0∞)) ω =
      ((convolutionMasks j n).right v).indicator (fun ω => ‖modelColumn P (firstEndpoint ω) v‖ₑ*‖modelComplement P (lastEndpoint ω) ((n:ℤ)+v)‖ₑ) ω := by
    by_cases h : ω∈(convolutionMasks j n).right v <;> simp [h]
  simpa only [hleft,hright,modelRetained] using hh
end

open MeasureTheory Set Filter ContinuousCircleWeight
open scoped ENNReal BigOperators Topology

def convolutionError (j : ℕ) : ℝ := Real.exp (-crossingBudget j)+2*Real.exp (-crossingBudget j/800)
lemma convolutionError_pos (j : ℕ) : 0<convolutionError j := by unfold convolutionError; positivity
lemma convolutionError_eq (j : ℕ) :
    ENNReal.ofReal (Real.exp (-crossingBudget j))+
      ENNReal.ofReal (Real.exp (-crossingBudget j/400))^(1/2:ℝ)+
      ENNReal.ofReal (Real.exp (-crossingBudget j/400))^(1/2:ℝ)=ENNReal.ofReal (convolutionError j) := by
  rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _),←Real.exp_mul]
  have he : -crossingBudget j/400*(1/2:ℝ)=-crossingBudget j/800 := by ring
  rw [he,←ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le,←ENNReal.ofReal_add (by positivity) (Real.exp_pos _).le]
  congr 1
  unfold convolutionError
  ring
lemma convolutionError_bound (j : ℕ) : convolutionError j ≤ 3*Real.exp (-crossingBudget j/10000) := by
  have hL : 0 ≤ crossingBudget j := (scaleStep j).Lge.trans' (by norm_num)
  have h₁ : Real.exp (-crossingBudget j) ≤ Real.exp (-crossingBudget j/10000) := Real.exp_le_exp.mpr (by linarith)
  have h₂ : Real.exp (-crossingBudget j/800) ≤ Real.exp (-crossingBudget j/10000) := Real.exp_le_exp.mpr (by linarith)
  unfold convolutionError
  linarith

lemma integrated_retained_bound (P : ModelProjectionField) (j n : ℕ) :
    (∫⁻ ω, (projectionEvent (modelDiagonal P) j).indicator (fun ω => ‖modelRetained P j n ω‖ₑ) ω ∂actualSystem.probability (stageTagged j)) ≤
      ENNReal.ofReal (convolutionError j) := by
  have hc : ∀ᵐ ω ∂actualSystem.probability (stageTagged j),
      (projectionEvent (modelDiagonal P) j).indicator (fun ω => ‖modelRetained P j n ω‖ₑ) ω ≤
      ENNReal.ofReal (Real.exp (-crossingBudget j))+
        (∑' v, ((convolutionMasks j n).left v).indicator (fun ω => ‖modelColumn P (firstEndpoint ω) v‖ₑ*‖modelComplement P (lastEndpoint ω) ((n:ℤ)+v)‖ₑ) ω)+
        (∑' v, ((convolutionMasks j n).right v).indicator (fun ω => ‖modelColumn P (firstEndpoint ω) v‖ₑ*‖modelComplement P (lastEndpoint ω) ((n:ℤ)+v)‖ₑ) ω) := by
    filter_upwards [model_convolution_ae P j] with ω hω
    by_cases he : ω∈projectionEvent (modelDiagonal P) j
    · rw [Set.indicator_of_mem he]
      exact modelRetained_cut P j n hω.1 he.1 (hω.2 n)
    · rw [Set.indicator_of_notMem he]
      exact zero_le
  have hh := two_endpoint_error_bound (actualSystem.probability (stageTagged j)) firstEndpoint lastEndpoint
    firstEndpoint_measurable lastEndpoint_measurable
    (fun v x => ‖modelColumn P x v‖ₑ) (fun v y => ‖modelComplement P y ((n:ℤ)+v)‖ₑ)
    (fun v => (modelColumn_coordinate P v).enorm) (fun v => (modelComplement_coordinate P _).enorm)
    (convolutionMasks j n).left (convolutionMasks j n).right
    (convolutionMasks j n).left_measurable (convolutionMasks j n).right_measurable
    (ENNReal.ofReal (Real.exp (-crossingBudget j/400))) (ENNReal.ofReal (Real.exp (-crossingBudget j)))
    (convolutionMasks j n).left_dom (convolutionMasks j n).right_dom
    (Eventually.of_forall (fun ω => fiber_squares_le (modelColumn_norm P (firstEndpoint ω))))
    (Eventually.of_forall (fun ω => shifted_complement_squares P (lastEndpoint ω) n)) _ hc
  rwa [convolutionError_eq] at hh

lemma projectionEvent_upper (P : ModelProjectionField) (j : ℕ) :
    (actualSystem.probability (stageTagged j)).real (projectionEvent (modelDiagonal P) j) ≤ 1/((j:ℝ)+1) := by
  let μ := actualSystem.probability (stageTagged j)
  let E := projectionEvent (modelDiagonal P) j
  have hE : MeasurableSet E := projectionEvent_measurable (modelDiagonal_measurable P) j
  have hlow : (ENNReal.ofReal (scaleStep j).ε)*μ E ≤
      ∫⁻ ω,∑ t : Fin (2*polynomialWindow j+1),E.indicator (fun ω => ‖modelRetained P j (2*polynomialWindow j-t.val) ω‖ₑ) ω ∂μ := by
    rw [←lintegral_indicator_const hE]
    apply lintegral_mono_ae
    filter_upwards [ae_regularSamples j] with ω hω
    by_cases he : ω∈E
    · rw [Set.indicator_of_mem he]
      obtain ⟨t,ht⟩ := model_coefficient_lower P j hω he
      calc
        _ ≤ ‖modelRetained P j (2*polynomialWindow j-t.val) ω‖ₑ := by simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal ht
        _ = E.indicator (fun ω => ‖modelRetained P j (2*polynomialWindow j-t.val) ω‖ₑ) ω := by rw [Set.indicator_of_mem he]
        _ ≤ _ := Finset.single_le_sum (f := fun t : Fin (2*polynomialWindow j+1) => E.indicator (fun ω => ‖modelRetained P j (2*polynomialWindow j-t.val) ω‖ₑ) ω) (fun _ _ => zero_le) (Finset.mem_univ t)
    · simp [he]
  have hu : (ENNReal.ofReal (scaleStep j).ε)*μ E ≤ ENNReal.ofReal ((2*(polynomialWindow j:ℝ)+1)*convolutionError j) := by
    apply hlow.trans
    rw [lintegral_finsetSum _ (fun t _ => (modelRetained_measurable P j _).enorm.indicator hE)]
    calc
      _ ≤ ∑ _t : Fin (2*polynomialWindow j+1), ENNReal.ofReal (convolutionError j) := Finset.sum_le_sum (fun t _ => integrated_retained_bound P j _)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; rw [ENNReal.ofReal_mul (by positivity)]; norm_cast
  have hreal : (scaleStep j).ε*μ.real E ≤ (2*(polynomialWindow j:ℝ)+1)*convolutionError j := by
    have hh := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hu
    simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofReal (scaleStep j).εpos.le,
      ENNReal.toReal_ofReal (mul_nonneg (by positivity : (0:ℝ)≤2*(polynomialWindow j:ℝ)+1) (convolutionError_pos j).le),measureReal_def] using hh
  have hb := (scaleStep j).exponential
  have hc : (2*(polynomialWindow j:ℝ)+1)*convolutionError j ≤ (scaleStep j).ε/((j:ℝ)+1) := by
    apply le_trans (mul_le_mul_of_nonneg_left (convolutionError_bound j) (by positivity))
    change (2*(polynomialWindow j:ℝ)+1)*3*Real.exp (-crossingBudget j/10000) ≤ (scaleStep j).ε/((j:ℝ)+1) at hb
    simpa only [mul_assoc] using hb
  have hh := hreal.trans hc
  have hε := (scaleStep j).εpos
  change μ.real E ≤ _
  nlinarith [show (scaleStep j).ε/((j:ℝ)+1)=(scaleStep j).ε*(1/((j:ℝ)+1)) by ring]

theorem model_no_strict_projection (P : ModelProjectionField)
    (hp : ∀ᵐ x,0 < modelDiagonal P x ∧ modelDiagonal P x<1) : False := by
  have hm := projectionEvent_mass (modelDiagonal_measurable P) hp
  have ht : Tendsto (fun j : ℕ => 1/((j:ℝ)+1)) atTop (𝓝 0) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have he := ht.eventually (gt_mem_nhds (by positivity : (0:ℝ)<Real.exp (-86)/2))
  obtain ⟨j,hj,hj'⟩ := (hm.and he).exists
  exact (not_lt_of_ge (hj.trans (projectionEvent_upper P j))) hj'


end CircleSampling

end

end OAI

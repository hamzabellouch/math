import OAI.Analysis.RotationWeights.LogarithmicDrops

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
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators
namespace CircleSampling

section
open CircleModel CircleRounding CircleConcentration ContinuousCircleWeight
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal

lemma blockLength_ge_index (j : ℕ) : j+1≤blockLength j := by
  induction j with
  | zero => exact (by norm_num : 1≤200).trans (blockLength_ge 0)
  | succ j ih => exact (by omega : j+1+1 ≤ blockLength j+1).trans (blockLength_strictMono (Nat.lt_succ_self j))
lemma blockH_zero_half (j : ℕ) : (1/2:ℝ)≤blockH j 0 := by
  have hm : (j:ℝ)+1≤blockLength j := by exact_mod_cast blockLength_ge_index j
  have hK : (1:ℝ)≤polynomialWindow j := by exact_mod_cast polynomialWindow_pos j
  have hc : 1≤dropSize j := by nlinarith [dropSize_ge_window_sq j]
  have hj : 0<(j:ℝ)+1 := by positivity
  calc
    _ ≤ (blockLength j:ℝ)*dropSize j/(2*((j:ℝ)+1)) := by
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith [mul_le_mul hm hc (by positivity) (by positivity)]
    _ ≤ _ := blockH_zero_lower j
lemma blockH_diverges_zero : ∀ B : ℝ, ∃ s : Finset ℕ,B<∑ j∈s,blockH j 0 := by
  intro B
  obtain ⟨N,hN⟩ := exists_nat_gt (2*B)
  refine ⟨Finset.range N,?_⟩
  calc
    B < (N:ℝ)*(1/2) := by linarith
    _ = ∑ _j∈Finset.range N,(1/2:ℝ) := by simp
    _ ≤ _ := Finset.sum_le_sum (fun j _ => blockH_zero_half j)

def finalWeight : C(CircleModel.CircleX,ℝ) :=
  ⟨concentratedWeight blockH 0,continuous_concentratedWeight blockH 0 blockH_continuous blockH_nonneg blockH_locallyFinite blockH_diverges_zero⟩
lemma finalWeight_bounds (x : CircleModel.CircleX) : 0 ≤ finalWeight x ∧ finalWeight x≤1 :=
  concentratedWeight_bounds _ _ blockH_nonneg x
lemma finalWeight_zero (x : CircleModel.CircleX) : finalWeight x=0 ↔ x=0 := concentratedWeight_eq_zero _ _ _
lemma finalWeight_log : (∫⁻ x : CircleModel.CircleX,negativeLog (finalWeight x))=∞ := by
  change (∫⁻ x : CircleModel.CircleX,negativeLog (concentratedWeight blockH 0 x))=_
  rw [lintegral_negativeLog_concentratedWeight volume blockH 0 blockH_continuous blockH_nonneg blockH_locallyFinite blockH_diverges_zero]
  apply top_unique
  calc
    ∞ = ∑' _j : ℕ,(1:ℝ≥0∞) := (ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero).symm
    _ ≤ _ := by
      apply ENNReal.tsum_le_tsum
      intro j
      have hi : Integrable (blockH j) (volume : Measure CircleModel.CircleX) := (blockH_continuous j).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      rw [←ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (blockH_nonneg j))]
      rw [←ENNReal.ofReal_one]
      apply ENNReal.ofReal_le_ofReal
      have hK : (1:ℝ)≤polynomialWindow j := by exact_mod_cast polynomialWindow_pos j
      exact hK.trans (blockH_integral_lower j)
lemma blockG_exponent {x : CircleModel.CircleX} (hx : x∈modelGood) :
    (∑' j,blockG j x)=exponent modelFrequency modelAngle coordinateDrop 1 x := by
  let f : ℕ → ℝ := fun i => coordinateDrop i*(floorTerm modelFrequency modelAngle 1 x i:ℝ)
  have hs : Summable f := summable_exponent coordinateDrop 1 hx
  calc
    _ = ∑' j,∑' i : Fin (blocks.m j),f (blocks.equiv ⟨j,i⟩) := by
      apply tsum_congr
      intro j
      rw [tsum_fintype]
      apply Finset.sum_congr rfl
      intro i _
      change dropSize j*_ = dropSize (coordinateBlock (blocks.equiv ⟨j,i⟩))*_
      rw [block_number_equiv]
    _ = ∑' ji : Σ j,Fin (blocks.m j),f (blocks.equiv ji) := (blocks.equiv.summable_iff.mpr hs).tsum_sigma.symm
    _ = _ := blocks.equiv.tsum_eq f
lemma finalWeight_coboundary : ∃ a : CircleModel.CircleX → ℝ, Measurable a ∧ (∀ x,0<a x) ∧
    ∀ᵐ x : CircleModel.CircleX, finalWeight x=modelWeight x*a x/a (x+modelAngle) := by
  have h0 : volume ({(0:CircleModel.CircleX)} : Set CircleModel.CircleX)=0 := by
    rw [←Metric.closedBall_zero,AddCircle.volume_closedBall]
    norm_num
  obtain ⟨a,ham,hapos,ha⟩ := concentrated_coboundary (volume:Measure CircleModel.CircleX)
    (fun x => x+modelAngle) (measurePreserving_add_right volume modelAngle) blockH blockG blockW 0 h0
    blockW_measurable blockG_support_sum blockW_support_sum (Eventually.of_forall (fun x j => block_coboundary j x))
  refine ⟨a,ham,hapos,?_⟩
  filter_upwards [ha,model_good_ae] with x hax hx
  change concentratedWeight blockH 0 x=_
  rw [hax,blockG_exponent hx]
  simp only [modelWeight,modelF,cocycle,ite_eq_left (show x ∈ good modelFrequency modelAngle from hx)]
end

open MeasureTheory Set Filter ContinuousCircleWeight
open scoped ComplexInnerProductSpace ENNReal
local instance : MeasurableSpace FiberHilbert := borel FiberHilbert
local instance : BorelSpace FiberHilbert := ⟨rfl⟩

def modelBorel : RealBorel where
  f := modelWeight
  measurable := modelF_measurable 1
  bound := 1
  norm_le x := by
    simpa only [Real.norm_eq_abs,abs_of_pos (modelWeight_bounds x).1,NNReal.coe_one] using (modelWeight_bounds x).2

lemma modelBorel_field (x : CircleX) : borelWeightedField modelAngle modelBorel x=
    fiberCocycleShift (fun k => modelF k x) (fun k => modelF_pos k x) (modelF_antitone x) := by
  ext u k
  change fiberShift 1 (realPiField modelAngle modelBorel x u) k=_
  rw [fiberShift_apply,realPiField_apply,fiberCocycleShift_apply]
  congr 1
  apply congrArg Complex.ofReal
  change modelF 1 (x+(k-1)•modelAngle)=modelF k x/modelF (k-1) x
  apply (eq_div_iff (ne_of_gt (modelF_pos _ _))).mpr
  simpa only [CircleModel.shift,sub_add_cancel] using (modelF_add (k-1) 1 x).symm

lemma modelAngle_ergodic : Ergodic (fun x : CircleX => x+modelAngle) AddCircle.haarAddCircle := by
  rw [Sampling.haarAddCircle_one_eq_volume]
  apply AddCircle.ergodic_add_right.mpr
  apply AddCircle.denseRange_zsmul_iff.mp
  simpa only [div_one,modelAngle] using (AddCircle.denseRange_zsmul_coe_iff (p:=(1:ℝ))).mpr (by simpa using parameterAngle_spec.2.2.1)

theorem modelOperator_no_projection (p : CircleFiberOperator) (hp : IsStarProjection p)
    (hcomm : ∀ B∈fiberCommutant parameterAngle,Commute p B)
    (hinv : (1-p)*(fiberShiftL2 1*realPi modelAngle modelBorel)*p=0) : p=0 ∨ p=1 := by
  by_cases hp0 : p=0
  · exact Or.inl hp0
  by_cases hp1 : p=1
  · exact Or.inr hp1
  exfalso
  obtain ⟨P,hPproj,hPbound,hPmeas,hP,hcov⟩ := extract_projection_field parameterAngle p hp hcomm
  let Q : ModelProjectionField :=
    { p := P
      projection := hPproj
      norm_le := hPbound
      measurable := hPmeas
      invariant := by
        have h := decomposable_invariant p P hP modelAngle modelBorel hinv
        simpa only [Sampling.haarAddCircle_one_eq_volume,modelBorel_field] using h
      covariance := by
        intro n
        simpa only [Sampling.haarAddCircle_one_eq_volume,CircleModel.shift,modelAngle] using hcov n }
  apply model_no_strict_projection Q
  have hs := borel_invariant_diagonal_strict parameterAngle modelAngle_ergodic p P hP hPproj hcov modelBorel
    (fun x => ne_of_gt (modelWeight_bounds x).1) hinv hp0 hp1
  simpa only [Sampling.haarAddCircle_one_eq_volume,lp.inner_single_left,RCLike.inner_apply,map_one,mul_one,
    modelDiagonal,modelColumn,Q] using hs

theorem continuousOperator_no_projection (p : CircleFiberOperator) (hp : IsStarProjection p)
    (hcomm : ∀ B∈fiberCommutant parameterAngle,Commute p B)
    (hinv : (1-p)*(fiberShiftL2 1*realPi modelAngle (RealBorel.ofContinuous finalWeight))*p=0) : p=0 ∨ p=1 := by
  by_cases hp0 : p=0
  · exact Or.inl hp0
  by_cases hp1 : p=1
  · exact Or.inr hp1
  exfalso
  obtain ⟨a,ham,hapos,ha⟩ := finalWeight_coboundary
  have he : ∀ᵐ x ∂AddCircle.haarAddCircle,RealBorel.ofContinuous finalWeight x*a (x+modelAngle)=modelBorel x*a x := by
    rw [Sampling.haarAddCircle_one_eq_volume]
    filter_upwards [ha] with x hx
    exact (eq_div_iff (ne_of_gt (hapos _))).mp hx
  obtain ⟨q,hq,hqc,hq0,hq1,hqi⟩ := borel_weight_transport parameterAngle (RealBorel.ofContinuous finalWeight) modelBorel a ham hapos he p hp hcomm hp0 hp1 hinv
  exact (modelOperator_no_projection q hq hqc hqi).elim hq0 hq1
end CircleSampling

namespace ContinuousCircleWeight

section
open MeasureTheory
open scoped ENNReal ComplexInnerProductSpace

lemma regular_isTracialRotation (θ : ℝ) :
    IsTracialRotation θ regularU (regularV (rotationScalar θ)) regularVacuum where
  relation := regular_relation (rotationScalar θ)
  moments := regular_moments (rotationScalar θ)
  cyclic := regular_cyclic (rotationScalar θ)

lemma fiberConjugacy_cfc (θ : ℝ) (f : C(CircleX,ℝ)) :
    fiberConjugacy (cfc (circleFunction f) (regularV (rotationScalar θ) : RegularOperator)) =
      realPi (θ:CircleX) (RealBorel.ofContinuous f) := by
  rw [realPi_continuous]
  have h := fiberConjugacy.toStarAlgHom.map_cfc (circleFunction f)
    (regularV (rotationScalar θ) : RegularOperator)
    ((circleFunction_continuousOn f).mono (Unitary.spectrum_subset_circle _))
    (StarAlgEquiv.isometry fiberConjugacy).continuous
  change fiberConjugacy _ = cfc (circleFunction f)
    (fiberConjugacy (regularV (rotationScalar θ) : RegularOperator)) at h
  rw [h,fiberConjugacy_V]
  exact (circle_cfc_hom (continuousPiHom (θ:CircleX)) (continuous_continuousPiHom _) f).symm

lemma fiberConjugacy_weighted (θ : ℝ) (f : C(CircleX,ℝ)) :
    fiberConjugacy (weightedRotation regularU (regularV (rotationScalar θ)) f) =
      fiberShiftL2 1 * realPi (θ:CircleX) (RealBorel.ofContinuous f) := by
  rw [weightedRotation,map_mul,fiberConjugacy_U,fiberConjugacy_cfc]

end

open MeasureTheory CircleSampling
open scoped ENNReal ComplexInnerProductSpace

theorem main_theorem : MainStatement := by
  refine ⟨parameterAngle, finalWeight, regularU, regularV (rotationScalar parameterAngle),
    regularVacuum, parameterAngle_spec.1, parameterAngle_spec.2.1,
    parameterAngle_spec.2.2.1, regular_isTracialRotation parameterAngle,
    finalWeight_bounds, ⟨0, finalWeight_zero⟩, finalWeight_log, ?_⟩
  intro p hp hppr hinv
  have hi : (1-fiberConjugacy p)*
      (fiberShiftL2 1*realPi modelAngle (RealBorel.ofContinuous finalWeight))*fiberConjugacy p=0 := by
    have h := congrArg fiberConjugacy hinv
    simpa only [map_mul,map_sub,map_one,map_zero,fiberConjugacy_weighted,modelAngle] using h
  have hq := continuousOperator_no_projection (fiberConjugacy p) (hppr.map fiberConjugacy)
    (fiber_commutes_of_regularAlgebra parameterAngle p hp) hi
  rcases hq with hq|hq
  · left
    apply fiberConjugacy.injective
    change fiberConjugacy p=fiberConjugacy 0
    simpa only [map_zero] using hq
  · right
    apply fiberConjugacy.injective
    change fiberConjugacy p=fiberConjugacy 1
    simpa only [map_one] using hq

end ContinuousCircleWeight

end

end OAI

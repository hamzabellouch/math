import OAI.Analysis.RotationWeights.ContinuousWeight

namespace OAI

noncomputable section

namespace CircleSampling

universe uι

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

section
open CircleModel CircleRounding CircleConcentration ContinuousCircleWeight
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal

def roundingWidth (j : ℕ) : ℝ := 1/(10*(blockLength j:ℝ)*polynomialWindow j)
lemma roundingWidth_pos (j : ℕ) : 0<roundingWidth j := by
  have hm : 0<(blockLength j:ℝ) := Nat.cast_pos.mpr (scaleStep j).mpos
  have hK : 0<(polynomialWindow j:ℝ) := Nat.cast_pos.mpr (polynomialWindow_pos j)
  unfold roundingWidth; positivity
lemma roundingWidth_lt_one (j : ℕ) : roundingWidth j<1 := by
  have hm : (1:ℝ)≤blockLength j := by exact_mod_cast (scaleStep j).mpos
  have hK : (1:ℝ)≤polynomialWindow j := by exact_mod_cast polynomialWindow_pos j
  rw [roundingWidth,div_lt_one (by positivity)]
  nlinarith
lemma phase_width_bounds (j : ℕ) (i : Fin (blockLength j)) :
    roundingWidth j≤coordinatePhase (blocks.equiv ⟨j,i⟩) ∧ coordinatePhase (blocks.equiv ⟨j,i⟩)≤1-roundingWidth j := by
  have hm : (200:ℝ)≤blockLength j := by exact_mod_cast blockLength_ge j
  have hK : (1:ℝ)≤polynomialWindow j := by exact_mod_cast polynomialWindow_pos j
  have hd : 0<(blockLength j:ℝ)*polynomialWindow j := by positivity
  have hp := coordinatePhase_block j i
  have he : roundingWidth j=(1/10:ℝ)/((blockLength j:ℝ)*polynomialWindow j) := by unfold roundingWidth; ring
  rw [he]
  constructor
  · exact (div_le_div_of_nonneg_right (by norm_num) hd.le).trans hp.1.le
  · have hh : 2/((blockLength j:ℝ)*polynomialWindow j)+(1/10:ℝ)/((blockLength j:ℝ)*polynomialWindow j)≤1 := by
      rw [←add_div,div_le_one hd]; nlinarith
    linarith [hp.2]

def smoothDrop (j : ℕ) (i : Fin (blockLength j)) (x : CircleModel.CircleX) : ℝ :=
  roundedDrop (roundingWidth j) (coordinatePhase (blocks.equiv ⟨j,i⟩)) (dropSize j)
    (modelFrequency (blocks.equiv ⟨j,i⟩) • x)
def smoothCorrection (j : ℕ) (i : Fin (blockLength j)) (x : CircleModel.CircleX) : ℝ :=
  correction (roundingWidth j) (dropSize j) (modelFrequency (blocks.equiv ⟨j,i⟩) • x)
def integerDrop (j : ℕ) (i : Fin (blockLength j)) (x : CircleModel.CircleX) : ℝ :=
  dropSize j * (floorTerm modelFrequency modelAngle 1 x (blocks.equiv ⟨j,i⟩):ℝ)
def concentratedDrop (j : ℕ) (i : Fin (blockLength j)) := movedDrop modelAngle j (smoothDrop j i)
def totalCorrection (j : ℕ) (i : Fin (blockLength j)) (x : CircleModel.CircleX) : ℝ :=
  smoothCorrection j i x+moveCorrection modelAngle j (smoothDrop j i) x

def blockH (j : ℕ) (x : CircleModel.CircleX) : ℝ := ∑ i,concentratedDrop j i x
def blockG (j : ℕ) (x : CircleModel.CircleX) : ℝ := ∑ i,integerDrop j i x
def blockW (j : ℕ) (x : CircleModel.CircleX) : ℝ := ∑ i,totalCorrection j i x

lemma smoothDrop_continuous (j : ℕ) (i : Fin (blockLength j)) : Continuous (smoothDrop j i) :=
  (roundedDrop_continuous (roundingWidth_pos j) (roundingWidth_lt_one j) _ _).comp (continuous_id.nsmul _)
lemma smoothDrop_nonneg (j : ℕ) (i : Fin (blockLength j)) (x : CircleModel.CircleX) : 0 ≤ smoothDrop j i x :=
  roundedDrop_nonneg (roundingWidth_pos j) (roundingWidth_lt_one j) (coordinatePhase_pos _).le
    (Int.fract_lt_one _) (dropSize_nonneg j) _
lemma smoothCorrection_measurable (j : ℕ) (i : Fin (blockLength j)) : Measurable (smoothCorrection j i) :=
  (correction_measurable _ _).comp (continuous_id.nsmul _).measurable
lemma concentratedDrop_continuous (j : ℕ) (i : Fin (blockLength j)) : Continuous (concentratedDrop j i) :=
  movedDrop_continuous _ _ (smoothDrop_continuous j i)
lemma concentratedDrop_nonneg (j : ℕ) (i : Fin (blockLength j)) (x : CircleModel.CircleX) : 0 ≤ concentratedDrop j i x :=
  movedDrop_nonneg _ _ (smoothDrop_nonneg j i) x
lemma totalCorrection_measurable (j : ℕ) (i : Fin (blockLength j)) : Measurable (totalCorrection j i) :=
  (smoothCorrection_measurable j i).add (moveCorrection_continuous _ _ (smoothDrop_continuous j i)).measurable
lemma blockH_continuous (j : ℕ) : Continuous (blockH j) := continuous_finsetSum _ (fun i _ => concentratedDrop_continuous j i)
lemma blockH_nonneg (j : ℕ) (x : CircleModel.CircleX) : 0 ≤ blockH j x := Finset.sum_nonneg (fun i _ => concentratedDrop_nonneg j i x)
lemma blockW_measurable (j : ℕ) : Measurable (blockW j) := Finset.measurable_sum _ (fun i _ => totalCorrection_measurable j i)
lemma blockH_support (j : ℕ) (x : CircleModel.CircleX) (hx : supportRadius modelAngle j≤dist x 0) : blockH j x=0 :=
  Finset.sum_eq_zero (fun _i _ => movedDrop_zero_off _ _ _ _ hx)
lemma blockH_locallyFinite : LocallyFiniteOff blockH 0 := by
  apply locallyFiniteOff_of_shrinking_supports blockH 0 (supportRadius modelAngle) _ blockH_support
  apply supportRadius_tendsto
  rw [←denseRange_zsmul_iff_nsmul]
  simpa only [div_one,modelAngle] using (AddCircle.denseRange_zsmul_coe_iff (p := (1:ℝ))).mpr (by simpa using parameterAngle_spec.2.2.1)

lemma smoothDrop_coboundary (j : ℕ) (i : Fin (blockLength j)) (x : CircleModel.CircleX) :
    smoothDrop j i x-integerDrop j i x=smoothCorrection j i (x+modelAngle)-smoothCorrection j i x := by
  have hp := phase_orbit (blocks.equiv ⟨j,i⟩) 1
  simp only [one_smul,Int.cast_one,one_mul] at hp
  unfold smoothDrop integerDrop smoothCorrection floorTerm
  rw [model_beta]
  simp only [Int.cast_one,one_mul]
  change roundedDrop _ _ _ _ - dropSize j * (⌊CircleRounding.repr _+_⌋:ℝ)=_
  rw [roundedDrop_coboundary,nsmul_add,hp]
lemma totalCorrection_coboundary (j : ℕ) (i : Fin (blockLength j)) (x : CircleModel.CircleX) :
    concentratedDrop j i x-integerDrop j i x=totalCorrection j i (x+modelAngle)-totalCorrection j i x := by
  have h1 := smoothDrop_coboundary j i x
  have h2 := moveCorrection_coboundary modelAngle j (smoothDrop j i) x
  unfold totalCorrection concentratedDrop
  linarith
lemma block_coboundary (j : ℕ) (x : CircleModel.CircleX) :
    blockH j x-blockG j x=blockW j (x+modelAngle)-blockW j x := by
  unfold blockH blockG blockW
  simp only [←Finset.sum_sub_distrib,totalCorrection_coboundary]

lemma smoothDrop_zero (j : ℕ) (i : Fin (blockLength j)) : smoothDrop j i 0=dropSize j/2 := by
  unfold smoothDrop
  rw [smul_zero]
  exact roundedDrop_zero (roundingWidth_pos j) (roundingWidth_lt_one j) (phase_width_bounds j i).1 (phase_width_bounds j i).2 _
lemma blockH_zero_lower (j : ℕ) : (blockLength j:ℝ)*dropSize j/(2*((j:ℝ)+1))≤blockH j 0 := by
  calc
    _ = ∑ _i : Fin (blockLength j),(dropSize j/2)/((j:ℝ)+1) := by simp; field_simp
    _ ≤ _ := Finset.sum_le_sum (fun i _ => by
      change _ ≤ movedDrop modelAngle j (smoothDrop j i) 0
      rw [←smoothDrop_zero j i]
      exact movedDrop_zero_lower modelAngle j (smoothDrop_nonneg j i))

lemma smoothDrop_integral (j : ℕ) (i : Fin (blockLength j)) :
    (∫ x : CircleModel.CircleX,smoothDrop j i x)=dropSize j*coordinatePhase (blocks.equiv ⟨j,i⟩) := by
  have hm := measurePreserving_XiMap (q:=modelFrequency) (fun i => (frequency_pos (i+1)).ne') (blocks.equiv ⟨j,i⟩)
  let f := roundedDrop (roundingWidth j) (coordinatePhase (blocks.equiv ⟨j,i⟩)) (dropSize j)
  have hf : AEStronglyMeasurable f volume := (roundedDrop_continuous (roundingWidth_pos j) (roundingWidth_lt_one j) _ _).aestronglyMeasurable
  calc
    _ = ∫ x : CircleModel.CircleX,f x ∂Measure.map (fun x => modelFrequency (blocks.equiv ⟨j,i⟩) • x) volume := by
      rw [integral_map hm.aemeasurable (by rwa [hm.map_eq])]; rfl
    _ = ∫ x : CircleModel.CircleX,f x := by rw [hm.map_eq]
    _ = _ := roundedDrop_integral (roundingWidth_pos j) (roundingWidth_lt_one j) _ _
lemma blockH_integral_lower (j : ℕ) : (polynomialWindow j:ℝ)≤∫ x : CircleModel.CircleX,blockH j x := by
  have he : (∫ x : CircleModel.CircleX,blockH j x)=∑ i : Fin (blockLength j),dropSize j*coordinatePhase (blocks.equiv ⟨j,i⟩) := by
    unfold blockH
    rw [integral_finsetSum _ (fun i _ => (concentratedDrop_continuous j i).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
    apply Finset.sum_congr rfl
    intro i _
    exact (movedDrop_integral modelAngle j (smoothDrop_continuous j i)).trans (smoothDrop_integral j i)
  rw [he]
  simpa only [coordinateDrop,block_number_equiv] using phase_drop_block_lower j
end
open CircleModel CircleRounding CircleConcentration ContinuousCircleWeight
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal

lemma measure_nonzero_sum {ι : Type uι} [Fintype ι] (f : ι → CircleModel.CircleX → ℝ) :
    volume {x | (∑ i,f i x)≠0} ≤ ∑ i,volume {x | f i x≠0} := by
  classical
  apply (measure_mono (show {x | (∑ i,f i x)≠0} ⊆ ⋃ i,{x | f i x≠0} from ?_)).trans (measure_iUnion_fintype_le _ _)
  intro x hx
  by_contra! hh
  simp only [mem_iUnion,mem_ofPred_eq,not_exists,not_not] at hh
  exact hx (Finset.sum_eq_zero (fun i _ => hh i))
lemma measure_nonzero_add (f g : CircleModel.CircleX → ℝ) :
    volume {x | f x+g x≠0}≤volume {x | f x≠0}+volume {x | g x≠0} := by
  apply (measure_mono (show {x | f x+g x≠0}⊆{x | f x≠0}∪{x | g x≠0} from ?_)).trans (measure_union_le _ _)
  intro x hx
  by_contra! hh
  simp only [mem_union,mem_ofPred_eq,not_or,not_not] at hh
  exact hx (by rw [hh.1,hh.2,add_zero])
lemma smoothCorrection_measure (j : ℕ) (i : Fin (blockLength j)) :
    volume {x | smoothCorrection j i x≠0}≤ENNReal.ofReal (2*roundingWidth j) := by
  have hm := measurePreserving_XiMap (q:=modelFrequency) (fun i => (frequency_pos (i+1)).ne') (blocks.equiv ⟨j,i⟩)
  change volume ((fun x : CircleModel.CircleX => modelFrequency (blocks.equiv ⟨j,i⟩) • x) ⁻¹' {x | correction (roundingWidth j) (dropSize j) x≠0}) ≤ _
  have he := hm.measure_preimage ((correction_measurable (roundingWidth j) (dropSize j)) (measurableSet_singleton 0).compl).nullMeasurableSet
  change volume ((fun x : CircleModel.CircleX => modelFrequency (blocks.equiv ⟨j,i⟩) • x) ⁻¹' {x | correction (roundingWidth j) (dropSize j) x≠0}) = _ at he
  exact he.le.trans (correction_measure (roundingWidth_pos j))
lemma smoothDrop_measure (j : ℕ) (i : Fin (blockLength j)) :
    volume {x | smoothDrop j i x≠0}≤ENNReal.ofReal (coordinatePhase (blocks.equiv ⟨j,i⟩)+2*roundingWidth j) := by
  have hm := measurePreserving_XiMap (q:=modelFrequency) (fun i => (frequency_pos (i+1)).ne') (blocks.equiv ⟨j,i⟩)
  change volume ((fun x : CircleModel.CircleX => modelFrequency (blocks.equiv ⟨j,i⟩) • x) ⁻¹' {x | roundedDrop (roundingWidth j) (coordinatePhase (blocks.equiv ⟨j,i⟩)) (dropSize j) x≠0}) ≤ _
  have he := hm.measure_preimage (((roundedDrop_continuous (roundingWidth_pos j) (roundingWidth_lt_one j) (coordinatePhase (blocks.equiv ⟨j,i⟩)) (dropSize j)).measurable) (measurableSet_singleton 0).compl).nullMeasurableSet
  change volume ((fun x : CircleModel.CircleX => modelFrequency (blocks.equiv ⟨j,i⟩) • x) ⁻¹' {x | roundedDrop (roundingWidth j) (coordinatePhase (blocks.equiv ⟨j,i⟩)) (dropSize j) x≠0}) = _ at he
  exact he.le.trans (roundedDrop_measure (roundingWidth_pos j) (coordinatePhase_pos _).le)
lemma integerDrop_measure (j : ℕ) (i : Fin (blockLength j)) :
    volume {x | integerDrop j i x≠0}≤ENNReal.ofReal (2*coordinatePhase (blocks.equiv ⟨j,i⟩)) := by
  have hs : {x | integerDrop j i x≠0}⊆{x | floorTerm modelFrequency modelAngle 1 x (blocks.equiv ⟨j,i⟩)≠0} := by
    intro x hx hh
    exact hx (by simp [integerDrop,hh])
  apply (measure_mono hs).trans
  simpa only [model_beta,Int.cast_one,abs_one,mul_one] using floorTerm_event_bound (q:=modelFrequency) (fun i => (frequency_pos (i+1)).ne') modelAngle 1 (blocks.equiv ⟨j,i⟩)
lemma totalCorrection_measure (j : ℕ) (i : Fin (blockLength j)) :
    volume {x | totalCorrection j i x≠0}≤ENNReal.ofReal (2*roundingWidth j+(j:ℝ)*(coordinatePhase (blocks.equiv ⟨j,i⟩)+2*roundingWidth j)) := by
  have hδ := (roundingWidth_pos j).le
  have hβ := (coordinatePhase_pos (blocks.equiv ⟨j,i⟩)).le
  calc
    _ ≤ volume {x | smoothCorrection j i x≠0}+volume {x | moveCorrection modelAngle j (smoothDrop j i) x≠0} := measure_nonzero_add _ _
    _ ≤ ENNReal.ofReal (2*roundingWidth j)+(j:ℝ≥0∞)*ENNReal.ofReal (coordinatePhase (blocks.equiv ⟨j,i⟩)+2*roundingWidth j) :=
      add_le_add (smoothCorrection_measure j i) ((moveCorrection_measure modelAngle j (smoothDrop_continuous j i).measurable).trans (mul_le_mul_right (smoothDrop_measure j i) _))
    _ = _ := by
      rw [←ENNReal.ofReal_natCast,←ENNReal.ofReal_mul (Nat.cast_nonneg j),←ENNReal.ofReal_add (by positivity : 0≤2*roundingWidth j) (by positivity)]

lemma blockG_measure (j : ℕ) : volume {x | blockG j x≠0}≤ENNReal.ofReal (4/(polynomialWindow j:ℝ)) := by
  calc
    _ ≤ ∑ i : Fin (blockLength j),volume {x | integerDrop j i x≠0} := measure_nonzero_sum _
    _ ≤ ∑ i : Fin (blockLength j),ENNReal.ofReal (2*coordinatePhase (blocks.equiv ⟨j,i⟩)) := Finset.sum_le_sum (fun i _ => integerDrop_measure j i)
    _ = ENNReal.ofReal (2*∑ i : Fin (blockLength j),coordinatePhase (blocks.equiv ⟨j,i⟩)) := by
      rw [Finset.mul_sum,ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (by norm_num) (coordinatePhase_pos _).le)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      calc
        _ ≤ 2*(2/(polynomialWindow j:ℝ)) := mul_le_mul_of_nonneg_left (sum_phase_block j) (by norm_num)
        _ = _ := by ring)
lemma blockW_measure (j : ℕ) : volume {x | blockW j x≠0}≤ENNReal.ofReal ((1+3*(j:ℝ))/(polynomialWindow j:ℝ)) := by
  have hm : 0<(blockLength j:ℝ) := Nat.cast_pos.mpr (scaleStep j).mpos
  have hK : 0<(polynomialWindow j:ℝ) := Nat.cast_pos.mpr (polynomialWindow_pos j)
  have hs := sum_phase_block j
  calc
    _ ≤ ∑ i : Fin (blockLength j),volume {x | totalCorrection j i x≠0} := measure_nonzero_sum _
    _ ≤ ∑ i : Fin (blockLength j),ENNReal.ofReal (2*roundingWidth j+(j:ℝ)*(coordinatePhase (blocks.equiv ⟨j,i⟩)+2*roundingWidth j)) := Finset.sum_le_sum (fun i _ => totalCorrection_measure j i)
    _ = ENNReal.ofReal (∑ i : Fin (blockLength j),(2*roundingWidth j+(j:ℝ)*(coordinatePhase (blocks.equiv ⟨j,i⟩)+2*roundingWidth j))) :=
      (ENNReal.ofReal_sum_of_nonneg (fun i _ => by have := (coordinatePhase_pos (blocks.equiv ⟨j,i⟩)).le; have := (roundingWidth_pos j).le; positivity)).symm
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      simp only [mul_add,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,←Finset.mul_sum]
      have hn : (0:ℝ)≤j := Nat.cast_nonneg j
      have hh := mul_le_mul_of_nonneg_left hs hn
      have he : (blockLength j:ℝ)*(2*roundingWidth j)=1/(5*(polynomialWindow j:ℝ)) := by unfold roundingWidth; field_simp; ring
      rw [show (blockLength j:ℝ)*((j:ℝ)*(2*roundingWidth j))=(j:ℝ)*((blockLength j:ℝ)*(2*roundingWidth j)) by ring,he]
      calc
        _ ≤ 1/(5*(polynomialWindow j:ℝ))+(j:ℝ)*(2/(polynomialWindow j:ℝ))+(j:ℝ)*(1/(5*(polynomialWindow j:ℝ))) := by linarith
        _ = (1+11*(j:ℝ))/(5*(polynomialWindow j:ℝ)) := by ring
        _ ≤ _ := (div_le_div_iff₀ (by positivity : 0<5*(polynomialWindow j:ℝ)) hK).mpr (by nlinarith)

lemma summable_blockW_bound : Summable (fun j : ℕ => (1+3*(j:ℝ))/(polynomialWindow j:ℝ)) := by
  have hgeom : Summable (fun j : ℕ => (j:ℝ)*(1/2:ℝ)^j) := by
    simpa only [pow_one] using summable_pow_mul_geometric_of_norm_lt_one 1 (by norm_num : ‖(1/2:ℝ)‖<1)
  have hs : Summable (fun j : ℕ => (1+3*(j:ℝ))*((1/(polynomialWindow 0:ℝ))*(1/2:ℝ)^j)) := by
    have h1 := (summable_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖<1)).mul_left (1/(polynomialWindow 0:ℝ))
    have h2 := hgeom.mul_left (3/(polynomialWindow 0:ℝ))
    apply (h1.add h2).congr
    intro j
    ring
  apply Summable.of_nonneg_of_le (fun j => by positivity) _ hs
  intro j
  have hh := mul_le_mul_of_nonneg_left (window_inverse_bound 0 j) (show 0≤1+3*(j:ℝ) by positivity)
  simpa only [Nat.zero_add,mul_one_div] using hh
lemma blockG_support_sum : (∑' j,volume {x | blockG j x≠0})≠∞ := by
  apply ne_of_lt ((ENNReal.tsum_le_tsum blockG_measure).trans_lt _)
  have hs : Summable (fun j : ℕ => 4/(polynomialWindow j:ℝ)) := by
    simpa only [Nat.zero_add,mul_one_div] using (summable_window_inverse 0).mul_left 4
  rw [←ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hs]
  exact ENNReal.ofReal_lt_top
lemma blockW_support_sum : (∑' j,volume {x | blockW j x≠0})≠∞ := by
  apply ne_of_lt ((ENNReal.tsum_le_tsum blockW_measure).trans_lt _)
  rw [←ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) summable_blockW_bound]
  exact ENNReal.ofReal_lt_top


end CircleSampling

end

end OAI

import OAI.Analysis.RotationWeights.Convolution

namespace OAI

noncomputable section

namespace CircleRounding

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
open Set MeasureTheory
open scoped ENNReal
abbrev X := AddCircle (1:ℝ)
def repr (x : X) : ℝ := (AddCircle.measurableEquivIco 1 0 x).val
lemma repr_mem (x : X) : repr x∈Ico 0 1 := by
  simpa [repr] using (AddCircle.measurableEquivIco 1 0 x).property
lemma coe_repr (x : X) : (repr x:X)=x := by
  exact (AddCircle.measurableEquivIco 1 0).symm_apply_apply x
lemma repr_measurable : Measurable repr := measurable_subtype_coe.comp (AddCircle.measurableEquivIco 1 0).measurable
lemma repr_mk (t : ℝ) : repr (t:X)=Int.fract t := by
  change (AddCircle.equivIco 1 0 (t:X)).val=_
  simpa only [div_one,mul_one] using AddCircle.coe_equivIco_mk_apply (p:=(1:ℝ)) t
lemma repr_zero : repr 0=0 := by simpa using repr_mk 0

def intervalRamp (δ s : ℝ) : ℝ := min 0 ((s-δ)/(2*δ))+max 0 ((s-(1-δ))/(2*δ))
lemma intervalRamp_continuous (δ : ℝ) : Continuous (intervalRamp δ) := by
  unfold intervalRamp
  fun_prop
lemma intervalRamp_monotone {δ : ℝ} (hδ : 0<δ) : Monotone (intervalRamp δ) := by
  intro s t hst
  apply add_le_add
  · exact min_le_min le_rfl (div_le_div_of_nonneg_right (sub_le_sub_right hst δ) (by positivity))
  · exact max_le_max le_rfl (div_le_div_of_nonneg_right (sub_le_sub_right hst (1-δ)) (by positivity))
lemma intervalRamp_zero {δ : ℝ} (hδ : 0<δ) (hδ1 : δ<1) : intervalRamp δ 0=-(1/2:ℝ) := by
  unfold intervalRamp
  rw [min_eq_right (by apply div_nonpos_of_nonpos_of_nonneg <;> linarith),max_eq_left (by apply div_nonpos_of_nonpos_of_nonneg <;> linarith)]
  field_simp
  ring
lemma intervalRamp_one {δ : ℝ} (hδ : 0<δ) (hδ1 : δ<1) : intervalRamp δ 1=(1/2:ℝ) := by
  unfold intervalRamp
  rw [min_eq_left (by apply div_nonneg <;> linarith),max_eq_right (by apply div_nonneg <;> linarith)]
  field_simp
  ring
lemma intervalRamp_bounds {δ s : ℝ} (hδ : 0<δ) (hδ1 : δ<1) (hs : s∈Icc 0 1) :
    -(1/2:ℝ) ≤ intervalRamp δ s ∧ intervalRamp δ s ≤ 1/2 := by
  rw [←intervalRamp_zero hδ hδ1,←intervalRamp_one hδ hδ1]
  exact ⟨intervalRamp_monotone hδ hs.1,intervalRamp_monotone hδ hs.2⟩
lemma intervalRamp_middle {δ s : ℝ} (hδ : 0<δ) (hs : δ ≤ s ∧ s ≤ 1-δ) : intervalRamp δ s=0 := by
  unfold intervalRamp
  rw [min_eq_left (div_nonneg (sub_nonneg.mpr hs.1) (by positivity)),max_eq_left (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hs.2) (by positivity))]
  ring

def periodicCorrector (δ : ℝ) : X → ℝ := AddCircle.liftIco 1 0 (fun s => intervalRamp δ s-s)
lemma periodicCorrector_continuous {δ : ℝ} (hδ : 0<δ) (hδ1 : δ<1) : Continuous (periodicCorrector δ) := by
  apply AddCircle.liftIco_zero_continuous
  · simp only [intervalRamp_zero hδ hδ1,intervalRamp_one hδ hδ1]; ring
  · exact ((intervalRamp_continuous δ).sub continuous_id).continuousOn
lemma periodicCorrector_repr (δ : ℝ) (x : X) : periodicCorrector δ x=intervalRamp δ (repr x)-repr x := by
  conv_lhs => rw [←coe_repr x]
  exact AddCircle.liftIco_zero_coe_apply (repr_mem x)

def roundedFloor (δ t : ℝ) : ℝ := t+periodicCorrector δ (t:X)
lemma roundedFloor_continuous {δ : ℝ} (hδ : 0<δ) (hδ1 : δ<1) : Continuous (roundedFloor δ) :=
  continuous_id.add ((periodicCorrector_continuous hδ hδ1).comp (AddCircle.continuous_mk' 1))
lemma roundedFloor_add_one (δ t : ℝ) : roundedFloor δ (t+1)=roundedFloor δ t+1 := by
  simp only [roundedFloor,AddCircle.coe_add,AddCircle.coe_period,add_zero]
  ring

def roundedDrop (δ β c : ℝ) (x : X) : ℝ := c*(β+periodicCorrector δ (x+(β:X))-periodicCorrector δ x)
def correction (δ c : ℝ) (x : X) : ℝ := c*intervalRamp δ (repr x)
lemma roundedDrop_continuous {δ : ℝ} (hδ : 0<δ) (hδ1 : δ<1) (β c : ℝ) : Continuous (roundedDrop δ β c) := by
  unfold roundedDrop
  exact continuous_const.mul ((continuous_const.add ((periodicCorrector_continuous hδ hδ1).comp (continuous_id.add continuous_const))).sub (periodicCorrector_continuous hδ hδ1))
lemma correction_measurable (δ c : ℝ) : Measurable (correction δ c) :=
  measurable_const.mul ((intervalRamp_continuous δ).measurable.comp repr_measurable)
lemma repr_add (x : X) (β : ℝ) : repr (x+(β:X))=Int.fract (repr x+β) := by
  calc
    _ = repr ((repr x+β:ℝ):X) := by rw [AddCircle.coe_add,coe_repr]
    _ = _ := repr_mk _

lemma roundedDrop_formula (δ β c : ℝ) (x : X) :
    roundedDrop δ β c x=c*((Int.floor (repr x+β):ℤ)+intervalRamp δ (repr (x+(β:X)))-intervalRamp δ (repr x)) := by
  rw [roundedDrop,periodicCorrector_repr,periodicCorrector_repr]
  have hh := repr_add x β
  rw [Int.fract] at hh
  congr 1
  linarith
lemma roundedDrop_coboundary (δ β c : ℝ) (x : X) :
    roundedDrop δ β c x-c*(Int.floor (repr x+β):ℤ)=correction δ c (x+(β:X))-correction δ c x := by
  rw [roundedDrop_formula,correction,correction]
  ring
lemma roundedDrop_nonneg {δ β c : ℝ} (hδ : 0<δ) (hδ1 : δ<1) (hβ : 0 ≤ β) (hβ1 : β<1) (hc : 0 ≤ c) (x : X) :
    0 ≤ roundedDrop δ β c x := by
  rw [roundedDrop_formula]
  apply mul_nonneg hc
  have hx := repr_mem x
  have hy := repr_mem (x+(β:X))
  have hf0 : 0 ≤ Int.floor (repr x+β) := Int.floor_nonneg.mpr (by linarith [hx.1])
  have hf1 : Int.floor (repr x+β) ≤ 1 := by
    rw [Int.floor_le_iff]; norm_num; linarith [hx.2]
  have hb := intervalRamp_bounds hδ hδ1 ⟨hx.1,hx.2.le⟩
  have hb' := intervalRamp_bounds hδ hδ1 ⟨hy.1,hy.2.le⟩
  rcases (show Int.floor (repr x+β)=0 ∨ Int.floor (repr x+β)=1 by omega) with he | he
  · have hxy : repr x ≤ repr (x+(β:X)) := by rw [repr_add,Int.fract,he]; norm_num; linarith
    have hh := intervalRamp_monotone hδ hxy
    rw [he]; norm_num; linarith
  · rw [he]; norm_num; linarith
end

open Set MeasureTheory
open scoped ENNReal
lemma roundedDrop_zero {δ β : ℝ} (hδ : 0<δ) (hδ1 : δ<1) (hβ : δ ≤ β) (hβ1 : β ≤ 1-δ) (c : ℝ) :
    roundedDrop δ β c 0=c/2 := by
  have hb0 : 0 ≤ β := hδ.le.trans hβ
  have hb1 : β<1 := by linarith
  rw [roundedDrop_formula,repr_zero,zero_add,Int.floor_eq_zero_iff.mpr ⟨hb0,hb1⟩]
  simp only [Int.cast_zero,zero_add]
  rw [repr_mk,Int.fract_eq_self.mpr ⟨hb0,hb1⟩,intervalRamp_middle hδ ⟨hβ,hβ1⟩,intervalRamp_zero hδ hδ1]
  ring
lemma correction_support {δ c : ℝ} (hδ : 0<δ) :
    {x : X | correction δ c x≠0} ⊆ {x | repr x<δ} ∪ {x | 1-δ ≤ repr x} := by
  intro x hx
  by_contra! hh
  have hh' : δ ≤ repr x ∧ repr x<1-δ := by simpa only [Set.mem_union,Set.mem_ofPred_eq,not_or,not_lt,not_le] using hh
  apply hx
  rw [correction,intervalRamp_middle hδ ⟨hh'.1,hh'.2.le⟩,mul_zero]
lemma roundedDrop_support {δ β c : ℝ} (hδ : 0<δ) (hβ : 0 ≤ β) :
    {x : X | roundedDrop δ β c x≠0} ⊆ {x | repr x<δ} ∪ {x | 1-(β+δ) ≤ repr x} := by
  intro x hx
  by_contra! hh
  have hh' : δ ≤ repr x ∧ repr x<1-(β+δ) := by simpa only [Set.mem_union,Set.mem_ofPred_eq,not_or,not_lt,not_le] using hh
  have ht : repr x+β∈Ico 0 1 := ⟨by linarith [hh'.1],by linarith [hh'.2]⟩
  apply hx
  rw [roundedDrop_formula,Int.floor_eq_zero_iff.mpr ht,repr_add,Int.fract_eq_self.mpr ht,
    intervalRamp_middle hδ ⟨by linarith [hh'.1],by linarith [hh'.2]⟩,
    intervalRamp_middle hδ ⟨hh'.1,by linarith [hh'.2]⟩]
  simp
lemma measure_repr_lower {r : ℝ} : volume {x : X | repr x < r} ≤ ENNReal.ofReal r := by
  change volume (repr ⁻¹' Iio r) ≤ _
  rw [AddCircle.add_projection_respects_measure 1 0 (repr_measurable measurableSet_Iio)]
  have hs : ((↑) : ℝ → X) ⁻¹' {x | repr x < r} ∩ Ioc 0 (0+1) ⊆ Ioo 0 r ∪ {1} := by
    rintro s ⟨hs,hsI⟩
    by_cases he : s=1
    · exact Or.inr (by simpa using he)
    · left
      refine ⟨hsI.1,?_⟩
      change repr (s : X)<r at hs
      rw [repr_mk,Int.fract_eq_self.mpr ⟨hsI.1.le,lt_of_le_of_ne (by simpa using hsI.2) he⟩] at hs
      exact hs
  calc
    _ ≤ volume (Ioo 0 r ∪ {1}) := measure_mono hs
    _ ≤ volume (Ioo 0 r) + volume ({1}:Set ℝ) := measure_union_le _ _
    _ = ENNReal.ofReal r := by simp

lemma measure_repr_upper {r : ℝ} : volume {x : X | 1-r≤repr x} ≤ ENNReal.ofReal r := by
  change volume (repr ⁻¹' Ici (1-r)) ≤ _
  rw [AddCircle.add_projection_respects_measure 1 0 (repr_measurable measurableSet_Ici)]
  have hs : ((↑) : ℝ → X) ⁻¹' {x | 1-r≤repr x} ∩ Ioc 0 (0+1) ⊆ Icc (1-r) 1 ∪ {1} := by
    rintro s ⟨hs,hsI⟩
    by_cases he : s=1
    · exact Or.inr (by simpa using he)
    · left
      refine ⟨?_,by simpa using hsI.2⟩
      change 1-r≤repr (s : X) at hs
      rw [repr_mk,Int.fract_eq_self.mpr ⟨hsI.1.le,lt_of_le_of_ne (by simpa using hsI.2) he⟩] at hs
      exact hs
  calc
    _ ≤ volume (Icc (1-r) 1 ∪ {1}) := measure_mono hs
    _ ≤ volume (Icc (1-r) 1)+volume ({1}:Set ℝ) := measure_union_le _ _
    _ = ENNReal.ofReal r := by simp

lemma correction_measure {δ c : ℝ} (hδ : 0<δ) : volume {x : X | correction δ c x≠0} ≤ ENNReal.ofReal (2*δ) := by
  apply (measure_mono (correction_support hδ)).trans
  apply (measure_union_le _ _).trans
  calc
    _ ≤ ENNReal.ofReal δ+ENNReal.ofReal δ := add_le_add measure_repr_lower measure_repr_upper
    _ = _ := by rw [←ENNReal.ofReal_add hδ.le hδ.le]; congr 1; ring
lemma roundedDrop_measure {δ β c : ℝ} (hδ : 0<δ) (hβ : 0 ≤ β) : volume {x : X | roundedDrop δ β c x≠0} ≤ ENNReal.ofReal (β+2*δ) := by
  apply (measure_mono (roundedDrop_support hδ hβ)).trans
  apply (measure_union_le _ _).trans
  calc
    _ ≤ ENNReal.ofReal δ+ENNReal.ofReal (β+δ) := add_le_add measure_repr_lower measure_repr_upper
    _ = _ := by rw [←ENNReal.ofReal_add hδ.le (add_nonneg hβ hδ.le)]; congr 1; ring
lemma roundedDrop_integral {δ : ℝ} (hδ : 0<δ) (hδ1 : δ<1) (β c : ℝ) :
    (∫ x : X,roundedDrop δ β c x)=c*β := by
  have hq : Integrable (periodicCorrector δ) (volume : Measure X) := (periodicCorrector_continuous hδ hδ1).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hσ : MeasurePreserving (fun x : X => x+(β:X)) volume volume := measurePreserving_add_right volume _
  have hq' : Integrable (fun x : X => periodicCorrector δ (x+(β:X))) volume := hσ.integrable_comp_of_integrable hq
  have hi : (∫ x : X,periodicCorrector δ (x+(β:X)))=∫ x : X,periodicCorrector δ x := hσ.integral_comp (Homeomorph.addRight (β:X)).isClosedEmbedding.measurableEmbedding _
  simp only [roundedDrop,integral_const_mul]
  have hs : Integrable (fun x : X => β+periodicCorrector δ (x+(β:X))) volume := (integrable_const β).add hq'
  rw [integral_sub hs hq,integral_add (integrable_const β) hq',hi]
  simp [AddCircle.volume_eq_smul_haarAddCircle]


end CircleRounding

end

end OAI

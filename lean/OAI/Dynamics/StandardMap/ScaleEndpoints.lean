import OAI.Dynamics.StandardMap.ScaleAction

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory Topology
open scoped Classical
namespace StandardMapEntropy
noncomputable def coreLength (d:DistanceArray) : ℝ := endpointRight d-endpointLeft d
lemma measurable_coreLength : Measurable coreLength := measurable_endpointRight.sub measurable_endpointLeft
lemma coreLength_translate (r:DyadicTime) (d:DistanceArray) (hd:d∈twoRayClass) : coreLength (arrayTranslate r d)=coreLength d := by
  unfold coreLength
  rw [endpointRight_translate r d hd.2.2.2 hd.2.2.1,endpointLeft_translate r d hd.2.1 hd.1]
  ring
lemma coreLength_dilate (d:DistanceArray) (hd:d∈twoRayClass) : coreLength (arrayDilate d)=coreLength d/2 := by
  unfold coreLength
  rw [endpointRight_dilate d hd.2.2.2 hd.2.2.1,endpointLeft_dilate d hd.2.1 hd.1]
  ring
lemma twoRayClass_half (d:NonAffineArray) (hu:UnitArray d.val) : (nonaffineHalf d).val∈twoRayClass ↔ d.val∈twoRayClass := by
  have he := twoRayClass_dilate (nonaffineHalf d).val
  change (nonaffineDilate (nonaffineHalf d)).val∈twoRayClass ↔ _ at he
  rw [nonaffineDilate_half d hu] at he
  exact he.symm
lemma coreLength_half (d:NonAffineArray) (hu:UnitArray d.val) (hd:d.val∈twoRayClass) : coreLength (nonaffineHalf d).val=2*coreLength d.val := by
  have he := coreLength_dilate (nonaffineHalf d).val ((twoRayClass_half d hu).mpr hd)
  change coreLength (nonaffineDilate (nonaffineHalf d)).val=_ at he
  rw [nonaffineDilate_half d hu] at he
  linarith
lemma scaleZ_twoRay (j:ℤ) (d:NonAffineArray) (hu:UnitArray d.val) : (scaleZ j d).val∈twoRayClass ↔ d.val∈twoRayClass := by
  induction j using Int.induction_on with
  | zero => rw [scaleZ_zero]
  | succ j ih =>
    rw [add_comm,scaleZ_add,scaleZ_one,nonaffineDouble,ite_eq_left ((scaleZ_unit j d).mpr hu)]
    exact (twoRayClass_dilate _).trans ih
  | pred j ih =>
    rw [sub_eq_add_neg,add_comm,scaleZ_add,scaleZ_neg_one]
    exact (twoRayClass_half _ ((scaleZ_unit (-(j:ℤ)) d).mpr hu)).trans ih
lemma scaleZ_length (j:ℤ) (d:NonAffineArray) (hu:UnitArray d.val) (hd:d.val∈twoRayClass) : coreLength (scaleZ j d).val=coreLength d.val/(2:ℝ)^j := by
  induction j using Int.induction_on with
  | zero => simp only [scaleZ_zero,zpow_zero,div_one]
  | succ j ih =>
    rw [add_comm,scaleZ_add,scaleZ_one,nonaffineDouble,ite_eq_left ((scaleZ_unit j d).mpr hu)]
    change coreLength (arrayDilate (scaleZ j d).val)=_
    rw [coreLength_dilate _ ((scaleZ_twoRay j d hu).mpr hd),ih,zpow_add₀ (by norm_num : (2:ℝ)≠0),zpow_one]
    ring
  | pred j ih =>
    rw [sub_eq_add_neg,add_comm,scaleZ_add,scaleZ_neg_one]
    rw [coreLength_half _ ((scaleZ_unit (-(j:ℤ)) d).mpr hu) ((scaleZ_twoRay (-(j:ℤ)) d hu).mpr hd),ih,zpow_add₀ (by norm_num : (2:ℝ)≠0),zpow_neg_one]
    ring
noncomputable def lengthBand (j:ℤ) : Set NonAffineArray := {d | UnitArray d.val ∧ d.val∈twoRayClass ∧ (2:ℝ)^j≤coreLength d.val ∧ coreLength d.val<(2:ℝ)^(j+1)}
lemma measurableSet_lengthBand (j:ℤ) : MeasurableSet (lengthBand j) :=
  (isClosed_unitArray.preimage continuous_subtype_val).measurableSet.inter
    ((measurableSet_twoRayClass.preimage measurable_subtype_coe).inter
      (((measurable_coreLength.comp measurable_subtype_coe) measurableSet_Ici).inter ((measurable_coreLength.comp measurable_subtype_coe) measurableSet_Iio)))
lemma lengthBand_scaleZ (i j:ℤ) : (scaleZ i)⁻¹'lengthBand j=lengthBand (i+j) := by
  ext d
  simp only [mem_preimage,lengthBand,mem_ofPred_eq]
  constructor
  · rintro ⟨hu,hd,hl,hr⟩
    have hud := (scaleZ_unit i d).mp hu
    have hdd := (scaleZ_twoRay i d hud).mp hd
    rw [scaleZ_length i d hud hdd] at hl hr
    refine ⟨hud,hdd,?_,?_⟩
    · have hh := (le_div_iff₀ (zpow_pos (by norm_num : (0:ℝ)<2) i)).mp hl
      rw [zpow_add₀ (by norm_num : (2:ℝ)≠0)]
      simpa only [mul_comm] using hh
    · have hh := (div_lt_iff₀ (zpow_pos (by norm_num : (0:ℝ)<2) i)).mp hr
      rw [show i+j+1=i+(j+1) by omega,zpow_add₀ (by norm_num : (2:ℝ)≠0)]
      simpa only [mul_comm] using hh
  · rintro ⟨hu,hd,hl,hr⟩
    refine ⟨(scaleZ_unit i d).mpr hu,(scaleZ_twoRay i d hu).mpr hd,?_,?_⟩
    · rw [scaleZ_length i d hu hd,le_div_iff₀ (zpow_pos (by norm_num : (0:ℝ)<2) i)]
      rw [zpow_add₀ (by norm_num : (2:ℝ)≠0),mul_comm] at hl
      exact hl
    · rw [scaleZ_length i d hu hd,div_lt_iff₀ (zpow_pos (by norm_num : (0:ℝ)<2) i)]
      rw [show i+j+1=i+(j+1) by omega,zpow_add₀ (by norm_num : (2:ℝ)≠0),mul_comm] at hr
      exact hr
lemma lengthBand_translate (j:ℤ) (r:DyadicTime) : (nonaffineTranslation r)⁻¹'lengthBand j=lengthBand j := by
  ext d
  change (UnitArray (arrayTranslate r d.val) ∧ arrayTranslate r d.val∈twoRayClass ∧ (2:ℝ)^j≤coreLength (arrayTranslate r d.val) ∧ coreLength (arrayTranslate r d.val)<(2:ℝ)^(j+1)) ↔ (UnitArray d.val ∧ d.val∈twoRayClass ∧ (2:ℝ)^j≤coreLength d.val ∧ coreLength d.val<(2:ℝ)^(j+1))
  have hu : UnitArray (arrayTranslate r d.val) ↔ UnitArray d.val := by
    constructor
    · intro h s t
      have hh := h (s-r) (t-r)
      change d.val.val (s-r+r) (t-r+r)≤|(t:ℝ)-(r:ℝ)-((s:ℝ)-(r:ℝ))| at hh
      simpa only [sub_add_cancel,sub_sub_sub_cancel_right] using hh
    · intro h s t
      have hh := h (s+r) (t+r)
      change d.val.val (s+r) (t+r)≤|(t:ℝ)+(r:ℝ)-((s:ℝ)+(r:ℝ))| at hh
      change d.val.val (s+r) (t+r)≤|(t:ℝ)-(s:ℝ)|
      simpa only [add_sub_add_right_eq_sub] using hh
  rw [hu,twoRayClass_translate]
  constructor <;> rintro ⟨hu,hd,hl,hr⟩
  · rw [coreLength_translate r d.val hd] at hl hr; exact ⟨hu,hd,hl,hr⟩
  · exact ⟨hu,hd,by simpa only [coreLength_translate r d.val hd] using hl,by simpa only [coreLength_translate r d.val hd] using hr⟩
end StandardMapEntropy

end OAI

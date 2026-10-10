import OAI.Dynamics.StandardMap.EndpointActions

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory Topology
open scoped Classical
namespace StandardMapEntropy
noncomputable def nonaffineDouble (d:NonAffineArray) : NonAffineArray :=
  if UnitArray d.val then nonaffineDilate d else d
lemma measurable_nonaffineDouble : Measurable nonaffineDouble :=
  continuous_nonaffineDilate.measurable.ite (isClosed_unitArray.preimage continuous_subtype_val).measurableSet measurable_id
lemma nonaffineDouble_unit (d:NonAffineArray) : UnitArray (nonaffineDouble d).val ↔ UnitArray d.val := by
  by_cases h:UnitArray d.val
  · simp only [nonaffineDouble,h,iff_true]; exact arrayDilate_unit d.val h
  · simp only [nonaffineDouble,ite_eq_right h]
lemma nonaffineHalf_unit_iff (d:NonAffineArray) : UnitArray (nonaffineHalf d).val ↔ UnitArray d.val := by
  by_cases h:UnitArray d.val
  · exact iff_of_true (nonaffineHalf_unit d h) h
  · simp only [nonaffineHalf,dite_eq_right h]
noncomputable def scaleEquiv : NonAffineArray ≃ᵐ NonAffineArray where
  toFun := nonaffineDouble
  invFun := nonaffineHalf
  left_inv d := by
    by_cases h:UnitArray d.val
    · simpa only [nonaffineDouble,ite_eq_left h] using nonaffineHalf_dilate d h
    · simp only [nonaffineDouble,ite_eq_right h,nonaffineHalf,dite_eq_right h]
  right_inv d := by
    by_cases h:UnitArray d.val
    · rw [nonaffineDouble,ite_eq_left (nonaffineHalf_unit d h),nonaffineDilate_half d h]
    · simp only [nonaffineHalf,dite_eq_right h,nonaffineDouble,ite_eq_right h]
  measurable_toFun := measurable_nonaffineDouble
  measurable_invFun := measurable_nonaffineHalf
noncomputable def scaleZ (j:ℤ) : Equiv.Perm NonAffineArray := scaleEquiv.toEquiv ^ j
lemma scaleZ_add (i j:ℤ) (d:NonAffineArray) : scaleZ (i+j) d=scaleZ i (scaleZ j d) := by
  change (scaleEquiv.toEquiv^(i+j)) d=(scaleEquiv.toEquiv^i) ((scaleEquiv.toEquiv^j) d)
  rw [zpow_add]; rfl
@[simp] lemma scaleZ_zero (d:NonAffineArray) : scaleZ 0 d=d := by simp only [scaleZ,zpow_zero]; rfl
lemma scaleZ_one (d:NonAffineArray) : scaleZ 1 d=nonaffineDouble d := by simp only [scaleZ,zpow_one]; rfl
lemma scaleZ_neg_one (d:NonAffineArray) : scaleZ (-1) d=nonaffineHalf d := by simp only [scaleZ,zpow_neg_one]; rfl
lemma scaleZ_unit (j:ℤ) (d:NonAffineArray) : UnitArray (scaleZ j d).val ↔ UnitArray d.val := by
  induction j using Int.induction_on with
  | zero => rw [scaleZ_zero]
  | succ j ih =>
    rw [add_comm,scaleZ_add,scaleZ_one,nonaffineDouble_unit,ih]
  | pred j ih =>
    rw [sub_eq_add_neg,add_comm,scaleZ_add,scaleZ_neg_one,nonaffineHalf_unit_iff,ih]
lemma measurable_scaleZ (j:ℤ) : Measurable (scaleZ j) := by
  induction j using Int.induction_on with
  | zero =>
    have he : (scaleZ 0:NonAffineArray→NonAffineArray)=id := funext scaleZ_zero
    rw [he]; exact measurable_id
  | succ j ih =>
    have he : (scaleZ ((j:ℤ)+1):NonAffineArray→NonAffineArray)=nonaffineDouble ∘ scaleZ j := funext (fun d => by rw [add_comm,scaleZ_add,scaleZ_one]; rfl)
    rw [he]; exact measurable_nonaffineDouble.comp ih
  | pred j ih =>
    have he : (scaleZ (-(j:ℤ)-1):NonAffineArray→NonAffineArray)=nonaffineHalf ∘ scaleZ (-(j:ℤ)) := funext (fun d => by rw [sub_eq_add_neg,add_comm,scaleZ_add,scaleZ_neg_one]; rfl)
    rw [he]; exact measurable_nonaffineHalf.comp ih
lemma map_scaleZ (μ:Measure NonAffineArray) (hu:∀ᵐd ∂μ,UnitArray d.val) (h:μ.map nonaffineDilate=μ) (j:ℤ) : μ.map (scaleZ j)=μ := by
  have hd : μ.map nonaffineDouble=μ := (Measure.map_congr (hu.mono (fun d hd => by simp only [nonaffineDouble,ite_eq_left hd]))).trans h
  have hb : μ.map nonaffineHalf=μ := by calc
    μ.map nonaffineHalf=(μ.map nonaffineDilate).map nonaffineHalf := by rw [h]
    _=μ := map_half_dilate μ hu
  induction j using Int.induction_on with
  | zero =>
    have he : (scaleZ 0:NonAffineArray→NonAffineArray)=id := funext scaleZ_zero
    rw [he,Measure.map_id]
  | succ j ih =>
    have he : (scaleZ (j+1):NonAffineArray→NonAffineArray)=nonaffineDouble ∘ scaleZ j := funext (fun d => by rw [add_comm,scaleZ_add,scaleZ_one]; rfl)
    rw [he,←Measure.map_map measurable_nonaffineDouble (measurable_scaleZ j),ih,hd]
  | pred j ih =>
    have he : (scaleZ (-(j:ℤ)-1):NonAffineArray→NonAffineArray)=nonaffineHalf ∘ scaleZ (-(j:ℤ)) := funext (fun d => by rw [sub_eq_add_neg,add_comm,scaleZ_add,scaleZ_neg_one]; rfl)
    rw [he,←Measure.map_map measurable_nonaffineHalf (measurable_scaleZ (-(j:ℤ))),ih,hb]
end StandardMapEntropy

end OAI

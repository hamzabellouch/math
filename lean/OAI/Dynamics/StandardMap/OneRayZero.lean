import OAI.Dynamics.StandardMap.BandComparison

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal Classical
namespace StandardMapEntropy
lemma invariant_interface_zero (μ:Measure NonAffineArray)
    (ht:∀r:DyadicTime,μ.map (nonaffineTranslation r)=μ) (hs:μ.map nonaffineDilate=μ)
    (A:Set NonAffineArray) (hA:MeasurableSet A) (e:NonAffineArray→ℝ) (he:Measurable e)
    (hAT:∀r:DyadicTime,(nonaffineTranslation r)⁻¹'A=A) (hAS:nonaffineDilate⁻¹'A=A)
    (hET:∀r:DyadicTime,∀d∈A,e (nonaffineTranslation r d)=e d-(r:ℝ))
    (hES:∀d∈A,e (nonaffineDilate d)=e d/2)
    (hf:μ (A∩e⁻¹'Ico 0 1)<∞) : μ A=0 := by
  let κ:=μ.restrict A
  let lam:=κ.map e
  have htκ (r:DyadicTime) : κ.map (nonaffineTranslation r)=κ :=
    map_restrict_invariant μ _ (nonaffineTranslation r).continuous.measurable (ht r) A hA (hAT r)
  have hsκ : κ.map nonaffineDilate=κ := map_restrict_invariant μ _ continuous_nonaffineDilate.measurable hs A hA hAS
  have htlam (r:DyadicTime) : lam.map (fun x:ℝ => x-(r:ℝ))=lam :=
    push_invariant κ _ (nonaffineTranslation r).continuous.measurable (htκ r) e he _ (measurable_id.sub measurable_const)
      ((ae_restrict_mem hA).mono (fun d hd => (hET r d hd).symm))
  have hslam : lam.map (fun x:ℝ => x/2)=lam :=
    push_invariant κ _ continuous_nonaffineDilate.measurable hsκ e he _ (measurable_id.div_const 2)
      ((ae_restrict_mem hA).mono (fun d hd => (hES d hd).symm))
  have hflam : lam (Ico 0 1)<∞ := by
    rw [Measure.map_apply he measurableSet_Ico,Measure.restrict_apply (he measurableSet_Ico),inter_comm]
    exact hf
  have hz : lam=0 := stationary_scaling_zero lam htlam hslam hflam
  have hh : lam univ=μ A := by rw [Measure.map_apply he MeasurableSet.univ,preimage_univ,Measure.restrict_apply_univ]
  rw [←hh,hz]; simp
namespace CriticalScaleSequence
variable (S:CriticalScaleSequence) (L:S.LimitLaws)
lemma remainder_local : IsFiniteMeasureOnCompacts (S.remainderLaw L) := by
  have : IsFiniteMeasureOnCompacts L.multi := L.multi_local
  exact ⟨fun K hK => (S.remainder_le L K).trans_lt hK.measure_lt_top⟩
lemma remainder_left_ray_zero : (S.remainderLaw L) {d:NonAffineArray | d.val∈leftRayClass}=0 := by
  have := S.remainder_local L
  apply invariant_interface_zero _ (S.remainder_translate L) (S.remainder_dilate L)
    {d:NonAffineArray | d.val∈leftRayClass} (measurableSet_leftRayClass.preimage measurable_subtype_coe)
    (fun d => endpointLeft d.val) (measurable_endpointLeft.comp measurable_subtype_coe)
  · intro r; ext d; exact leftRayClass_translate r d.val
  · ext d; exact leftRayClass_dilate d.val
  · intro r d hd; exact endpointLeft_translate r d.val hd.2.1 hd.1
  · intro d hd; exact endpointLeft_dilate d.val hd.2.1 hd.1
  · exact one_left_interface_finite _ (S.remainder_unit L) (S.remainder_shape L)
lemma remainder_right_ray_zero : (S.remainderLaw L) {d:NonAffineArray | d.val∈rightRayClass}=0 := by
  have := S.remainder_local L
  apply invariant_interface_zero _ (S.remainder_translate L) (S.remainder_dilate L)
    {d:NonAffineArray | d.val∈rightRayClass} (measurableSet_rightRayClass.preimage measurable_subtype_coe)
    (fun d => endpointRight d.val) (measurable_endpointRight.comp measurable_subtype_coe)
  · intro r; ext d; exact rightRayClass_translate r d.val
  · ext d; exact rightRayClass_dilate d.val
  · intro r d hd; exact endpointRight_translate r d.val hd.2.2 hd.2.1
  · intro d hd; exact endpointRight_dilate d.val hd.2.2 hd.2.1
  · exact one_right_interface_finite _ (S.remainder_unit L) (S.remainder_shape L)
end CriticalScaleSequence
end StandardMapEntropy

end OAI

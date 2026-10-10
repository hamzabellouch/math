import OAI.Dynamics.StandardMap.EndpointClasses

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal Classical
namespace StandardMapEntropy
lemma erealOrderIso_eq_bot (e:ℝ≃oℝ) (x:EReal) : erealOrderIso e x=⊥ ↔ x=⊥ := by
  constructor
  · intro h; apply (erealOrderIso e).injective; simpa only [erealOrderIso_bot] using h
  · intro h; rw [h,erealOrderIso_bot]
lemma erealOrderIso_eq_top (e:ℝ≃oℝ) (x:EReal) : erealOrderIso e x=⊤ ↔ x=⊤ := by
  constructor
  · intro h; apply (erealOrderIso e).injective; simpa only [erealOrderIso_top] using h
  · intro h; rw [h,erealOrderIso_top]
lemma leftRayClass_translate (r:DyadicTime) (d:DistanceArray) : arrayTranslate r d∈leftRayClass ↔ d∈leftRayClass := by
  change (_≠⊥ ∧ _≠⊤ ∧ _=⊤) ↔ _
  rw [(endpoints_translate r d).1,(endpoints_translate r d).2]
  simp only [ne_eq,erealOrderIso_eq_bot,erealOrderIso_eq_top]
  rfl
lemma rightRayClass_translate (r:DyadicTime) (d:DistanceArray) : arrayTranslate r d∈rightRayClass ↔ d∈rightRayClass := by
  change (_=⊥ ∧ _≠⊥ ∧ _≠⊤) ↔ _
  rw [(endpoints_translate r d).1,(endpoints_translate r d).2]
  simp only [ne_eq,erealOrderIso_eq_bot,erealOrderIso_eq_top]
  rfl
lemma twoRayClass_translate (r:DyadicTime) (d:DistanceArray) : arrayTranslate r d∈twoRayClass ↔ d∈twoRayClass := by
  change (_≠⊥ ∧ _≠⊤ ∧ _≠⊥ ∧ _≠⊤) ↔ _
  rw [(endpoints_translate r d).1,(endpoints_translate r d).2]
  simp only [ne_eq,erealOrderIso_eq_bot,erealOrderIso_eq_top]
  rfl
lemma leftRayClass_dilate (d:DistanceArray) : arrayDilate d∈leftRayClass ↔ d∈leftRayClass := by
  change (_≠⊥ ∧ _≠⊤ ∧ _=⊤) ↔ _
  rw [(endpoints_dilate d).1,(endpoints_dilate d).2]
  simp only [ne_eq,erealOrderIso_eq_bot,erealOrderIso_eq_top]
  rfl
lemma rightRayClass_dilate (d:DistanceArray) : arrayDilate d∈rightRayClass ↔ d∈rightRayClass := by
  change (_=⊥ ∧ _≠⊥ ∧ _≠⊤) ↔ _
  rw [(endpoints_dilate d).1,(endpoints_dilate d).2]
  simp only [ne_eq,erealOrderIso_eq_bot,erealOrderIso_eq_top]
  rfl
lemma twoRayClass_dilate (d:DistanceArray) : arrayDilate d∈twoRayClass ↔ d∈twoRayClass := by
  change (_≠⊥ ∧ _≠⊤ ∧ _≠⊥ ∧ _≠⊤) ↔ _
  rw [(endpoints_dilate d).1,(endpoints_dilate d).2]
  simp only [ne_eq,erealOrderIso_eq_bot,erealOrderIso_eq_top]
  rfl
lemma endpointLeft_translate (r:DyadicTime) (d:DistanceArray) (ht:leftEndpoint d≠⊤) (hb:leftEndpoint d≠⊥) :
    endpointLeft (arrayTranslate r d)=endpointLeft d-(r:ℝ) := by
  unfold endpointLeft
  rw [(endpoints_translate r d).1,←EReal.coe_toReal ht hb,erealOrderIso_coe]
  simp only [EReal.toReal_coe]
  rfl
lemma endpointRight_translate (r:DyadicTime) (d:DistanceArray) (ht:rightEndpoint d≠⊤) (hb:rightEndpoint d≠⊥) :
    endpointRight (arrayTranslate r d)=endpointRight d-(r:ℝ) := by
  unfold endpointRight
  rw [(endpoints_translate r d).2,←EReal.coe_toReal ht hb,erealOrderIso_coe]
  simp only [EReal.toReal_coe]
  rfl
lemma endpointLeft_dilate (d:DistanceArray) (ht:leftEndpoint d≠⊤) (hb:leftEndpoint d≠⊥) :
    endpointLeft (arrayDilate d)=endpointLeft d/2 := by
  unfold endpointLeft
  rw [(endpoints_dilate d).1,←EReal.coe_toReal ht hb,erealOrderIso_coe]
  simp only [EReal.toReal_coe]
  simp only [OrderIso.mulRight₀_apply]
  ring
lemma endpointRight_dilate (d:DistanceArray) (ht:rightEndpoint d≠⊤) (hb:rightEndpoint d≠⊥) :
    endpointRight (arrayDilate d)=endpointRight d/2 := by
  unfold endpointRight
  rw [(endpoints_dilate d).2,←EReal.coe_toReal ht hb,erealOrderIso_coe]
  simp only [EReal.toReal_coe]
  simp only [OrderIso.mulRight₀_apply]
  ring
lemma map_restrict_invariant {X:Type*} [MeasurableSpace X] (μ:Measure X) (f:X→X) (hf:Measurable f)
    (hm:μ.map f=μ) (A:Set X) (hA:MeasurableSet A) (hfA:f⁻¹'A=A) : (μ.restrict A).map f=μ.restrict A := by
  rw [←hfA,←Measure.restrict_map hf hA,hm,hfA]
lemma push_invariant {X Y:Type*} [MeasurableSpace X] [MeasurableSpace Y] (μ:Measure X)
    (f:X→X) (hf:Measurable f) (hm:μ.map f=μ) (e:X→Y) (he:Measurable e) (g:Y→Y) (hg:Measurable g)
    (hc:∀ᵐx ∂μ,g (e x)=e (f x)) : (μ.map e).map g=μ.map e := by
  rw [Measure.map_map hg he]
  calc
    μ.map (g ∘ e)=μ.map (e ∘ f) := Measure.map_congr hc
    _=(μ.map f).map e := (Measure.map_map he hf).symm
    _=μ.map e := by rw [hm]
end StandardMapEntropy

end OAI

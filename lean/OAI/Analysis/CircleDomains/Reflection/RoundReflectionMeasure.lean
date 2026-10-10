import OAI.Analysis.CircleDomains.Reflection.RoundReflectionDifferential
import OAI.Analysis.CircleDomains.Sobolev.SmoothWeightedL2Pullback

namespace OAI

/-! Circular reflection preserves planar null sets, including the harmless
chosen value at its single pole. -/
open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma roundReflectionPlane_measurable (c : ℂ) (r : ℝ) :
    Measurable (roundReflectionPlane c r) :=
  measurable_const.add (measurable_const.div
    (Complex.continuous_conj.measurable.comp (measurable_id.sub_const c)))

lemma roundReflectionPlane_quasiMeasurePreserving (c : ℂ) {r : ℝ} (hr : r≠0) :
    Measure.QuasiMeasurePreserving (roundReflectionPlane c r) volume volume := by
  let R := roundReflectionPlane c r
  have hR := roundReflectionPlane_involutive c hr
  refine ⟨roundReflectionPlane_measurable c r,Measure.AbsolutelyContinuous.mk ?_⟩
  intro s hs hs0
  rw [Measure.map_apply (roundReflectionPlane_measurable c r) hs]
  have heq : R ⁻¹' s=R '' s := by
    ext z
    constructor
    · intro hz
      exact ⟨R z,hz,hR z⟩
    · rintro ⟨w,hw,rfl⟩
      change roundReflectionPlane c r (roundReflectionPlane c r w)∈s
      rw [hR w]
      exact hw
  change volume (R ⁻¹' s)=0
  rw [heq]
  have hz : volume (s \ {c})=0 := measure_mono_null sdiff_subset hs0
  have hi : volume (R '' (s \ {c}))=0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      (fun z hz => (roundReflectionPlane_differentiable
        (show z≠c from fun h => hz.2 (by simp [h]))).differentiableWithinAt) hz
  apply measure_mono_null (show R '' s⊆R '' (s \ {c}) ∪ {c} from ?_)
    (measure_union_null hi (measure_singleton c))
  rintro z ⟨w,hw,rfl⟩
  by_cases hwc : w=c
  · right
    simp [R,roundReflectionPlane,hwc]
  · exact Or.inl ⟨w,⟨hw,by simpa using hwc⟩,rfl⟩

end CircleDomainRigidity

end

end OAI

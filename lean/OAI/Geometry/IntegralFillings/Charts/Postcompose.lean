import Mathlib
import OAI.Geometry.IntegralFillings.Currents.Pushforward

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace SharpIntegralFillings
open Set MeasureTheory
open CurrentOperations

namespace IntegerChart
variable {X Y : Type*} [MetricSpace X] [MetricSpace Y] {k : ℕ}
  (C : IntegerChart X k) {f : X → Y} {K J : ℝ≥0}

noncomputable def postcompose (hf : LipschitzWith K f)
    (hJ : AntilipschitzWith J (f ∘ C.param)) : IntegerChart Y k where
  domain := C.domain
  borel := C.borel
  bounded := C.bounded
  param := f ∘ C.param
  bilipschitz := by
    obtain ⟨L,U,hL,_⟩ := C.bilipschitz
    exact ⟨K*L,J,hf.comp hL,hJ⟩
  multiplicity := C.multiplicity
  integrable := C.integrable

lemma postcompose_scalar (hf : LipschitzWith K f)
    (hJ : AntilipschitzWith J (f ∘ C.param)) (b : Y → ℝ) :
    (C.postcompose hf hJ).scalar b = C.scalar (b ∘ f) := by
  classical
  funext x
  change (if h : x ∈ C.domain then b (f (C.param ⟨x,h⟩)) else 0) = _
  rfl

lemma postcompose_jacobian (hf : LipschitzWith K f)
    (hJ : AntilipschitzWith J (f ∘ C.param)) (π : Fin k → Y → ℝ) :
    (C.postcompose hf hJ).jacobian π = C.jacobian (fun i => π i ∘ f) := by
  rfl

lemma postcompose_action (hf : LipschitzWith K f)
    (hJ : AntilipschitzWith J (f ∘ C.param)) :
    (C.postcompose hf hJ).action = pushCurrent f C.action := by
  classical
  funext b π
  by_cases h : Admissible b π
  · rw [pushCurrent_apply f C.action h,action,ite_eq_left h,
      action,ite_eq_left (admissible_comp h hf)]
    change (∫ x in C.domain, (C.multiplicity x : ℝ)*
      (C.postcompose hf hJ).scalar b x*(C.postcompose hf hJ).jacobian π x) = _
    rw [C.postcompose_scalar hf hJ,C.postcompose_jacobian hf hJ]
  · simp only [action,pushCurrent,ite_eq_right h]

lemma postcompose_image (hf : LipschitzWith K f)
    (hJ : AntilipschitzWith J (f ∘ C.param)) :
    (C.postcompose hf hJ).image = f '' C.image := by
  exact range_comp f C.param

end IntegerChart

end SharpIntegralFillings
end

end OAI

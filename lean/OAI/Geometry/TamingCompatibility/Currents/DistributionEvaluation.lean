import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.ComplexMatrix

namespace OAI


noncomputable section
namespace TamingCompatibility.ComplexMatrix
open scoped SchwartzMap
variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {m n : ℕ}
lemma continuous_system_eval (L : E →L[ℝ] 𝓢'(D,C n))
    (P : 𝓢'(D,C n) →L[ℂ] 𝓢'(D,C m)) (φ : 𝓢(D,ℂ)) (i : Fin m) :
    Continuous (fun w => (P (L w) φ) i) := by
  exact (EuclideanSpace.proj (𝕜 := ℂ) i).continuous.comp
    ((PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) (C m) φ).continuous.comp
      (P.continuous.comp L.continuous))
lemma continuous_system_composed {T : Type*} [TopologicalSpace T]
    {f : T → 𝓢'(D,C n)} (hf : Continuous f)
    (P : 𝓢'(D,C n) →L[ℂ] 𝓢'(D,C m)) (φ : 𝓢(D,ℂ)) (i : Fin m) :
    Continuous (fun w => (P (f w) φ) i) :=
  (EuclideanSpace.proj (𝕜 := ℂ) i).continuous.comp
    ((PointwiseConvergenceCLM.evalCLM (RingHom.id ℂ) (C m) φ).continuous.comp
      (P.continuous.comp hf))
end TamingCompatibility.ComplexMatrix

end

end OAI

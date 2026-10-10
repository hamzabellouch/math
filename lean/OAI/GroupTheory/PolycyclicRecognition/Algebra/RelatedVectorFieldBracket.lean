import Mathlib.Analysis.Calculus.VectorField

namespace OAI

/-! # Brackets of related vector fields

The relation is local, so this lemma can be applied in a manifold chart.
It will identify the bracket of the actual representation differential.
-/

noncomputable section
namespace PolycyclicRecognition

open Filter
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem fderiv_lieBracket_of_related
    {f : E → F} {V W : E → E} {V' W' : F → F} {x : E}
    (hf : ContDiffAt ℝ 2 f x)
    (hV : DifferentiableAt ℝ V x) (hW : DifferentiableAt ℝ W x)
    (hV' : DifferentiableAt ℝ V' (f x)) (hW' : DifferentiableAt ℝ W' (f x))
    (hrelV : ∀ᶠ y in 𝓝 x, fderiv ℝ f y (V y) = V' (f y))
    (hrelW : ∀ᶠ y in 𝓝 x, fderiv ℝ f y (W y) = W' (f y)) :
    fderiv ℝ f x (VectorField.lieBracket ℝ V W x) =
      VectorField.lieBracket ℝ V' W' (f x) := by
  have hfd : DifferentiableAt ℝ f x := hf.differentiableAt (by norm_num)
  have hrelV' : (fun y => fderiv ℝ f y (V y)) =ᶠ[𝓝 x] V' ∘ f := hrelV
  have hrelW' : (fun y => fderiv ℝ f y (W y)) =ᶠ[𝓝 x] W' ∘ f := hrelW
  rw [VectorField.fderiv_apply_lieBracket hf (by norm_num) hW hV,
    hrelW'.fderiv_eq, hrelV'.fderiv_eq,
    fderiv_comp x hW' hfd, fderiv_comp x hV' hfd]
  simp only [ContinuousLinearMap.comp_apply, VectorField.lieBracket]
  have hVx : fderiv ℝ f x (V x) = V' (f x) := hrelV'.self_of_nhds
  have hWx : fderiv ℝ f x (W x) = W' (f x) := hrelW'.self_of_nhds
  rw [hVx, hWx]

end PolycyclicRecognition

end

end OAI

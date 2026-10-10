import OAI.GroupTheory.PolycyclicRecognition.Algebra.CoordinateOrbitRepresentation
import OAI.GroupTheory.PolycyclicRecognition.Geometry.FiniteCoordinateSmoothness
import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialFunctionSpace
import Mathlib.Geometry.Manifold.Algebra.LieGroup

namespace OAI

/-! # Smooth finite-dimensional actions from coordinate translates

This construction needs smooth coordinate functions, without assuming that
straight lines are exponential curves.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff

variable {G I W : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [Group G]
  [LieGroup (𝓘(ℝ, G)) ⊤ G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (q : I → G → ℝ) (B : W ≃ₗ[ℝ] coordinateOrbitSpan q)

def smoothCoordinateAction : Representation ℝ G W :=
  B.symm.conjRingEquiv.toMonoidHom.comp (coordinateOrbitRepresentation q)

omit [NormedAddCommGroup G] [NormedSpace ℝ G]
  [LieGroup (𝓘(ℝ, G)) ⊤ G] [FiniteDimensional ℝ W] in
theorem smoothCoordinateAction_eval (g : G) (v : W) (a : G) :
    (B (smoothCoordinateAction q B g v) : G → ℝ) a = (B v : G → ℝ) (a * g) := by
  change (B (B.symm (_)) : G → ℝ) a = _
  rw [B.apply_symm_apply]
  rfl

theorem contDiff_coordinateTranslate (hq : ∀ i, ContDiff ℝ ∞ (q i))
    {f : G → ℝ} (hf : f ∈ coordinateOrbitSpan q) (a : G) :
    ContDiff ℝ ∞ (fun g => f (a * g)) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨⟨h, i⟩, rfl⟩ := hf
    exact (hq i).comp (((contMDiff_mul_right (I := 𝓘(ℝ, G)) (a := h)).contDiff).comp
      ((contMDiff_mul_left (I := 𝓘(ℝ, G)) (a := a)).contDiff))
  | zero => exact contDiff_const
  | add f g _ _ hf hg => exact hf.add hg
  | smul c f _ hf => exact hf.const_smul c

theorem contDiff_smoothCoordinateAction (hq : ∀ i, ContDiff ℝ ∞ (q i)) (v : W) :
    ContDiff ℝ ∞ (fun g => smoothCoordinateAction q B g v) := by
  let e := (coordinateOrbitSpan q).subtype.comp B.toLinearMap
  apply contDiff_of_coordinateEvaluations e (Subtype.coe_injective.comp B.injective)
  intro a
  change ContDiff ℝ ∞ (fun g => (B (smoothCoordinateAction q B g v) : G → ℝ) a)
  simp only [smoothCoordinateAction_eval]
  exact contDiff_coordinateTranslate q hq (B v).2 a

omit [NormedAddCommGroup G] [NormedSpace ℝ G] [LieGroup (𝓘(ℝ, G)) ⊤ G] in
theorem polynomial_smoothCoordinateAction (γ : ℝ → G)
    (hγ : ∀ a b i, (fun t => q i ((a * γ t) * b)) ∈ polynomialFunctions)
    (v : W) (f : Module.Dual ℝ W) :
    (fun t => f (smoothCoordinateAction q B (γ t) v)) ∈ polynomialFunctions := by
  let e := (coordinateOrbitSpan q).subtype.comp B.toLinearMap
  apply polynomial_of_coordinateEvaluations e (Subtype.coe_injective.comp B.injective) _ ?_ f
  intro a
  change (fun t => (B (smoothCoordinateAction q B (γ t) v) : G → ℝ) a) ∈ polynomialFunctions
  simp only [smoothCoordinateAction_eval]
  have hfun (u : G → ℝ) (hu : u ∈ coordinateOrbitSpan q) :
      (fun t => u (a * γ t)) ∈ polynomialFunctions := by
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨⟨b, i⟩, rfl⟩ := hu
      exact hγ a b i
    | zero => exact polynomialFunctions.zero_mem
    | add f g _ _ hf hg => exact polynomialFunctions.add_mem hf hg
    | smul c f _ hf => exact polynomialFunctions.smul_mem c hf
  exact hfun _ (B v).2

end PolycyclicRecognition

end

end OAI

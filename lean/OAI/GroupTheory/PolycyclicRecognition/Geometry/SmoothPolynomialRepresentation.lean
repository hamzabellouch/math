import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialModelRepresentation
import OAI.GroupTheory.PolycyclicRecognition.Geometry.FiniteCoordinateSmoothness

namespace OAI

/-! # Smoothness of the polynomial-coordinate representation -/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold ContDiff

variable {L : Type*} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] {n : ℕ} (b : Module.Basis (Fin n) ℝ L)

theorem contDiff_translated_coordinateFunction {f : L → ℝ}
    (hf : f ∈ coordinateOrbitSpan (polynomialModelCoordinate b)) (a : L) :
    ContDiff ℝ ∞ (fun g => f (a * g)) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨⟨h, i⟩, rfl⟩ := hf
    have hm : ContDiff ℝ ∞ (fun g : L => (a * g) * h) :=
      ((contMDiff_mul_right (I := 𝓘(ℝ, L)) (a := h)).contDiff).comp
        ((contMDiff_mul_left (I := 𝓘(ℝ, L)) (a := a)).contDiff)
    exact contDiff_pi.mp (b.equivFun.toContinuousLinearEquiv.contDiff.comp hm) i
  | zero => exact contDiff_const
  | add f g _ _ hf hg => exact hf.add hg
  | smul c f _ hf => exact hf.const_smul c

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (B : W ≃ₗ[ℝ] coordinateOrbitSpan (polynomialModelCoordinate b))

def coordinateActionInBasis : Representation ℝ L W :=
  B.symm.conjRingEquiv.toMonoidHom.comp
    (coordinateOrbitRepresentation (polynomialModelCoordinate b))

omit [FiniteDimensional ℝ W] in
theorem coordinateActionInBasis_eval (g : L) (v : W) (a : L) :
    (B (coordinateActionInBasis b B g v) : L → ℝ) a = (B v : L → ℝ) (a * g) := by
  change (B (B.symm (_)) : L → ℝ) a = _
  rw [B.apply_symm_apply]
  rfl

theorem contDiff_coordinateActionInBasis (v : W) :
    ContDiff ℝ ∞ (fun g => coordinateActionInBasis b B g v) := by
  let e : W →ₗ[ℝ] (L → ℝ) :=
    (coordinateOrbitSpan (polynomialModelCoordinate b)).subtype.comp B.toLinearMap
  have he : Function.Injective e := Subtype.coe_injective.comp B.injective
  apply contDiff_of_coordinateEvaluations e he
  intro a
  have heq : (fun g => e (coordinateActionInBasis b B g v) a) =
      (fun g => (B v : L → ℝ) (a * g)) := by
    funext g
    exact coordinateActionInBasis_eval b B g v a
  rw [heq]
  exact contDiff_translated_coordinateFunction b (B v).2 a

omit [FiniteDimensional ℝ W] in
theorem coordinateActionInBasis_injective : Function.Injective (coordinateActionInBasis b B) :=
  B.symm.conjRingEquiv.injective.comp (polynomialModelRepresentation_injective b)

end PolycyclicRecognition

end

end OAI

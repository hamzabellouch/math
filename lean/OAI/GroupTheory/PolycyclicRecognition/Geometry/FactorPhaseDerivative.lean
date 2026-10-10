import OAI.GroupTheory.PolycyclicRecognition.Geometry.RealPhaseDerivative
import OAI.GroupTheory.PolycyclicRecognition.Geometry.DifferentialAlongExponential
import OAI.GroupTheory.PolycyclicRecognition.Algebra.ComplexFactorParameters
import OAI.GroupTheory.PolycyclicRecognition.Geometry.FactorRotationCharacter

namespace OAI

/-! # The infinitesimal character of the actual Cartan factorization -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  {a : ℕ} {T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ,E)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G}

namespace ComplexWeightFactorModel
variable (F : ComplexWeightFactorModel T H Exp)

theorem inverse_rotationCharacter_exp_line (t : ℝ) (x : GroupLieAlgebra (𝓘(ℝ,E)) G) :
    (F.rotationCharacter (Exp (t • x)))⁻¹ =
      realPhaseVector (GroupLieAlgebra (𝓘(ℝ,E)) G) H (t • (-T.cartanComponent H x)) := by
  rw [F.rotationCharacter_exp]
  change (realPhaseVector _ H (T.cartanComponent H (t • x)))⁻¹ = _
  rw [map_smul]
  have hh := (realPhaseHom (GroupLieAlgebra (𝓘(ℝ,E)) G) H).map_inv
    (Multiplicative.ofAdd (t • T.cartanComponent H x))
  change realPhaseVector _ H (-(t • T.cartanComponent H x)) = _ at hh
  rw [smul_neg]
  exact hh.symm

theorem hasDerivAt_inverse_factorPhase_line
    (x v : GroupLieAlgebra (𝓘(ℝ,E)) G) :
    HasDerivAt (fun t : ℝ =>
      (tangentTorusUnitAction H ((F.rotationCharacter (Exp (t • x)))⁻¹) : E →L[ℝ] E) v)
      (show E from -(T.weightImaginaryAction H x v)) 0 := by
  have hh := hasDerivAt_realPhase_line H (-T.cartanComponent H x) v
  have hneg : realImaginaryOperator (GroupLieAlgebra (𝓘(ℝ,E)) G) H
      (-T.cartanComponent H x) v = -(T.weightImaginaryAction H x v) := by
    have he := congrArg (fun D : LieDerivation ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)
      (GroupLieAlgebra (𝓘(ℝ,E)) G) => D v)
        ((realImaginaryDerivationLinear (GroupLieAlgebra (𝓘(ℝ,E)) G) H).map_neg
          (T.cartanComponent H x))
    exact he
  exact (hh.congr_deriv hneg).congr_of_eventuallyEq
    (Filter.Eventually.of_forall (fun t =>
      congrArg (fun z : realRotationTorus (GroupLieAlgebra (𝓘(ℝ,E)) G) H =>
        (tangentTorusUnitAction H z : E →L[ℝ] E) v)
        (F.inverse_rotationCharacter_exp_line t x)))

theorem mfderiv_inverse_factorPhase_apply (hExp : IsGroupExponential Exp)
    (x v : GroupLieAlgebra (𝓘(ℝ,E)) G) :
    mfderiv (𝓘(ℝ,E)) (𝓘(ℝ,E))
      (fun g => (tangentTorusUnitAction H ((F.rotationCharacter g)⁻¹) : E →L[ℝ] E) v) 1 x =
        -(T.weightImaginaryAction H x v) := by
  let q := invMonoidHom.comp F.rotationCharacter
  have hR : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E →L[ℝ] E)) ∞
      (fun g => (tangentTorusUnitAction H (q g) : E →L[ℝ] E)) :=
    contMDiff_tangentTorusRepresentation H hExp q F.continuous_rotationCharacter.inv
  have hv : ContMDiff (𝓘(ℝ,E)) (𝓘(ℝ,E)) ∞
      (fun g => (tangentTorusUnitAction H (q g) : E →L[ℝ] E) v) :=
    hR.clm_apply contMDiff_const
  exact mfderiv_apply_eq_of_exponential_line hExp
    (hv.mdifferentiableAt (by simp)) x _ (F.hasDerivAt_inverse_factorPhase_line x v)

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI

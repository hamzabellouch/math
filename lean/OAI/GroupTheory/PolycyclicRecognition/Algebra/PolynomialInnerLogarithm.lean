import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialInnerUnipotence
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CanonicalNilpotentLogarithm
import OAI.GroupTheory.PolycyclicRecognition.Geometry.AnalyticNilpotentExponential

namespace OAI

/-! # The exact logarithm of every inner automorphism in exponential coordinates -/

noncomputable section
namespace PolycyclicRecognition
variable {L : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]
local instance polynomialInnerRationalModule : Module ℚ L :=
  Module.compHom L (algebraMap ℚ ℝ)

theorem polynomial_inner_unipotent (w : L) :
    IsNilpotent ((polynomialInnerLieEquiv w).toLinearMap - 1) := by
  have h := polynomial_inner_mul_unipotent (LieEquiv.refl : L ≃ₗ⁅ℝ⁆ L)
    (by change IsNilpotent ((1 : Module.End ℝ L) - 1); simp) w
  change IsNilpotent ((polynomialInnerLieEquiv w).toLinearMap * 1 - 1) at h
  simpa only [mul_one] using h

theorem polynomial_inner_log (w : L) :
    nilpotentLog ((polynomialInnerLieEquiv w).toLinearMap - 1) = LieAlgebra.ad ℝ L w := by
  let E := Module.End.toContinuousLinearMap (𝕜 := ℝ) L
  let := NormedAlgebra.restrictScalars ℚ ℝ (L →L[ℝ] L)
  have hn : IsNilpotent (LieAlgebra.ad ℝ L w) :=
    LieModule.isNilpotent_toEnd_of_isNilpotent ℝ L L w
  have hexp : E (polynomialInnerLieEquiv w).toLinearMap =
      NormedSpace.exp (LinearMap.toContinuousLinearMap (LieAlgebra.ad ℝ L w)) := by
    apply ContinuousLinearMap.ext
    intro x
    exact (polynomialInnerLieEquiv_apply w x).trans (polynomial_inner_eq_exp_ad w x)
  apply E.injective
  have he : E (nilpotentLog ((polynomialInnerLieEquiv w).toLinearMap - 1)) =
      nilpotentLog (E ((polynomialInnerLieEquiv w).toLinearMap - 1)) :=
    (nilpotentLog_map E.toRingHom _ (polynomial_inner_unipotent w)).symm
  rw [he, map_sub, map_one, hexp]
  have hn' : IsNilpotent (LinearMap.toContinuousLinearMap (LieAlgebra.ad ℝ L w)) :=
    hn.map E.toRingHom
  rw [analytic_exp_eq_nilpotent_exp hn', nilpotentLog_exp _ hn']
  rfl

theorem polynomial_inner_eq_implies_ad_eq (u v : L)
    (h : (polynomialInnerLieEquiv u).toLinearMap = (polynomialInnerLieEquiv v).toLinearMap) :
    LieAlgebra.ad ℝ L u = LieAlgebra.ad ℝ L v := by
  rw [← polynomial_inner_log u, ← polynomial_inner_log v, h]

omit [LieRing.IsNilpotent L] in
theorem polynomial_inner_eq_of_ad_eq (u v : L)
    (h : LieAlgebra.ad ℝ L u = LieAlgebra.ad ℝ L v) :
    (polynomialInnerLieEquiv u).toLinearMap = (polynomialInnerLieEquiv v).toLinearMap := by
  apply LinearMap.ext
  intro x
  change polynomialInnerLieEquiv u x = polynomialInnerLieEquiv v x
  rw [polynomialInnerLieEquiv_apply, polynomialInnerLieEquiv_apply,
    polynomial_inner_eq_exp_ad, polynomial_inner_eq_exp_ad, h]

end PolycyclicRecognition

end

end OAI

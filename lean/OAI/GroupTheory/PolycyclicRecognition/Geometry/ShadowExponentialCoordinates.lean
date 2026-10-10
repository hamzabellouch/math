import OAI.GroupTheory.PolycyclicRecognition.Algebra.ComplexFactorParameters
import OAI.GroupTheory.PolycyclicRecognition.Geometry.CartanRealShadow
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Algebra.Lie.OfAssociative

namespace OAI

/-! # Linear coordinates for the two real-shadow exponential factors -/

noncomputable section
namespace PolycyclicRecognition
attribute [local instance 100] LieRing.ofAssociativeRing

variable {L A : Type} [LieRing L] [LieAlgebra ℝ L]
  [FiniteDimensional ℝ L]
  [NormedRing A] [NormedAlgebra ℝ A]
  {a : ℕ} (T : ComplexTriangularAdjoint L a)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]
  (j : CartanRealShadow T H →ₗ⁅ℝ⁆ A)

def shadowRepresentationParameter : L →ₗ[ℝ] A :=
  j.toLinearMap.comp (cartanRealShadowEquiv T H).toLinearMap

def shadowKernelParameter : L →ₗ[ℝ] A := (shadowRepresentationParameter T H j).comp
  (T.kernelIdeal.incl.toLinearMap.comp (T.kernelComponent H))

def shadowCartanParameter : L →ₗ[ℝ] A := (shadowRepresentationParameter T H j).comp
  (H.subtype.comp (T.cartanComponent H))

theorem shadowParameters_add : shadowKernelParameter T H j + shadowCartanParameter T H j =
    shadowRepresentationParameter T H j := by
  apply LinearMap.ext
  intro v
  change j (cartanRealShadowEquiv T H (T.kernelComponent H v)) +
    j (cartanRealShadowEquiv T H (T.cartanComponent H v)) = j (cartanRealShadowEquiv T H v)
  rw [← map_add, ← map_add, T.factorComponents_add H]

theorem shadowParameters_injective (hj : Function.Injective j) :
    Function.Injective (shadowKernelParameter T H j + shadowCartanParameter T H j) := by
  rw [shadowParameters_add]
  exact hj.comp (cartanRealShadowEquiv T H).injective

end PolycyclicRecognition

end

end OAI

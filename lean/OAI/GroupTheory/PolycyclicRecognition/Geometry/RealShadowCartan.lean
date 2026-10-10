import OAI.GroupTheory.PolycyclicRecognition.Geometry.RealShadowSplit

namespace OAI

/-! # The unchanged Cartan factor and its corrected adjoint action -/

noncomputable section
namespace PolycyclicRecognition
open LieAlgebra Module

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {a : ℕ} (T : ComplexTriangularAdjoint L a)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

/-- Every imaginary Cartan derivation annihilates the whole Cartan algebra. -/
theorem weightImaginaryAction_apply_cartan (x : L) (h : H) :
    T.weightImaginaryAction H x h = 0 :=
  realImaginaryOperator_cartan L H _ h

/-- The Cartan factor retains its original Lie bracket. -/
def realShadowCartanHom : H →ₗ⁅ℝ⁆ CartanRealShadow T H where
  toLinearMap := (cartanRealShadowEquiv T H).toLinearMap.comp H.subtype
  map_lie' {x y} := by
    apply (cartanRealShadowEquiv T H).symm.injective
    change ⁅(x : L),(y : L)⁆ =
      (cartanRealShadowEquiv T H).symm
        ⁅cartanRealShadowEquiv T H x,cartanRealShadowEquiv T H y⁆
    rw [cartanRealShadow_bracket, weightImaginaryAction_apply_cartan,
      weightImaginaryAction_apply_cartan, sub_zero, add_zero]

@[simp] theorem realShadowCartanHom_apply (h : H) :
    realShadowCartanHom T H h = cartanRealShadowEquiv T H h := rfl

/-- For a Cartan parameter, the modified adjoint is exactly the original
adjoint minus its imaginary semisimple part, on the entire vector space. -/
theorem realShadowAdjoint_cartan (h : H) (x : L) :
    realShadowAdjoint T H h x = ⁅(h : L),x⁆ - realImaginaryOperator L H h x := by
  rw [realShadowAdjoint_apply, T.weightImaginaryAction_cartan,
    weightImaginaryAction_apply_cartan, add_zero]

/-- The two operators whose exponentials occur in the rotational correction commute. -/
theorem realImaginaryOperator_commutes_ad (h : H) :
    Commute (realImaginaryOperator L H h) (ad ℝ L (h : L)) := by
  ext x
  change realImaginaryOperator L H h ⁅(h : L),x⁆ =
    ⁅(h : L),realImaginaryOperator L H h x⁆
  rw [realImaginaryOperator_lie, realImaginaryOperator_cartan, zero_lie, zero_add]

end PolycyclicRecognition

end

end OAI

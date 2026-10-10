import OAI.GroupTheory.PolycyclicRecognition.Geometry.RealCartanQuotient

namespace OAI

/-! # Linear parameters for the two actual complex-weight factors -/

noncomputable section
namespace PolycyclicRecognition

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  {n : ℕ} (T : ComplexTriangularAdjoint L n)
  (H : LieSubalgebra ℝ L) [H.IsCartanSubalgebra]

namespace ComplexTriangularAdjoint

def cartanComponent : L →ₗ[ℝ] H :=
  (T.cartanWeightSection H).comp T.weightMap.rangeRestrict

theorem cartanComponent_weight (x : L) :
    T.weightMap (T.cartanComponent H x : L) = T.weightMap x :=
  T.cartanWeightSection_weight H _

theorem cartanComponent_eq_zero {x : L} (hx : T.weightMap x = 0) :
    T.cartanComponent H x = 0 := by
  have he : T.weightMap.rangeRestrict x = 0 := Subtype.ext hx
  change T.cartanWeightSection H (T.weightMap.rangeRestrict x) = 0
  rw [he,map_zero]

def kernelComponent : L →ₗ[ℝ] T.kernelIdeal :=
  (LinearMap.id - H.subtype.comp (T.cartanComponent H)).codRestrict
    T.kernelIdeal.toSubmodule (fun x => by
      change T.weightMap (x - (T.cartanComponent H x : L)) = 0
      rw [map_sub,T.cartanComponent_weight H,sub_self])

theorem kernelComponent_coe (x : L) :
    (T.kernelComponent H x : L) = x - (T.cartanComponent H x : L) := rfl

theorem factorComponents_add (x : L) :
    (T.kernelComponent H x : L) + (T.cartanComponent H x : L) = x :=
  sub_add_cancel _ _

theorem kernelComponent_of_mem (x : T.kernelIdeal) : T.kernelComponent H (x : L) = x := by
  apply Subtype.ext
  rw [T.kernelComponent_coe H,T.cartanComponent_eq_zero H x.property]
  exact sub_zero _

end ComplexTriangularAdjoint
end PolycyclicRecognition

end

end OAI

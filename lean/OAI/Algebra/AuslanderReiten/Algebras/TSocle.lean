import OAI.Algebra.AuslanderReiten.Algebras.TCoordinates
import OAI.Algebra.AuslanderReiten.Algebras.TSimple
import OAI.Algebra.AuslanderReiten.Cocycles.CocycleDetector

namespace OAI

noncomputable section

namespace ArExplicit.T

variable {k : Type*} [Field k] (q : k)

theorem mul_upper_f (a : T k q) : a * upper q .f = simpleCharacter q a • upper q .f := by
  apply TrivialExtension.ext
  · simp [upper, TrivialExtension.inr]
  · apply LinearMap.ext
    intro c
    change (c * a.base).coeff .f + a.dual (0 * c) = a.base.coeff .f * c.coeff .f
    simp [BaseAlgebra.coeff_mul, BaseAlgebra.product, mul_comm]

def socleMap : Resolution.Simple q →ₗ[T k q] T k q where
  toFun s := Resolution.simpleCoordinate q s • upper q .f
  map_add' x y := by simp [add_smul]
  map_smul' a s := by
    change Resolution.simpleCoordinate q (a • s) • upper q .f =
      a * (Resolution.simpleCoordinate q s • upper q .f)
    rw [Resolution.t_simple_character, mul_smul_comm, mul_upper_f]
    change (a.base.coeff .f * Resolution.simpleCoordinate q s) • upper q .f =
      Resolution.simpleCoordinate q s • (a.base.coeff .f • upper q .f)
    rw [smul_smul, mul_comm]

@[simp] theorem socleMap_generator : socleMap q (CocycleData.simpleGenerator q) = upper q .f := by
  simp [socleMap]

theorem socleMap_injective (hq1 : 1 + q ≠ 0) : Function.Injective (socleMap q) := by
  intro x y h
  apply Resolution.simpleCoordinate_injective q hq1
  have hh := congrArg (coefficient q (true, .f)) h
  simpa [socleMap] using hh

end ArExplicit.T

end

end OAI

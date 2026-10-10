import OAI.GroupTheory.PolycyclicRecognition.Algebra.ControlledPrism
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.ControlledCochainMap
import OAI.GroupTheory.PolycyclicRecognition.Analysis.TupleChainPrism

namespace OAI

/-! # The controlled prism identity

The identity is inherited from the actual simplicial chain homotopy, after
the support estimate has placed every summand in the controlled complex.
-/

noncomputable section
namespace PolycyclicRecognition
open CategoryTheory
variable {G H R : Type} [Group G] [Group H] [CommRing R] {n : ℕ}

@[simp] theorem controlledLinearExtension_single (c : controlledCochains R G n)
    (x : Fin (n + 1) → G) (r : R) :
    controlledLinearExtension c (MonoidAlgebra.single x r) = r * c x := by
  simp [controlledLinearExtension]

def controlledLinearExtensionMap :
    controlledCochains R G n →ₗ[R] (MonoidAlgebra R (Fin (n + 1) → G) →ₗ[R] R) where
  toFun := controlledLinearExtension
  map_add' c d := by
    refine MonoidAlgebra.lhom_ext' fun x => LinearMap.ext_ring ?_
    simp [mul_add]
  map_smul' r c := by
    refine MonoidAlgebra.lhom_ext' fun x => LinearMap.ext_ring ?_
    simp

theorem controlledLinearExtension_injective :
    Function.Injective (controlledLinearExtension (R := R) (G := G) (n := n)) := by
  intro c d h
  apply Subtype.ext
  funext x
  have hx := congrArg (fun f => f (MonoidAlgebra.single x 1)) h
  simpa using hx

omit [Group G] in
theorem tupleChainComplex_boundary_linear :
    ((tupleChainComplex R G).d (n + 1) n).hom = Rep.standardComplex.d R G (n + 1) := by
  refine MonoidAlgebra.lhom_ext' fun (x : Fin (n + 2) → G) => LinearMap.ext_ring ?_
  change (tupleChainComplex R G).d (n + 1) n (MonoidAlgebra.single x 1) =
    Rep.standardComplex.d R G (n + 1) (MonoidAlgebra.single x 1)
  rw [tupleChainComplex_boundary, Rep.standardComplex.d_single]
  simp
  rfl

theorem controlledLinearExtension_pullback (e : GroupCoarseEquivalence G H)
    (c : controlledCochains R H n) :
    controlledLinearExtension (controlledCochainPullback e n c) =
      (controlledLinearExtension c).comp ((tupleChainMap e.toFun).f n).hom := by
  refine MonoidAlgebra.lhom_ext' fun x => LinearMap.ext_ring ?_
  change controlledLinearExtension (controlledCochainPullback e n c) (MonoidAlgebra.single x 1) =
    controlledLinearExtension c ((tupleChainMap e.toFun).f n (MonoidAlgebra.single x 1))
  rw [tupleChainMap_single]
  simp

theorem controlledLinearExtension_prism (e e' : GroupCoarseEquivalence G H)
    (hc : (Set.range fun x => (e.toFun x)⁻¹ * e'.toFun x).Finite)
    (c : controlledCochains R H (n + 1)) :
    controlledLinearExtension (controlledPrism e e' hc c) =
      (controlledLinearExtension c).comp
        ((tupleChainPrism e.toFun e'.toFun).hom n (n + 1)).hom := by
  refine MonoidAlgebra.lhom_ext' fun x => LinearMap.ext_ring ?_
  change controlledLinearExtension (controlledPrism e e' hc c) (MonoidAlgebra.single x 1) =
    controlledLinearExtension c
      ((tupleChainPrism e.toFun e'.toFun).hom n (n + 1) (MonoidAlgebra.single x 1))
  rw [tupleChainPrism_single]
  simp

end PolycyclicRecognition

end

end OAI

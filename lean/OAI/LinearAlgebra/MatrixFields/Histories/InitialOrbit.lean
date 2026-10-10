import Mathlib
import OAI.LinearAlgebra.MatrixFields.Entropy.InitialEntropy

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

namespace MatrixMultiplication.AllFieldInitialOrbit

open AllFieldParameters AllFieldHistory AllFieldInitialEntropy
open scoped BigOperators

theorem source_total (p : PlacedInitial) :
    (initialShapeCode p).1.val + (initialShapeCode p).2.1.val +
      (initialShapeCode p).2.2.val = 16 := by
  unfold initialShapeCode rootShape
  rw [encodePhysicalShape_total]
  exact (root_shape_spec _ (initialShape_mem _)).2

theorem decodeShape_injective : Function.Injective decodeShape := by
  intro u v h
  apply Prod.ext
  · exact Fin.ext (congrFun h 0)
  · apply Prod.ext
    · exact Fin.ext (congrFun h 1)
    · exact Fin.ext (congrFun h 2)

theorem decodeShape_mem_shapes (u : JointPopulation.Shape)
    (hu : u.1.val + u.2.1.val + u.2.2.val = 16) :
    decodeShape u ∈ shapes 16 := by
  simp only [shapes, List.mem_flatMap, List.mem_map, List.mem_range]
  refine ⟨u.1.val, by omega, u.2.1.val, by omega, ?_⟩
  funext i
  fin_cases i
  · rfl
  · rfl
  · change 16 - u.1.val - u.2.1.val = u.2.2.val
    omega

theorem initialShapeCode_eq_iff (p : PlacedInitial) (u : JointPopulation.Shape) :
    initialShapeCode p = u ↔
      physicalShape p.2 (sortedInitial.get p.1) = decodeShape u := by
  have hdecode : decodeShape (initialShapeCode p) =
      physicalShape p.2 (sortedInitial.get p.1) := by
    funext i
    exact initialShapeCode_side p i
  rw [← hdecode]
  exact decodeShape_injective.eq_iff.symm

theorem weighted_shape_fiber_count : ∀ u ∈ shapes 16,
    (∑ p : PlacedInitial,
      if physicalShape p.2 (sortedInitial.get p.1) = u
      then initialMultiplicity (sortedInitial.get p.1) else 0) = 6 := by
  decide +kernel

theorem weighted_fiber_count (u : JointPopulation.Shape)
    (hu : u.1.val + u.2.1.val + u.2.2.val = 16) :
    (∑ p : PlacedInitial, if initialShapeCode p = u
      then initialMultiplicity (sortedInitial.get p.1) else 0) = 6 := by
  simp only [initialShapeCode_eq_iff]
  exact weighted_shape_fiber_count _ (decodeShape_mem_shapes u hu)

end MatrixMultiplication.AllFieldInitialOrbit

end MatrixAllFields

end OAI

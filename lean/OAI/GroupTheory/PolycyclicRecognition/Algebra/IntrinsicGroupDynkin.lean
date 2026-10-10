import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialModelDynkin
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentIntrinsicIntegration

namespace OAI

/-! # Finite BCH for arbitrary finite-dimensional real Lie groups

The constructed nilpotent coordinate model maps to the target by the proved
intrinsic integration theorem. Its exact class-bounded product formula descends
without a representation or simple-connectivity hypothesis on the target.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold
attribute [local instance 100] LieRing.ofAssociativeRing

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G]

theorem nilpotentDynkinExpansionInput : NilpotentDynkinExpansionInput E G := by
  intro Exp hExp c hc n
  let T := GroupLieAlgebra (𝓘(ℝ, E)) G
  let : RealNormedLieAlgebra T :=
    { (inferInstance : NormedAddCommGroup E), (inferInstance : LieRing T),
      (inferInstance : NormedSpace ℝ E), (inferInstance : LieAlgebra ℝ T) with }
  let finiteT : FiniteDimensional ℝ T := by
    change FiniteDimensional ℝ E
    infer_instance
  have hn : LieRing.IsNilpotent T := (LieModule.isNilpotent_iff ℝ T T).mpr ⟨c, hc⟩
  obtain ⟨P⟩ := @polynomialExponentialCoordinates_nilpotent T _ finiteT hn
  let := P
  let : Group T := P.group
  obtain ⟨φ, _, hφ⟩ := @integrate_polynomial_nilpotent E G _ _ _ _ _ _ _ _ Exp hExp T _ finiteT P hn (LieHom.id)
  refine ⟨universalDynkinCoefficients c n, universalDynkinCoefficients_bound c n, ?_⟩
  intro X
  have hp := congrArg φ (@polynomialCoordinate_product_of_class T _ finiteT P c n hc X)
  rw [map_list_prod, List.map_ofFn] at hp
  simp only [Function.comp_def, hφ] at hp
  convert hp using 1 <;> rfl

end PolycyclicRecognition

end

end OAI

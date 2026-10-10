import OAI.GroupTheory.PolycyclicRecognition.Algebra.PolynomialModelDynkin
import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentFaithfulIntegration

namespace OAI

/-! # Finite BCH for faithfully represented Lie groups

The target representation need not have nilpotent operators. Instead, the
constructed nilpotent coordinate model maps to the target by the proved
integration theorem. Its exact class-bounded product formula then descends.
-/

noncomputable section
namespace PolycyclicRecognition

open scoped Manifold
attribute [local instance 100] LieRing.ofAssociativeRing

variable {E G A : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace G] [ChartedSpace E G] [Group G]
  [LieGroup (𝓘(ℝ, E)) ⊤ G] [T2Space G]
  [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

theorem nilpotentDynkinExpansionInput_of_faithful
    (ρ : G →* Aˣ) (hρ : Function.Injective ρ)
    (j : GroupLieAlgebra (𝓘(ℝ, E)) G →ₗ⁅ℝ⁆ A)
    (hd : HasMFDerivAt (𝓘(ℝ, E)) (𝓘(ℝ, A)) (fun g => (ρ g : A)) 1
      j.toLinearMap.toContinuousLinearMap) : NilpotentDynkinExpansionInput E G := by
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
  obtain ⟨φ, _, hφ⟩ := @integrate_polynomial_nilpotent_to_faithful E G A _ _ _ _ _ _ _ _ _ _ _ Exp hExp ρ hρ j
    (hom_exp_eq_algebraExpUnit hExp ρ j.toLinearMap.toContinuousLinearMap hd) T _ finiteT P hn (LieHom.id)
  refine ⟨universalDynkinCoefficients c n, universalDynkinCoefficients_bound c n, ?_⟩
  intro X
  have hp := congrArg φ (@polynomialCoordinate_product_of_class T _ finiteT P c n hc X)
  rw [map_list_prod, List.map_ofFn] at hp
  simp only [Function.comp_def, hφ] at hp
  convert hp using 1 <;> rfl

end PolycyclicRecognition

end

end OAI

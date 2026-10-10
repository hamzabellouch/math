import OAI.GroupTheory.PolycyclicRecognition.Geometry.RotationFactorKernel
import OAI.GroupTheory.PolycyclicRecognition.Geometry.RotationalTwistConjugation

namespace OAI

/-! # The Cartan action on the nilpotent factor of the rotational graph -/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold

variable {E G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MetricSpace G] [ChartedSpace E G]
  [Group G] [LieGroup (𝓘(ℝ,E)) ⊤ G]
  {a : ℕ} {T : ComplexTriangularAdjoint (GroupLieAlgebra (𝓘(ℝ,E)) G) a}
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ,E)) G)} [H.IsCartanSubalgebra]
  {Exp : GroupLieAlgebra (𝓘(ℝ,E)) G → G}

namespace ComplexWeightFactorModel
variable (F : ComplexWeightFactorModel T H Exp) (hExp : IsGroupExponential Exp)
attribute [local instance] semidirectProductTopology

def rotationFactorAction : F.D.carrier →* MulAut F.N.carrier :=
  conjugationLiftOfNormal (F.nilpotentFactorToRotation hExp) (F.cartanFactorToRotation hExp)
    (F.closedEmbedding_nilpotentFactorToRotation hExp).injective
    (F.normal_nilpotentFactorToRotation hExp)

theorem rotationFactorAction_conjugation (d : F.D.carrier) (n : F.N.carrier) :
    F.nilpotentFactorToRotation hExp (F.rotationFactorAction hExp d n) =
      F.cartanFactorToRotation hExp d * F.nilpotentFactorToRotation hExp n *
        (F.cartanFactorToRotation hExp d)⁻¹ :=
  conjugationLiftOfNormal_spec _ _ _ _ d n

theorem rotationFactorAction_exponential (h : H) (x : T.kernelIdeal) :
    F.rotationFactorAction hExp (F.ExpD (F.D.equiv h)) (F.ExpN (F.N.equiv x)) =
      F.ExpN (F.N.equiv (T.nilradicalRotation H
        (realPhaseVector (GroupLieAlgebra (𝓘(ℝ,E)) G) H h)⁻¹
        ⟨adjointLinearMap (E := E) (Exp h) (x : GroupLieAlgebra (𝓘(ℝ,E)) G),
          cartan_conjugation_mem hExp h x⟩)) := by
  apply F.closedN.injective
  have hc := congrArg (F.smoothRotationalModificationHomeomorph hExp)
    (F.rotationFactorAction_conjugation hExp
      (F.ExpD (F.D.equiv h)) (F.ExpN (F.N.equiv x)))
  have ht := rotationalTwistLift_conjugation_left
    (F.factorCompactRotationAction hExp) F.rotationCharacter
    (F.factorCompactRotationAction_invariant hExp) F.inclusionN F.inclusionD
    (F.inverse_rotation_fixes_nilpotent_factor hExp)
    (F.inverse_rotation_fixes_cartan_factor hExp)
    (F.ExpD (F.D.equiv h)) (F.ExpN (F.N.equiv x))
    (F.rotationCharacter_nilradical x)
  have he := hc.trans ht
  change F.inclusionN (F.rotationFactorAction hExp _ _) = _ at he
  let y : T.kernelIdeal := ⟨adjointLinearMap (E := E) (Exp h)
    (x : GroupLieAlgebra (𝓘(ℝ,E)) G), cartan_conjugation_mem hExp h x⟩
  have hchar := (congrArg F.rotationCharacter (F.compatibleD h)).trans
    (F.rotationCharacter_cartan h)
  have harg : F.inclusionD (F.ExpD (F.D.equiv h)) *
      F.inclusionN (F.ExpN (F.N.equiv x)) * (F.inclusionD (F.ExpD (F.D.equiv h)))⁻¹ =
      Exp (y : GroupLieAlgebra (𝓘(ℝ,E)) G) := by
    rw [F.compatibleD h, F.compatibleN x]
    exact conjugation_exponential hExp (Exp h) x
  have hrotate := congrArg₂ (fun z g => F.factorCompactRotationAction hExp z⁻¹ g)
    hchar harg
  exact he.trans (hrotate.trans ((F.rotation_exp_nilradical (F.factorCompactRotationAction hExp)
    (F.factorCompactRotationAction_formula hExp) _ y).trans (F.compatibleN _).symm))

end ComplexWeightFactorModel
end PolycyclicRecognition

end

end OAI

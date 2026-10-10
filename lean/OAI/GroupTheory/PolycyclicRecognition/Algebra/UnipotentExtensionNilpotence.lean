import OAI.GroupTheory.PolycyclicRecognition.Lattices.JointFixedResidualNilpotent

namespace OAI

/-! # Nilpotence from unipotent quotient generators

This applies the proved lower-central-layer argument to the entire kernel:
the auxiliary fixed family consists only of the identity operator.
-/

noncomputable section
namespace PolycyclicRecognition
open scoped Manifold ContDiff IsMulCommutative
attribute [local instance] polynomialSubalgebraGroup
variable {L G Q : Type} [RealNormedLieAlgebra L] [FiniteDimensional ℝ L]
  [P : PolynomialExponentialCoordinates L] [LieRing.IsNilpotent L]
  [Group G] [Group Q] [IsMulCommutative Q]

theorem extension_nilpotent_of_unipotent_generators (E : GroupExtension L G Q)
    (hsmooth : ∀ g : G, ContMDiff (𝓘(ℝ, L)) (𝓘(ℝ, L)) ∞ (E.conjAct g))
    (σ : E.Section) (hσ : σ 1 = 1) (qs : List Q)
    (hgen : Subgroup.closure {q | q ∈ qs} = ⊤)
    (hu : ∀ q ∈ qs,
      IsNilpotent ((polynomialModelLieEquiv (E.conjAct (σ q)) (hsmooth (σ q))).toLinearMap - 1)) :
    Group.IsNilpotent G := by
  let D : JointFixedReductionData E hsmooth qs :=
    { operators := [LieEquiv.refl]
      semisimple := by
        intro S hS
        have he : S = LieEquiv.refl := List.mem_singleton.mp hS
        subst S
        exact Module.End.isSemisimple_id
      commute := by
        intro S hS T hT
        have hS' : S = LieEquiv.refl := List.mem_singleton.mp hS
        have hT' : T = LieEquiv.refl := List.mem_singleton.mp hT
        subst S
        subst T
        exact Commute.refl _
      sectionMap := σ
      normalized := hσ
      centralizes := by
        intro S hS q
        have he : S = LieEquiv.refl := List.mem_singleton.mp hS
        subst S
        apply (mem_semisimpleActionCentralizer_iff E _ _ (hsmooth (σ q))).mpr
        exact Commute.one_left _
      factorsFixed := by
        intro S hS q r
        have he : S = LieEquiv.refl := List.mem_singleton.mp hS
        subst S
        rfl
      jordanLifts := by
        intro q hq
        refine ⟨LieEquiv.refl, List.mem_singleton_self _,
          polynomialModelLieEquiv (E.conjAct (σ q)) (hsmooth (σ q)), hu q hq,
          Commute.one_left _, ?_⟩
        exact (one_mul _).symm }
  let := D.residual_nilpotent hgen
  apply Group.nilpotent_of_surjective D.residualEmbedding
  intro g
  let a := GroupExtensionSection.mulEquiv E σ hσ g
  have hx : a.left ∈ jointFixedLieSubalgebra D.operators := by
    intro S hS
    have he : S = LieEquiv.refl := List.mem_singleton.mp hS
    subst S
    rfl
  let b : FactorExtension D.residualSystem := ⟨⟨a.left, hx⟩, a.right⟩
  refine ⟨b, ?_⟩
  change (GroupExtensionSection.mulEquiv E σ hσ).symm
    (jointFixedFactorInclusion _ D.action _ D.operators _ _ b) = g
  have hb : jointFixedFactorInclusion _ D.action _ D.operators _ _ b = a := by
    apply FactorExtension.ext <;> rfl
  rw [hb]
  exact (GroupExtensionSection.mulEquiv E σ hσ).symm_apply_apply g

end PolycyclicRecognition

end

end OAI

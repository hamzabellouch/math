import OAI.GroupTheory.PolycyclicRecognition.Algebra.RationalNilpotentQuotient

namespace OAI

/-! # The rational linear quotient of a finite-dimensional solvable group

The vector space is the product of the rational upper central layers of an
actual maximal nilpotent normal subgroup. Its action is faithful on the
quotient. No finite generation of the nilpotent subgroup is assumed.
-/

noncomputable section
namespace PolycyclicRecognition

structure FiniteRationalLinearModel (Q : Type) [Group Q] where
  space : Type
  [addCommGroup : AddCommGroup space]
  [module : Module ℚ space]
  [finite : Module.Finite ℚ space]
  action : Q →* (space ≃ₗ[ℚ] space)
  faithful : Function.Injective action

attribute [instance] FiniteRationalLinearModel.addCommGroup
  FiniteRationalLinearModel.module FiniteRationalLinearModel.finite

variable {G : Type} [Group G] [Group.IsSolvable G]

theorem exists_nilpotent_normal_rational_linear_quotient
    (hG : HasFiniteIntegralCohomologicalDimension G) :
    ∃ F : Subgroup G, ∃ _ : F.Normal, Group.IsNilpotent F ∧
      Nonempty (FiniteRationalLinearModel (G ⧸ F)) := by
  obtain ⟨F, hFn, hF, hmax⟩ := exists_maximal_nilpotent_normal_subgroup hG
  let := hFn
  let := hF
  have hFcd := hG.subgroup F
  have hFtf := hFcd.torsionFree
  let := centralLayersSpace_finite F hFcd (Group.nilpotencyClass F)
  exact ⟨F, hFn, hF, ⟨{
    space := CentralLayersSpace F (Group.nilpotencyClass F)
    action := nilpotentQuotientRationalAction F hFtf hmax
    faithful := nilpotentQuotientRationalAction_injective F hFtf hmax }⟩⟩

end PolycyclicRecognition

end

end OAI

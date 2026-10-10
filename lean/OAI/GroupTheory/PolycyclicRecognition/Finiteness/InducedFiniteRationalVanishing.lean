import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteGroupRationalTelescope
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SubgroupInductionExact
import OAI.GroupTheory.PolycyclicRecognition.Finiteness.CompletedCohomologyProjective

namespace OAI

/-! # Rational vanishing for coefficients induced from finite subgroups

This is the finite-stabilizer base of the hierarchy argument. Both the
projective dimension bound and the resulting complete-cohomology vanishing
are proved, without a finiteness condition on the ambient group.
-/
noncomputable section
namespace PolycyclicRecognition
open CategoryTheory CategoryTheory.Limits
attribute [local instance 2000] Rep.hV2 Rep.instLinear
variable {G : Type} [Group G]

theorem finiteSubgroup_induced_rational_projectiveDimension_le_one
    (H : Subgroup G) [Finite H] :
    HasProjectiveDimensionLE (Rep.ind H.subtype (Rep.trivial ℤ H ℚ)) 1 := by
  let := Fintype.ofFinite H
  let F := Rep.indFunctor ℤ H.subtype
  let c := finiteGroupRationalColimit H
  let S := c.telescopeSequence
  let : ∀ i, Projective ((finiteGroupRationalDiagram H).obj i) := fun i => by
    change Projective (finiteGroupRationalStage H)
    infer_instance
  let : Mono S.f := c.telescopeSequence_shortExact.mono_f
  let : Epi S.g := c.telescopeSequence_shortExact.epi_g
  have hS : (S.map F).ShortExact := (c.telescopeSequence_shortExact).map F
  have h₁ : Projective (F.obj S.X₁) := by
    change Projective (F.obj (finiteGroupRationalDiagram H).telescopeSum)
    infer_instance
  have h₂ : Projective (F.obj S.X₂) := by
    change Projective (F.obj (finiteGroupRationalDiagram H).telescopeSum)
    infer_instance
  let := h₁
  let := h₂
  exact hS.hasProjectiveDimensionLT_X₃ 1
    (show HasProjectiveDimensionLT (F.obj S.X₁) 1 from inferInstance)
    (hasProjectiveDimensionLT_of_ge (F.obj S.X₂) 1 2 (by omega))

theorem finiteSubgroup_induced_rational_completeCohomology
    (H : Subgroup G) [Finite H] :
    Subsingleton (CompletedCohomology (Rep.ind H.subtype (Rep.trivial ℤ H ℚ))) := by
  let := finiteSubgroup_induced_rational_projectiveDimension_le_one H
  exact completedCohomology_subsingleton_of_finite_projectiveDimension _ 1

end PolycyclicRecognition

end

end OAI

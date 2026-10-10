import OAI.NumberTheory.CubicMoment.Theta.CubicThetaComplexLocalization
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoreProfiles

namespace OAI

/-! The abstract chart estimate applies to the actual arithmetic core
profiles already constructed from the quotient's smooth bump functions. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaCorePointSupport (c : CubicThetaQuotient) : Set CubicThetaPoint :=
  cubicThetaPointInclusion.symm '' tsupport (cubicThetaCoreProfile c)

lemma cubicThetaCorePointSupport_compact (c : CubicThetaQuotient) :
    IsCompact (cubicThetaCorePointSupport c) := by
  have hinc : ContinuousOn cubicThetaPointInclusion.symm {y : ℂ × ℝ | 0<y.2} := by
    simpa only [OpenPartialHomeomorph.symm_source,cubicThetaPointInclusion_target] using
      cubicThetaPointInclusion.symm.continuousOn
  exact (cubicThetaCoreProfile_compact c).image_of_continuousOn
    (hinc.mono (cubicThetaCoreProfile_support_positive c))

lemma cubicThetaCorePointSupport_sheet (c : CubicThetaQuotient) :
    cubicThetaCorePointSupport c⊆(cubicThetaCoveringChart (cubicThetaQuotientLift c)).source := by
  rintro p ⟨y,hy,rfl⟩
  have ht := cubicThetaCoreProfile_support_target c hy
  change y∈cubicThetaPointInclusion.target ∧
    cubicThetaPointInclusion.symm y∈(cubicThetaCoveringChart (cubicThetaQuotientLift c)).source at ht
  exact ht.2

lemma cubicThetaCoreProfile_support_coordinates (c : CubicThetaQuotient) :
    tsupport (cubicThetaCoreProfile c)⊆cubicThetaPointCoordinates '' cubicThetaCorePointSupport c := by
  intro y hy
  refine ⟨cubicThetaPointInclusion.symm y,⟨y,hy,rfl⟩,?_⟩
  exact cubicThetaPointInclusion.right_inv
    (by rw [cubicThetaPointInclusion_target]; exact cubicThetaCoreProfile_support_positive c hy)

def cubicThetaCoreLocalInclusion (c : CubicThetaQuotient) :
    cubicThetaGlobalEnergySpace →L[ℂ] LocalSobolev.TangentComplexL2 :=
  cubicThetaComplexLocalInclusion (cubicThetaCoreProfile_contDiff c)
    (cubicThetaCoreProfile_compact c) (cubicThetaCoreProfile_support_positive c)

theorem cubicThetaCoreLocalInclusion_compact (c : CubicThetaQuotient) :
    IsCompactOperator (cubicThetaCoreLocalInclusion c) :=
  cubicThetaComplexLocalInclusion_compact (cubicThetaCoreProfile_contDiff c)
    (cubicThetaCoreProfile_compact c) (cubicThetaCoreProfile_support_positive c)
    (cubicThetaCoveringChart (cubicThetaQuotientLift c)) (cubicThetaCoveringChart_coe _)
    (cubicThetaCorePointSupport_compact c) (cubicThetaCorePointSupport_sheet c)
    (cubicThetaCoreProfile_support_coordinates c)

theorem cubicThetaCoreLocalInclusion_test (c : CubicThetaQuotient) (F : cubicThetaSmoothTests) :
    cubicThetaCoreLocalInclusion c (cubicThetaGlobalEnergyTest F)=
      cubicThetaLocalValue (cubicThetaCoreProfile_contDiff c)
        (cubicThetaCoreProfile_compact c) (cubicThetaCoreProfile_support_positive c) F :=
  cubicThetaComplexLocalInclusion_test (cubicThetaCoreProfile_contDiff c)
    (cubicThetaCoreProfile_compact c) (cubicThetaCoreProfile_support_positive c)
    (cubicThetaCoveringChart (cubicThetaQuotientLift c)) (cubicThetaCoveringChart_coe _)
    (cubicThetaCorePointSupport_compact c) (cubicThetaCorePointSupport_sheet c)
    (cubicThetaCoreProfile_support_coordinates c) F

end CubicFirstMoment

end

end OAI

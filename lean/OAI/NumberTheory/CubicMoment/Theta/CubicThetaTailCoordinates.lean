import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoordinateMass
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCoefficientTailSupport

namespace OAI

/-! Explicit coordinate parametrizations for the two arithmetic remainder families. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaOrdinaryCoordinate (p : CubicThetaIntegerPoint) : Eisenstein :=
  ofCoords p.1 p.2

def cubicThetaPrimaryCoordinate (p : CubicThetaIntegerPoint) : Eisenstein :=
  ofCoords (1+3*p.1) (3*p.2)

lemma cubicThetaOrdinaryCoordinate_norm (p : CubicThetaIntegerPoint) :
    norm (cubicThetaOrdinaryCoordinate p)=cubicThetaIntegerQuadratic p := by
  rw [cubicThetaOrdinaryCoordinate,norm,ofCoords_coe,coordinates_norm]
  push_cast
  rfl

lemma cubicThetaPrimaryCoordinate_norm (p : CubicThetaIntegerPoint) :
    norm (cubicThetaPrimaryCoordinate p)=cubicThetaPrimaryQuadratic p := by
  rw [cubicThetaPrimaryCoordinate,norm,ofCoords_coe,coordinates_norm]
  push_cast
  rfl

lemma cubicThetaPrimaryCoordinate_eq (p : CubicThetaIntegerPoint) :
    cubicThetaPrimaryCoordinate p=1+3*cubicThetaOrdinaryCoordinate p := by
  unfold cubicThetaPrimaryCoordinate cubicThetaOrdinaryCoordinate ofCoords
  push_cast
  ring

lemma cubicThetaPrimaryCoordinate_primary (p : CubicThetaIntegerPoint) :
    primary (cubicThetaPrimaryCoordinate p) := by
  refine ⟨cubicThetaOrdinaryCoordinate p,?_⟩
  rw [cubicThetaPrimaryCoordinate_eq]
  ring

lemma cubicThetaPrimaryCoordinate_zero : cubicThetaPrimaryCoordinate (0,0)=1 := by
  apply Subtype.ext
  norm_num [cubicThetaPrimaryCoordinate,ofCoords_coe]

lemma cubicThetaOrdinaryCoordinate_zero : cubicThetaOrdinaryCoordinate (0,0)=0 := by
  apply Subtype.ext
  norm_num [cubicThetaOrdinaryCoordinate,ofCoords_coe]

lemma cubicThetaPrimaryCoordinate_exists {m : Eisenstein} (hm : primary m) (hne : m≠1) :
    ∃ p : CubicThetaIntegerPoint,p≠(0,0) ∧ cubicThetaPrimaryCoordinate p=m := by
  obtain ⟨w,hw⟩ := hm
  obtain ⟨p,hp⟩ := ofCoords_surjective w
  change ofCoords p.1 p.2=w at hp
  have he : cubicThetaPrimaryCoordinate p=m := by
    rw [cubicThetaPrimaryCoordinate_eq]
    change 1+3*ofCoords p.1 p.2=m
    rw [hp]
    linear_combination -hw
  refine ⟨p,?_,he⟩
  intro h
  exact hne (by rw [←he,h,cubicThetaPrimaryCoordinate_zero])

lemma cubicThetaOrdinaryCoordinate_exists {m : Eisenstein} (hm : m≠0) :
    ∃ p : CubicThetaIntegerPoint,p≠(0,0) ∧ cubicThetaOrdinaryCoordinate p=m := by
  obtain ⟨p,hp⟩ := ofCoords_surjective m
  refine ⟨p,?_,hp⟩
  intro h
  exact hm (by rw [←hp]; change cubicThetaOrdinaryCoordinate p=0
               rw [h,cubicThetaOrdinaryCoordinate_zero])

end CubicFirstMoment

end

end OAI

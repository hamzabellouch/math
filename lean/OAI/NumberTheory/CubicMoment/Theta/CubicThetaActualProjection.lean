import OAI.NumberTheory.CubicMoment.Theta.CubicThetaActualCuspCoefficients
import OAI.NumberTheory.CubicGram.IntegerBasis

namespace OAI

/-! The actual primary projector and its finite transformed cusp family. -/
noncomputable section
open scoped MatrixGroups Matrix
namespace CubicFirstMoment
attribute [local instance] Classical.propDecidable

def cubicThetaCuspIndex (b : Eisenstein) : ℤ := coordinatesEquiv.symm b 1

lemma cubicThetaCuspCoordinates (b : Eisenstein) :
    b=((coordinatesEquiv.symm b 0:ℤ):Eisenstein)+cubicThetaCuspIndex b*omegaE :=
  (coordinatesEquiv.apply_symm_apply b).symm

lemma cubicThetaNormalizedSeries_primaryBottom_index (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (p : CubicThetaPoint) :
    cubicThetaNormalizedSeriesSection.val (g • p)=
      cubicThetaKubotaValue (cubicThetaPrimaryBottomPrincipal g hc)*
        cubicThetaCuspExpansion (cubicThetaCuspIndex (g 0 0))
          (cubicThetaFullTranslation (g 1 1) • p).val :=
  cubicThetaNormalizedSeries_primaryBottom_complete g hc
    (coordinatesEquiv.symm (g 0 0) 0) (cubicThetaCuspIndex (g 0 0))
    (cubicThetaCuspCoordinates (g 0 0)) p

def cubicThetaNormalizedPrimaryProjection (p : CubicThetaPoint) : ℂ :=
  (star (cubicThetaNormalizedSeriesSection.val p)+
    omega*star (cubicThetaNormalizedSeriesSection.val (cubicThetaFullTranslation omegaE • p))+
    omega^2*star (cubicThetaNormalizedSeriesSection.val (cubicThetaFullTranslation (2*omegaE) • p)))/3

lemma cubicThetaNormalizedSeries_translation_conjugate (b : Eisenstein) (p : CubicThetaPoint) :
    star (cubicThetaNormalizedSeriesSection.val (cubicThetaFullTranslation b • p))=
      star cubicThetaSeriesConstant*((p.val.2^(2/3:ℝ):ℝ):ℂ)+
        cubicThetaNonconstant cubicThetaConjugateCoefficient (p.val.1+(b:ℂ),p.val.2) := by
  rw [cubicThetaNormalizedSeries_conjugate]
  have he : (cubicThetaFullTranslation b • p).val=(p.val.1+(b:ℂ),p.val.2) := by
    rw [cubicThetaFullPointAction_apply,cubicThetaFullTranslation_complex,cubicThetaMobius_translation]
  rw [he]

lemma cubicThetaNormalizedPrimaryProjection_series (p : CubicThetaPoint) :
    cubicThetaNormalizedPrimaryProjection p=
      cubicThetaNonconstant cubicThetaSelectedCoefficient p.val := by
  unfold cubicThetaNormalizedPrimaryProjection
  rw [cubicThetaNormalizedSeries_conjugate,
    cubicThetaNormalizedSeries_translation_conjugate,
    cubicThetaNormalizedSeries_translation_conjugate]
  have he := cubicThetaSelected_projection p.val.1 p.property
  change _=cubicThetaNonconstant cubicThetaSelectedCoefficient (p.val.1,p.val.2)
  rw [he]
  have htwo : ((2*omegaE:Eisenstein):ℂ)=2*omega := by push_cast; rfl
  rw [htwo,show (omegaE:ℂ)=omega from rfl]
  change _=((cubicThetaNonconstant cubicThetaConjugateCoefficient (p.val.1,p.val.2)+
    omega*cubicThetaNonconstant cubicThetaConjugateCoefficient (p.val.1+omega,p.val.2)+
    omega^2*cubicThetaNonconstant cubicThetaConjugateCoefficient (p.val.1+2*omega,p.val.2))/3)
  linear_combination star cubicThetaSeriesConstant*((p.val.2^(2/3:ℝ):ℝ):ℂ)/3*omega_quadratic

lemma cubicThetaFullTranslation_mul_bottom (b : Eisenstein) (g : SL(2,Eisenstein)) :
    (cubicThetaFullTranslation b*g) 1 0=g 1 0 ∧
      (cubicThetaFullTranslation b*g) 1 1=g 1 1 := by
  change ((!![1,b;0,1] : Matrix (Fin 2) (Fin 2) Eisenstein)*g.val) 1 0=g 1 0 ∧
    ((!![1,b;0,1] : Matrix (Fin 2) (Fin 2) Eisenstein)*g.val) 1 1=g 1 1
  constructor <;> simp [Matrix.mul_apply,Fin.sum_univ_two]

def cubicThetaProjectedCuspMatrix (g : SL(2,Eisenstein)) (j : Fin 3) : SL(2,Eisenstein) :=
  cubicThetaFullTranslation ((j.val:Eisenstein)*omegaE)*g

lemma cubicThetaProjectedCuspMatrix_primary (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (j : Fin 3) : primary (cubicThetaProjectedCuspMatrix g j 1 0) := by
  rw [cubicThetaProjectedCuspMatrix,(cubicThetaFullTranslation_mul_bottom _ g).1]
  exact hc

def cubicThetaProjectedCuspMultiplier (g : SL(2,Eisenstein)) (hc : primary (g 1 0))
    (j : Fin 3) : ℂ :=
  cubicThetaKubotaValue (cubicThetaPrimaryBottomPrincipal (cubicThetaProjectedCuspMatrix g j)
    (cubicThetaProjectedCuspMatrix_primary g hc j))

def cubicThetaProjectedCuspType (g : SL(2,Eisenstein)) (j : Fin 3) : ℤ :=
  cubicThetaCuspIndex (cubicThetaProjectedCuspMatrix g j 0 0)

lemma cubicThetaProjectedCusp_identity (g : SL(2,Eisenstein)) (hc : primary (g 1 0))
    (j : Fin 3) (p : CubicThetaPoint) :
    cubicThetaNormalizedSeriesSection.val
      (cubicThetaFullTranslation ((j.val:Eisenstein)*omegaE) • (g • p))=
      cubicThetaProjectedCuspMultiplier g hc j*
        cubicThetaCuspExpansion (cubicThetaProjectedCuspType g j)
          (cubicThetaFullTranslation (g 1 1) • p).val := by
  rw [←mul_smul]
  have he := cubicThetaNormalizedSeries_primaryBottom_index (cubicThetaProjectedCuspMatrix g j)
    (cubicThetaProjectedCuspMatrix_primary g hc j) p
  rw [show cubicThetaProjectedCuspMatrix g j 1 1=g 1 1 from
    (cubicThetaFullTranslation_mul_bottom _ g).2] at he
  exact he

theorem cubicThetaNormalizedPrimaryProjection_cusps (g : SL(2,Eisenstein))
    (hc : primary (g 1 0)) (p : CubicThetaPoint) :
    cubicThetaNonconstant cubicThetaSelectedCoefficient (g • p).val=
      (∑ j : Fin 3, omega^j.val*star (cubicThetaProjectedCuspMultiplier g hc j*
        cubicThetaCuspExpansion (cubicThetaProjectedCuspType g j)
          (cubicThetaFullTranslation (g 1 1) • p).val))/3 := by
  rw [←cubicThetaNormalizedPrimaryProjection_series]
  have hs : (∑ j : Fin 3, omega^j.val*star (cubicThetaNormalizedSeriesSection.val
      (cubicThetaFullTranslation ((j.val:Eisenstein)*omegaE) • (g • p))))/3=
      cubicThetaNormalizedPrimaryProjection (g • p) := by
    rw [Fin.sum_univ_three]
    have hz : cubicThetaFullTranslation 0=1 := by
      apply Subtype.ext
      apply Matrix.ext
      intro i j
      fin_cases i <;> fin_cases j <;> rfl
    simp only [Fin.val_zero,Fin.val_one,Fin.val_two,Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat,
      zero_mul,one_mul,pow_zero,pow_one,hz,one_smul,cubicThetaNormalizedPrimaryProjection]
  rw [←hs]
  simp_rw [cubicThetaProjectedCusp_identity g hc]

end CubicFirstMoment

end

end OAI

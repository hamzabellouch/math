import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPointC1Inversion
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaInversionFiniteEnergy

namespace OAI

/-! The C1 trace is the literal cubed-prime Hecke operator, and its
three geometric pullbacks have the required finite gradient integrals. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

def cubicThetaPointC1Hecke {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPointC1) : cubicThetaPointC1 :=
  cubicThetaPointC1Trace hp (cubicThetaPointC1Pullback
    (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero)) F)

lemma cubicThetaPointC1Hecke_section {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2}) :
    cubicThetaPointC1Hecke hp (cubicThetaSectionPointC1 F hF)=
      cubicThetaSectionPointC1 (cubicThetaPrimeCubeHecke hp F) (cubicThetaPrimeCubeHecke_c1 hp F hF) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  rw [show (cubicThetaPointC1Hecke hp (cubicThetaSectionPointC1 F hF)).val x=
    (cubicThetaPointC1Trace hp (cubicThetaPointC1Pullback
      (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero)) (cubicThetaSectionPointC1 F hF))).val x from rfl,
    cubicThetaPointC1Trace_apply]
  exact (cubicThetaPrimeCubeHecke_apply hp F x).symm

lemma cubicThetaPointC1_dilation_atkin {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPointC1) :
    cubicThetaPointC1Pullback (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero)) F=
      cubicThetaPointC1Pullback (cubicThetaPrimeCubeAtkinMatrix hp)
        (cubicThetaPointC1Pullback (cubicThetaFullComplex cubicThetaFullInversion) F) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  exact congrArg F.val (cubicThetaPrimeCubeDilation_inversion_atkin hp x).symm

lemma cubicThetaPointC1_atkin_dilation {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPointC1) :
    cubicThetaPointC1Pullback (cubicThetaPrimeCubeAtkinMatrix hp) F=
      cubicThetaPointC1Pullback (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero))
        (cubicThetaPointC1Pullback (cubicThetaFullComplex cubicThetaFullInversion) F) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  exact congrArg F.val (mul_smul (β:=CubicThetaPoint) _ _ x)

lemma cubicThetaPointC1_section_cover_integrable {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaFiniteEnergySections) :
    IntegrableOn (fun x => ‖cubicThetaPointC1Gradient x (cubicThetaSectionPointC1 F.val F.property.1)‖^2)
      (cubicThetaPrimeCubeCoverDomain p) cubicThetaPointMeasure := by
  simp_rw [cubicThetaSectionPointC1_gradient,cubicThetaSectionGradient_norm_sq]
  exact cubicThetaPrimeCubeInvariant_integrable hp (cubicThetaPrimeCubeFinite_energy_domain F)
    (cubicThetaC1Energy_invariant F.val F.property.1)

lemma cubicThetaPointC1_dilation_integrable {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaFiniteEnergySections) :
    IntegrableOn (fun x => ‖cubicThetaPointC1Gradient x
      (cubicThetaPointC1Pullback (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero))
        (cubicThetaSectionPointC1 F.val F.property.1))‖^2)
      (cubicThetaPrimeCubeCoverDomain p) cubicThetaPointMeasure := by
  simp_rw [cubicThetaPointC1Pullback_gradient_norm,cubicThetaSectionPointC1_gradient,
    cubicThetaSectionGradient_norm_sq]
  exact cubicThetaPrimeCubeScalarDilation_integrable hp (cubicThetaPrimeCubeFinite_energy_domain F)
    (cubicThetaC1Energy_invariant F.val F.property.1)

lemma cubicThetaPointC1_atkin_integrable {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaFiniteEnergySections) :
    IntegrableOn (fun x => ‖cubicThetaPointC1Gradient x
      (cubicThetaPointC1Pullback (cubicThetaPrimeCubeAtkinMatrix hp)
        (cubicThetaSectionPointC1 F.val F.property.1))‖^2)
      (cubicThetaPrimeCubeCoverDomain p) cubicThetaPointMeasure := by
  rw [cubicThetaPointC1_atkin_dilation]
  rw [←cubicThetaInversionPointC1]
  exact cubicThetaPointC1_dilation_integrable hp (cubicThetaInversionFinite F)

end CubicFirstMoment

end

end OAI

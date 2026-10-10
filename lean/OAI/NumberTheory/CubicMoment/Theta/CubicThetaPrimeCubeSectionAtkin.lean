import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeAtkinIntegral
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaInversionEnergyInvolution

namespace OAI

/-! Restriction and Atkin pullback of actual cubed-prime sections. The
original dilation is exactly Atkin pullback after the global inversion. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaPrimeCubeSectionRestrict {p : Eisenstein} (F : CubicThetaSection) :
    cubicThetaPrimeCubeSections p :=
  ⟨F.val,fun g x => F.property g.val x⟩

def cubicThetaPrimeCubeAtkinSection {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeCubeSections p) : cubicThetaPrimeCubeSections p :=
  ⟨⟨fun x => F.val (cubicThetaPrimeCubeAtkinMatrix hp • x),
    F.val.continuous.comp (continuous_const_smul _)⟩,by
    intro g x
    change F.val (cubicThetaPrimeCubeAtkinMatrix hp • (g.val • x))=
      cubicThetaKubotaValue g.val*F.val (cubicThetaPrimeCubeAtkinMatrix hp • x)
    have ht := cubicThetaPrimeCubeAtkinPoint_intertwines hp g x
    change cubicThetaPrimeCubeAtkinMatrix hp • (g.val • x)=
      (cubicThetaPrimeCubeAtkinConjugate hp g).val • (cubicThetaPrimeCubeAtkinMatrix hp • x) at ht
    rw [ht,F.property,cubicThetaPrimeCubeAtkinConjugate_kubota]⟩

theorem cubicThetaPrimeCubeDilation_eq_atkin {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) :
    cubicThetaPrimeCubeDilationSection hp F=
      cubicThetaPrimeCubeAtkinSection hp (cubicThetaPrimeCubeSectionRestrict (cubicThetaInversionSection F)) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  change F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • x)=
    F.val (cubicThetaFullInversion • (cubicThetaPrimeCubeAtkinMatrix hp • x))
  rw [cubicThetaPrimeCubeAtkinMatrix,mul_smul]
  change F.val (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • x)=
    F.val (cubicThetaFullInversion • (cubicThetaFullInversion •
      (cubicThetaPrimeDilation (pow_ne_zero 3 hp.2.ne_zero) • x)))
  rw [cubicThetaFullInversion_involutive]

end CubicFirstMoment

end

end OAI

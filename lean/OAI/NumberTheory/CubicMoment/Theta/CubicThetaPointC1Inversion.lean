import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPointC1TraceIntegral
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeHeckePairing

namespace OAI

/-! Global inversion for the actual gradient pairing. -/
noncomputable section
open Set MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaPointC1Inversion_covariance (F : cubicThetaPointC1)
    (hF : ∀ (g : cubicThetaPrincipalGroup) x,F.val (g • x)=cubicThetaKubotaValue g*F.val x)
    (g : cubicThetaPrincipalGroup) (x : CubicThetaPoint) :
    (cubicThetaPointC1Pullback (cubicThetaFullComplex cubicThetaFullInversion) F).val (g • x)=
      cubicThetaKubotaValue g*
        (cubicThetaPointC1Pullback (cubicThetaFullComplex cubicThetaFullInversion) F).val x := by
  change F.val (cubicThetaFullInversion • (g • x))=
    cubicThetaKubotaValue g*F.val (cubicThetaFullInversion • x)
  rw [cubicThetaInversion_intertwine,hF,cubicThetaInversionConjugate_character]

theorem cubicThetaPointC1Inversion_gradient_pairing (F G : cubicThetaPointC1)
    (hF : ∀ (g : cubicThetaPrincipalGroup) x,F.val (g • x)=cubicThetaKubotaValue g*F.val x)
    (hG : ∀ (g : cubicThetaPrincipalGroup) x,G.val (g • x)=cubicThetaKubotaValue g*G.val x) :
    (∫ x in cubicThetaFundamentalDomain,
      inner ℂ (cubicThetaPointC1Gradient x G)
        (cubicThetaPointC1Gradient x (cubicThetaPointC1Pullback
          (cubicThetaFullComplex cubicThetaFullInversion) F)) ∂cubicThetaPointMeasure)=
    ∫ x in cubicThetaFundamentalDomain,
      inner ℂ (cubicThetaPointC1Gradient x (cubicThetaPointC1Pullback
        (cubicThetaFullComplex cubicThetaFullInversion) G))
        (cubicThetaPointC1Gradient x F) ∂cubicThetaPointMeasure := by
  let S := cubicThetaFullComplex cubicThetaFullInversion
  have hi (g : cubicThetaPrincipalGroup) (x : CubicThetaPoint) :
      inner ℂ (cubicThetaPointC1Gradient (g • x) (cubicThetaPointC1Pullback S G))
        (cubicThetaPointC1Gradient (g • x) F)=
      inner ℂ (cubicThetaPointC1Gradient x (cubicThetaPointC1Pullback S G))
        (cubicThetaPointC1Gradient x F) :=
    cubicThetaPointC1Pair_covariance F (cubicThetaPointC1Pullback S G) g (hF g)
      (cubicThetaPointC1Inversion_covariance G hG g) x
  have he := cubicThetaComplexInversion_integral
    (f:=fun x => inner ℂ (cubicThetaPointC1Gradient x (cubicThetaPointC1Pullback S G))
      (cubicThetaPointC1Gradient x F)) hi
  have hGG : cubicThetaPointC1Pullback S (cubicThetaPointC1Pullback S G)=G := by
    apply Subtype.ext
    apply ContinuousMap.ext
    intro x
    exact congrArg G.val (cubicThetaFullInversion_involutive x)
  have ht (x : CubicThetaPoint) :
      inner ℂ (cubicThetaPointC1Gradient (cubicThetaFullInversion • x) (cubicThetaPointC1Pullback S G))
        (cubicThetaPointC1Gradient (cubicThetaFullInversion • x) F)=
      inner ℂ (cubicThetaPointC1Gradient x G)
        (cubicThetaPointC1Gradient x (cubicThetaPointC1Pullback S F)) := by
    have hh := cubicThetaPointC1Pullback_gradient_pair S (cubicThetaPointC1Pullback S G) F x
    rw [hGG] at hh
    exact hh.symm
  dsimp [S] at he ht
  simpa only [ht] using he

end CubicFirstMoment

end

end OAI

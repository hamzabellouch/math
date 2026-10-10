import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPointC1
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeCubeHeckeEnergyOperator

namespace OAI

/-! The auxiliary C1 coordinates retain the literal automorphic section
and its previously constructed gradient. -/
noncomputable section
namespace CubicFirstMoment

def cubicThetaSectionPointC1 (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2}) :
    cubicThetaPointC1 := ⟨F.val,hF⟩

lemma cubicThetaSectionPointC1_gradient (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (x : CubicThetaPoint) :
    cubicThetaPointC1Gradient x (cubicThetaSectionPointC1 F hF)=cubicThetaSectionGradient F x := by
  ext i
  simp only [cubicThetaPointC1Gradient,cubicThetaSectionPointC1,cubicThetaTangentValues,
    cubicThetaSectionGradient,cubicThetaSectionDifferential,ContinuousLinearMap.comp_apply]
  rfl

lemma cubicThetaSectionPointC1_automorphy (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {y : ℂ × ℝ | 0<y.2})
    (g : cubicThetaPrincipalGroup) :
    cubicThetaPointC1Pullback (cubicThetaPrincipalComplex g) (cubicThetaSectionPointC1 F hF)=
      cubicThetaKubotaValue g • cubicThetaSectionPointC1 F hF := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  exact F.property g x

lemma cubicThetaPointC1Gradient_continuous (F : cubicThetaPointC1) :
    Continuous (fun x => cubicThetaPointC1Gradient x F) := by
  have hd : Continuous (fun x : CubicThetaPoint =>
      fderiv ℝ (cubicThetaPointFunction F.val) x.val) :=
    (F.property.continuousOn_fderiv_of_isOpen (isOpen_lt continuous_const continuous_snd)
      (by norm_num)).comp_continuous continuous_subtype_val (fun x => x.property)
  change Continuous (fun x : CubicThetaPoint => (x.val.2:ℂ) •
    cubicThetaTangentValues (fderiv ℝ (cubicThetaPointFunction F.val) x.val))
  apply Continuous.smul (Complex.continuous_ofReal.comp (continuous_snd.comp continuous_subtype_val))
  apply (PiLp.continuous_toLp _ _).comp
  apply continuous_pi
  intro i
  exact hd.clm_apply continuous_const

end CubicFirstMoment

end

end OAI

import OAI.NumberTheory.CubicMoment.Theta.CubicThetaGlobalEnergy

namespace OAI

/-! The value and differential of compact C1 sections define genuine
L2 data. Smooth approximation will place these data in the energy graph. -/
noncomputable section
open Set Filter Topology MeasureTheory
namespace CubicFirstMoment

lemma cubicThetaC1Differential_automorphy (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {p : ℂ × ℝ | 0<p.2})
    (g : cubicThetaPrincipalGroup) (p : CubicThetaPoint) :
    (cubicThetaSectionDifferential F (g • p)).comp
        (cubicThetaTangentDerivative (cubicThetaPrincipalComplex g) p.val)=
      cubicThetaKubotaValue g • cubicThetaSectionDifferential F p := by
  have hd {y : ℂ × ℝ} (hy : 0<y.2) : DifferentiableAt ℝ (cubicThetaSectionFunction F) y :=
    (hF.contDiffAt
      ((isOpen_lt continuous_const continuous_snd).mem_nhds hy)).differentiableAt (by norm_num)
  have hm := cubicThetaMobius_height_pos (cubicThetaPrincipalComplex g) p.property
  have hM := (cubicThetaMobius_contDiffAt (cubicThetaPrincipalComplex g)
    p.property).differentiableAt (by simp)
  have hF := hd p.property
  have hG := hd hm
  have he : (fun y => cubicThetaSectionFunction F
      (cubicThetaMobius (cubicThetaPrincipalComplex g) y))=ᶠ[𝓝 p.val]
      (fun y => cubicThetaKubotaValue g*cubicThetaSectionFunction F y) := by
    filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds p.property] with y hy
    exact cubicThetaSectionFunction_automorphy F g hy
  have hd' := ((hG.hasFDerivAt.comp p.val hM.hasFDerivAt).congr_of_eventuallyEq he.symm).unique
    (hF.hasFDerivAt.const_mul (cubicThetaKubotaValue g))
  ext u
  have hv := congrArg (fun L : (ℂ × ℝ) →L[ℝ] ℂ => L (cubicThetaTangentCoordinates u)) hd'
  have hgp : (g • p).val=cubicThetaMobius (cubicThetaPrincipalComplex g) p.val := rfl
  simpa only [cubicThetaSectionDifferential,cubicThetaTangentDerivative,hgp,
    ContinuousLinearMap.comp_apply,smul_apply,
    ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.apply_symm_apply] using hv

lemma cubicThetaC1Energy_invariant (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {p : ℂ × ℝ | 0<p.2})
    (g : cubicThetaPrincipalGroup) (p : CubicThetaPoint) :
    cubicThetaSectionEnergy F (g • p)=
      cubicThetaSectionEnergy F p := by
  have he := congrArg cubicThetaTangentEnergy (cubicThetaC1Differential_automorphy F hF g p)
  rw [cubicThetaTangentEnergy_derivative _ _ p.property,
    cubicThetaTangentEnergy_complex_smul,cubicThetaKubotaValue_norm,one_pow,one_mul] at he
  change (cubicThetaMobius (cubicThetaPrincipalComplex g) p.val).2^2*
    cubicThetaTangentEnergy (cubicThetaSectionDifferential F (g • p))=
    p.val.2^2*cubicThetaTangentEnergy (cubicThetaSectionDifferential F p)
  calc
    _ = p.val.2^2*(((cubicThetaMobius (cubicThetaPrincipalComplex g) p.val).2/p.val.2)^2*
        cubicThetaTangentEnergy (cubicThetaSectionDifferential F (g • p))) := by
      field_simp [p.property.ne']
    _ = _ := by rw [he]

lemma cubicThetaC1Energy_continuous (F : CubicThetaSection)
    (hF : ContDiffOn ℝ 1 (cubicThetaSectionFunction F) {p : ℂ × ℝ | 0<p.2}) :
    Continuous (cubicThetaSectionEnergy F) := by
  have hd : Continuous (fun p : CubicThetaPoint =>
      fderiv ℝ (cubicThetaSectionFunction F) p.val) :=
    (hF.continuousOn_fderiv_of_isOpen
      (isOpen_lt continuous_const continuous_snd) (by norm_num)).comp_continuous
      continuous_subtype_val (fun p => p.property)
  unfold cubicThetaSectionEnergy cubicThetaTangentEnergy cubicThetaSectionDifferential
  apply ((continuous_snd.comp continuous_subtype_val).pow 2).mul
  apply continuous_finsetSum
  intro i hi
  exact ((hd.clm_apply continuous_const).norm).pow 2


end CubicFirstMoment

end

end OAI

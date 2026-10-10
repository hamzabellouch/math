import OAI.NumberTheory.CubicMoment.Theta.CubicThetaTangentEnergy
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSmoothTests

namespace OAI

/-! Differentiate the actual cubic automorphy law. Its unit multiplier
and the conformal tangent map imply invariance of hyperbolic energy. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff MatrixGroups
namespace CubicFirstMoment

def cubicThetaSectionFunction (F : CubicThetaSection) (y : ℂ × ℝ) : ℂ :=
  F.val (cubicThetaPointInclusion.symm y)

lemma cubicThetaSectionFunction_apply (F : CubicThetaSection) {y : ℂ × ℝ}
    (hy : 0<y.2) : cubicThetaSectionFunction F y=F.val ⟨y,hy⟩ := by
  apply congrArg F.val
  apply Subtype.ext
  have hy' : y∈cubicThetaPointInclusion.target := by
    rwa [cubicThetaPointInclusion_target]
  have h := cubicThetaPointInclusion.right_inv hy'
  exact h

lemma cubicThetaSectionFunction_differentiable (F : cubicThetaSmoothTests)
    {y : ℂ × ℝ} (hy : 0<y.2) : DifferentiableAt ℝ (cubicThetaSectionFunction F) y :=
  (F.property.1.contDiffAt ((isOpen_lt continuous_const continuous_snd).mem_nhds hy)).differentiableAt
    (by simp)

def cubicThetaSectionDifferential (F : CubicThetaSection) (p : CubicThetaPoint) :
    CubicThetaTangent →L[ℝ] ℂ :=
  (fderiv ℝ (cubicThetaSectionFunction F) p.val).comp
    cubicThetaTangentCoordinates.toContinuousLinearMap

lemma cubicThetaSectionFunction_automorphy (F : CubicThetaSection)
    (g : cubicThetaPrincipalGroup) {y : ℂ × ℝ} (hy : 0<y.2) :
    cubicThetaSectionFunction F (cubicThetaMobius (cubicThetaPrincipalComplex g) y)=
      cubicThetaKubotaValue g*cubicThetaSectionFunction F y := by
  unfold cubicThetaSectionFunction
  rw [cubicThetaPointInclusion_action g hy,F.property]

lemma cubicThetaSectionDifferential_automorphy (F : cubicThetaSmoothTests)
    (g : cubicThetaPrincipalGroup) (p : CubicThetaPoint) :
    (cubicThetaSectionDifferential F (g • p)).comp
        (cubicThetaTangentDerivative (cubicThetaPrincipalComplex g) p.val)=
      cubicThetaKubotaValue g • cubicThetaSectionDifferential F p := by
  have hm := cubicThetaMobius_height_pos (cubicThetaPrincipalComplex g) p.property
  have hM := (cubicThetaMobius_contDiffAt (cubicThetaPrincipalComplex g)
    p.property).differentiableAt (by simp)
  have hF := cubicThetaSectionFunction_differentiable F p.property
  have hG := cubicThetaSectionFunction_differentiable F hm
  have he : (fun y => cubicThetaSectionFunction F
      (cubicThetaMobius (cubicThetaPrincipalComplex g) y)) =ᶠ[𝓝 p.val]
        (fun y => cubicThetaKubotaValue g*cubicThetaSectionFunction F y) := by
    filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds p.property] with y hy
    exact cubicThetaSectionFunction_automorphy F g hy
  have hd := ((hG.hasFDerivAt.comp p.val hM.hasFDerivAt).congr_of_eventuallyEq he.symm).unique
    (hF.hasFDerivAt.const_mul (cubicThetaKubotaValue g))
  ext u
  have hv := congrArg (fun L : (ℂ × ℝ) →L[ℝ] ℂ => L (cubicThetaTangentCoordinates u)) hd
  have hgp : (g • p).val=cubicThetaMobius (cubicThetaPrincipalComplex g) p.val := rfl
  simpa only [cubicThetaSectionDifferential,cubicThetaTangentDerivative,hgp,
    ContinuousLinearMap.comp_apply,smul_apply,
    ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.apply_symm_apply] using hv

def cubicThetaSectionEnergy (F : CubicThetaSection) (p : CubicThetaPoint) : ℝ :=
  p.val.2^2*cubicThetaTangentEnergy (cubicThetaSectionDifferential F p)

lemma cubicThetaSectionEnergy_invariant (F : cubicThetaSmoothTests)
    (g : cubicThetaPrincipalGroup) (p : CubicThetaPoint) :
    cubicThetaSectionEnergy F (g • p)=cubicThetaSectionEnergy F p := by
  have he := congrArg cubicThetaTangentEnergy (cubicThetaSectionDifferential_automorphy F g p)
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

end CubicFirstMoment

end

end OAI

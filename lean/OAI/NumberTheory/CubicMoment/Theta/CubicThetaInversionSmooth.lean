import OAI.NumberTheory.CubicMoment.Theta.CubicThetaInversionCharacter
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaIntegralQuotient
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSectionDifferential

namespace OAI

/-! Inversion acts on the actual compact smooth sections. Both their
pointwise differential and quotient norm are transported geometrically. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace CubicFirstMoment

lemma cubicThetaInversionSection_norm (F : CubicThetaSection) (q : CubicThetaQuotient) :
    cubicThetaSectionNorm (cubicThetaInversionSection F) q=
      cubicThetaSectionNorm F (cubicThetaIntegralQuotientMap cubicThetaFullInversion q) := by
  obtain ⟨p,rfl⟩ := cubicThetaQuotientMap_surjective q
  rw [cubicThetaSectionNorm_apply,cubicThetaIntegralQuotientMap_apply,cubicThetaSectionNorm_apply]
  rfl

lemma cubicThetaInversionSection_function (F : CubicThetaSection)
    {y : ℂ × ℝ} (hy : 0<y.2) :
    cubicThetaSectionFunction (cubicThetaInversionSection F) y=
      cubicThetaSectionFunction F (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) y) := by
  rw [cubicThetaSectionFunction_apply _ hy,cubicThetaSectionFunction_apply _
    (cubicThetaMobius_height_pos _ hy)]
  rfl

lemma cubicThetaInversionSection_smooth (F : cubicThetaSmoothTests) :
    ContDiffOn ℝ ∞ (cubicThetaSectionFunction (cubicThetaInversionSection F)) {y | 0<y.2} := by
  have hM : ContDiffOn ℝ ∞ (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion))
      {y : ℂ × ℝ | 0<y.2} := fun _ hy => (cubicThetaMobius_contDiffAt _ hy).contDiffWithinAt
  have hcomp := F.property.1.comp hM (fun _ hy => cubicThetaMobius_height_pos _ hy)
  exact hcomp.congr (fun _ hy => cubicThetaInversionSection_function F hy)

def cubicThetaInversionSmooth (F : cubicThetaSmoothTests) : cubicThetaSmoothTests :=
  ⟨cubicThetaInversionSection F,cubicThetaInversionSection_smooth F,by
    have h := F.property.2.comp_homeomorph
      (cubicThetaIntegralQuotientHomeomorph cubicThetaFullInversion)
    change HasCompactSupport (fun q => cubicThetaSectionNorm F
      (cubicThetaIntegralQuotientMap cubicThetaFullInversion q)) at h
    simpa only [←cubicThetaInversionSection_norm] using h⟩

lemma cubicThetaInversionSection_differential (F : cubicThetaSmoothTests) (p : CubicThetaPoint) :
    cubicThetaSectionDifferential (cubicThetaInversionSection F) p=
      (cubicThetaSectionDifferential F (cubicThetaFullInversion • p)).comp
        (cubicThetaTangentDerivative (cubicThetaFullComplex cubicThetaFullInversion) p.val) := by
  have hM := (cubicThetaMobius_contDiffAt
    (cubicThetaFullComplex cubicThetaFullInversion) p.property).differentiableAt (by simp)
  have hF := cubicThetaSectionFunction_differentiable F
    (cubicThetaMobius_height_pos (cubicThetaFullComplex cubicThetaFullInversion) p.property)
  have hI := cubicThetaSectionFunction_differentiable (cubicThetaInversionSmooth F) p.property
  change DifferentiableAt ℝ (cubicThetaSectionFunction (cubicThetaInversionSection F)) p.val at hI
  have he : (fun y => cubicThetaSectionFunction F
      (cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) y))=ᶠ[𝓝 p.val]
      cubicThetaSectionFunction (cubicThetaInversionSection F) := by
    filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds p.property] with y hy
    exact (cubicThetaInversionSection_function F hy).symm
  have hd := ((hF.hasFDerivAt.comp p.val hM.hasFDerivAt).congr_of_eventuallyEq he.symm).unique
    hI.hasFDerivAt
  ext u
  have hv := congrArg (fun L : (ℂ × ℝ) →L[ℝ] ℂ => L (cubicThetaTangentCoordinates u)) hd
  have hgp : (cubicThetaFullInversion • p).val=
      cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) p.val := rfl
  simpa only [cubicThetaSectionDifferential,cubicThetaTangentDerivative,
    ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply,hgp] using hv.symm

lemma cubicThetaInversionSection_energy (F : cubicThetaSmoothTests) (p : CubicThetaPoint) :
    cubicThetaSectionEnergy (cubicThetaInversionSection F) p=
      cubicThetaSectionEnergy F (cubicThetaFullInversion • p) := by
  rw [cubicThetaSectionEnergy,cubicThetaInversionSection_differential,
    cubicThetaTangentEnergy_derivative _ _ p.property]
  unfold cubicThetaSectionEnergy
  have hgp : (cubicThetaFullInversion • p).val=
      cubicThetaMobius (cubicThetaFullComplex cubicThetaFullInversion) p.val := rfl
  rw [hgp]
  field_simp [p.property.ne']

end CubicFirstMoment

end

end OAI

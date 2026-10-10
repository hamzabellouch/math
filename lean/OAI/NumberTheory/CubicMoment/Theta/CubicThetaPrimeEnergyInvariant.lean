import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeSectionEnergy

namespace OAI

/-! The first-derivative energy of a C1 section descends to the actual
prime quotient. Its invariance is obtained by differentiating automorphy. -/
noncomputable section
open Set Filter Topology
namespace CubicFirstMoment

lemma cubicThetaPrimeSectionFunction_automorphy {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeSections hp) (g : cubicThetaPrimeCoverGroup hp)
    {y : ℂ × ℝ} (hy : 0<y.2) :
    cubicThetaPrimeSectionFunction hp F (cubicThetaMobius (cubicThetaPrincipalComplex g.val) y)=
      cubicThetaKubotaValue g.val*cubicThetaPrimeSectionFunction hp F y := by
  rw [cubicThetaPrimeSectionFunction_apply hp _ (cubicThetaMobius_height_pos _ hy),
    cubicThetaPrimeSectionFunction_apply hp _ hy]
  exact cubicThetaPrimeSection_property hp F g ⟨y,hy⟩

def cubicThetaPrimeSectionDifferential {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeSections hp) (x : CubicThetaPoint) : CubicThetaTangent →L[ℝ] ℂ :=
  (fderiv ℝ (cubicThetaPrimeSectionFunction hp F) x.val).comp
    cubicThetaTangentCoordinates.toContinuousLinearMap

lemma cubicThetaPrimeSectionDifferential_automorphy {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeSections hp)
    (hF : ContDiffOn ℝ 1 (cubicThetaPrimeSectionFunction hp F) {y : ℂ × ℝ | 0<y.2})
    (g : cubicThetaPrimeCoverGroup hp) (x : CubicThetaPoint) :
    (cubicThetaPrimeSectionDifferential hp F (g • x)).comp
        (cubicThetaTangentDerivative (cubicThetaPrincipalComplex g.val) x.val)=
      cubicThetaKubotaValue g.val • cubicThetaPrimeSectionDifferential hp F x := by
  have hd {y : ℂ × ℝ} (hy : 0<y.2) : DifferentiableAt ℝ (cubicThetaPrimeSectionFunction hp F) y :=
    (hF.contDiffAt ((isOpen_lt continuous_const continuous_snd).mem_nhds hy)).differentiableAt
      (by norm_num)
  have hm := cubicThetaMobius_height_pos (cubicThetaPrincipalComplex g.val) x.property
  have hM := (cubicThetaMobius_contDiffAt (cubicThetaPrincipalComplex g.val)
    x.property).differentiableAt (by simp)
  have he : (fun y => cubicThetaPrimeSectionFunction hp F
      (cubicThetaMobius (cubicThetaPrincipalComplex g.val) y))=ᶠ[𝓝 x.val]
      (fun y => cubicThetaKubotaValue g.val*cubicThetaPrimeSectionFunction hp F y) := by
    filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds x.property] with y hy
    exact cubicThetaPrimeSectionFunction_automorphy hp F g hy
  have he' := (((hd hm).hasFDerivAt.comp x.val hM.hasFDerivAt).congr_of_eventuallyEq he.symm).unique
    ((hd x.property).hasFDerivAt.const_mul (cubicThetaKubotaValue g.val))
  ext u
  have hv := congrArg (fun L : (ℂ × ℝ) →L[ℝ] ℂ => L (cubicThetaTangentCoordinates u)) he'
  have hx : (g • x).val=cubicThetaMobius (cubicThetaPrincipalComplex g.val) x.val := rfl
  simpa only [cubicThetaPrimeSectionDifferential,cubicThetaTangentDerivative,hx,
    ContinuousLinearMap.comp_apply,smul_apply,ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply] using hv

theorem cubicThetaPrimeSectionEnergy_invariant {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeSections hp)
    (hF : ContDiffOn ℝ 1 (cubicThetaPrimeSectionFunction hp F) {y : ℂ × ℝ | 0<y.2})
    (g : cubicThetaPrimeCoverGroup hp) (x : CubicThetaPoint) :
    cubicThetaPrimeSectionEnergy hp F (g • x)=cubicThetaPrimeSectionEnergy hp F x := by
  have he := congrArg cubicThetaTangentEnergy
    (cubicThetaPrimeSectionDifferential_automorphy hp F hF g x)
  rw [cubicThetaTangentEnergy_derivative _ _ x.property,
    cubicThetaTangentEnergy_complex_smul,cubicThetaKubotaValue_norm,one_pow,one_mul] at he
  change (cubicThetaMobius (cubicThetaPrincipalComplex g.val) x.val).2^2*
      cubicThetaTangentEnergy (cubicThetaPrimeSectionDifferential hp F (g • x))=
    x.val.2^2*cubicThetaTangentEnergy (cubicThetaPrimeSectionDifferential hp F x)
  calc
    _ = x.val.2^2*(((cubicThetaMobius (cubicThetaPrincipalComplex g.val) x.val).2/x.val.2)^2*
        cubicThetaTangentEnergy (cubicThetaPrimeSectionDifferential hp F (g • x))) := by
      field_simp [x.property.ne']
    _ = _ := by rw [he]

lemma cubicThetaPrimeSectionEnergy_continuous {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeSections hp)
    (hF : ContDiffOn ℝ 1 (cubicThetaPrimeSectionFunction hp F) {y : ℂ × ℝ | 0<y.2}) :
    Continuous (cubicThetaPrimeSectionEnergy hp F) := by
  have hd : Continuous (fun x : CubicThetaPoint =>
      fderiv ℝ (cubicThetaPrimeSectionFunction hp F) x.val) :=
    (hF.continuousOn_fderiv_of_isOpen (isOpen_lt continuous_const continuous_snd)
      (by norm_num)).comp_continuous continuous_subtype_val (fun x => x.property)
  unfold cubicThetaPrimeSectionEnergy cubicThetaFunctionEnergy cubicThetaTangentEnergy
  apply ((continuous_snd.comp continuous_subtype_val).pow 2).mul
  apply continuous_finsetSum
  intro i _hi
  exact ((hd.clm_apply continuous_const).norm).pow 2

end CubicFirstMoment

end

end OAI

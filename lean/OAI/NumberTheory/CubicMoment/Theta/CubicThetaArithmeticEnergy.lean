import OAI.NumberTheory.CubicMoment.Theta.CubicThetaJointRegularity
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaArithmeticSection
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaQuotientEnergy

namespace OAI

/-! The actual arithmetic remainder has a continuous invariant
Dirichlet energy density. No energy membership is assumed here. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff MatrixGroups
namespace CubicFirstMoment

lemma cubicThetaArithmeticRemainder_contDiffOn_one {s : ℂ} (hs : 2<s.re) :
    ContDiffOn ℝ 1 (fun p => cubicThetaArithmeticRemainder p s)
      {p : ℂ × ℝ | 0<p.2} := by
  intro p hp
  exact ((cubicThetaEisenstein_contDiffAt_one hs hp).sub
    (((cubicThetaIncomingEisenstein_contDiffOn s).contDiffAt
      ((isOpen_lt continuous_const continuous_snd).mem_nhds hp)).of_le (by norm_num))).contDiffWithinAt

lemma cubicThetaArithmeticSectionFunction_contDiffOn_one {s : ℂ} (hs : 2<s.re) :
    ContDiffOn ℝ 1 (cubicThetaSectionFunction (cubicThetaArithmeticSection s hs))
      {p : ℂ × ℝ | 0<p.2} := by
  apply (cubicThetaArithmeticRemainder_contDiffOn_one hs).congr
  intro p hp
  rw [cubicThetaSectionFunction_apply _ hp]
  rfl

lemma cubicThetaArithmeticDifferential_automorphy {s : ℂ} (hs : 2<s.re)
    (g : cubicThetaPrincipalGroup) (p : CubicThetaPoint) :
    (cubicThetaSectionDifferential (cubicThetaArithmeticSection s hs) (g • p)).comp
        (cubicThetaTangentDerivative (cubicThetaPrincipalComplex g) p.val)=
      cubicThetaKubotaValue g • cubicThetaSectionDifferential (cubicThetaArithmeticSection s hs) p := by
  let F := cubicThetaArithmeticSection s hs
  have hd {y : ℂ × ℝ} (hy : 0<y.2) : DifferentiableAt ℝ (cubicThetaSectionFunction F) y :=
    ((cubicThetaArithmeticSectionFunction_contDiffOn_one hs).contDiffAt
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

lemma cubicThetaArithmeticEnergy_invariant {s : ℂ} (hs : 2<s.re)
    (g : cubicThetaPrincipalGroup) (p : CubicThetaPoint) :
    cubicThetaSectionEnergy (cubicThetaArithmeticSection s hs) (g • p)=
      cubicThetaSectionEnergy (cubicThetaArithmeticSection s hs) p := by
  have he := congrArg cubicThetaTangentEnergy (cubicThetaArithmeticDifferential_automorphy hs g p)
  rw [cubicThetaTangentEnergy_derivative _ _ p.property,
    cubicThetaTangentEnergy_complex_smul,cubicThetaKubotaValue_norm,one_pow,one_mul] at he
  change (cubicThetaMobius (cubicThetaPrincipalComplex g) p.val).2^2*
    cubicThetaTangentEnergy (cubicThetaSectionDifferential (cubicThetaArithmeticSection s hs) (g • p))=
    p.val.2^2*cubicThetaTangentEnergy (cubicThetaSectionDifferential (cubicThetaArithmeticSection s hs) p)
  calc
    _ = p.val.2^2*(((cubicThetaMobius (cubicThetaPrincipalComplex g) p.val).2/p.val.2)^2*
        cubicThetaTangentEnergy (cubicThetaSectionDifferential (cubicThetaArithmeticSection s hs) (g • p))) := by
      field_simp [p.property.ne']
    _ = _ := by rw [he]

lemma cubicThetaArithmeticEnergy_continuous {s : ℂ} (hs : 2<s.re) :
    Continuous (cubicThetaSectionEnergy (cubicThetaArithmeticSection s hs)) := by
  have hd : Continuous (fun p : CubicThetaPoint =>
      fderiv ℝ (cubicThetaSectionFunction (cubicThetaArithmeticSection s hs)) p.val) :=
    ((cubicThetaArithmeticSectionFunction_contDiffOn_one hs).continuousOn_fderiv_of_isOpen
      (isOpen_lt continuous_const continuous_snd) (by norm_num)).comp_continuous
      continuous_subtype_val (fun p => p.property)
  unfold cubicThetaSectionEnergy cubicThetaTangentEnergy cubicThetaSectionDifferential
  apply ((continuous_snd.comp continuous_subtype_val).pow 2).mul
  apply continuous_finsetSum
  intro i hi
  exact ((hd.clm_apply continuous_const).norm).pow 2

def cubicThetaArithmeticQuotientEnergy (s : ℂ) (hs : 2<s.re) (q : CubicThetaQuotient) : ℝ :=
  cubicThetaSectionEnergy (cubicThetaArithmeticSection s hs) (cubicThetaQuotientLift q)

lemma cubicThetaArithmeticQuotientEnergy_apply (s : ℂ) (hs : 2<s.re) (p : CubicThetaPoint) :
    cubicThetaArithmeticQuotientEnergy s hs (cubicThetaQuotientMap p)=
      cubicThetaSectionEnergy (cubicThetaArithmeticSection s hs) p := by
  have he := cubicThetaQuotientLift_map (cubicThetaQuotientMap p)
  obtain ⟨g,hg⟩ := cubicThetaQuotient_covering.apply_eq_iff_mem_orbit.mp he
  unfold cubicThetaArithmeticQuotientEnergy
  rw [← hg,cubicThetaArithmeticEnergy_invariant]

lemma cubicThetaArithmeticQuotientEnergy_continuous (s : ℂ) (hs : 2<s.re) :
    Continuous (cubicThetaArithmeticQuotientEnergy s hs) := by
  apply cubicThetaQuotientMap_open.isQuotientMap.continuous_iff.mpr
  have he : cubicThetaArithmeticQuotientEnergy s hs ∘ cubicThetaQuotientMap=
      cubicThetaSectionEnergy (cubicThetaArithmeticSection s hs) :=
    funext (cubicThetaArithmeticQuotientEnergy_apply s hs)
  rw [he]
  exact cubicThetaArithmeticEnergy_continuous hs

end CubicFirstMoment

end

end OAI

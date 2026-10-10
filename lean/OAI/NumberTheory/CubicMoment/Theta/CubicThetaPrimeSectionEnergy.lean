import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPrimeArithmeticResidue
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaFunctionEnergyTransport

namespace OAI

/-! Actual first derivatives of sections on the prime cover. The
Atkin pullback preserves the hyperbolic differential energy pointwise. -/
noncomputable section
open Set Filter Topology
namespace CubicFirstMoment

def cubicThetaPrimeSectionFunction {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeSections hp) (y : ℂ × ℝ) : ℂ :=
  F.val (cubicThetaPointInclusion.symm y)

lemma cubicThetaPrimeSectionFunction_apply {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeSections hp) {y : ℂ × ℝ} (hy : 0<y.2) :
    cubicThetaPrimeSectionFunction hp F y=F.val ⟨y,hy⟩ := by
  apply congrArg F.val
  apply Subtype.ext
  have hyt : y∈cubicThetaPointInclusion.target := by rwa [cubicThetaPointInclusion_target]
  exact cubicThetaPointInclusion.right_inv hyt

lemma cubicThetaPrimeAtkinSection_function {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeSections hp) {y : ℂ × ℝ} (hy : 0<y.2) :
    cubicThetaPrimeSectionFunction hp (cubicThetaPrimeAtkinSection hp F) y=
      cubicThetaPrimeSectionFunction hp F (cubicThetaMobius (cubicThetaPrimeAtkinMatrix hp) y) := by
  rw [cubicThetaPrimeSectionFunction_apply hp _ hy,cubicThetaPrimeSectionFunction_apply hp _
    (cubicThetaMobius_height_pos _ hy)]
  rfl

lemma cubicThetaPrimeAtkinSection_c1 {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeSections hp)
    (hF : ContDiffOn ℝ 1 (cubicThetaPrimeSectionFunction hp F) {y : ℂ × ℝ | 0<y.2}) :
    ContDiffOn ℝ 1 (cubicThetaPrimeSectionFunction hp (cubicThetaPrimeAtkinSection hp F))
      {y : ℂ × ℝ | 0<y.2} := by
  have hM : ContDiffOn ℝ 1 (cubicThetaMobius (cubicThetaPrimeAtkinMatrix hp))
      {y : ℂ × ℝ | 0<y.2} := fun _ hy =>
    ((cubicThetaMobius_contDiffAt _ hy).of_le (by simp)).contDiffWithinAt
  exact (hF.comp hM (fun _ hy => cubicThetaMobius_height_pos _ hy)).congr
    (fun _ hy => cubicThetaPrimeAtkinSection_function hp F hy)

def cubicThetaPrimeSectionEnergy {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeSections hp) (x : CubicThetaPoint) : ℝ :=
  x.val.2^2*cubicThetaFunctionEnergy (cubicThetaPrimeSectionFunction hp F) x.val

lemma cubicThetaPrimeAtkinSection_energy {p : Eisenstein} (hp : primaryPrime p)
    (F : cubicThetaPrimeSections hp)
    (hF : ContDiffOn ℝ 1 (cubicThetaPrimeSectionFunction hp F) {y : ℂ × ℝ | 0<y.2})
    (x : CubicThetaPoint) :
    cubicThetaPrimeSectionEnergy hp (cubicThetaPrimeAtkinSection hp F) x=
      cubicThetaPrimeSectionEnergy hp F (cubicThetaPrimeAtkinMatrix hp • x) := by
  have he : cubicThetaPrimeSectionFunction hp (cubicThetaPrimeAtkinSection hp F)=ᶠ[𝓝 x.val]
      (fun y => cubicThetaPrimeSectionFunction hp F (cubicThetaMobius (cubicThetaPrimeAtkinMatrix hp) y)) := by
    filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds x.property] with y hy
    exact cubicThetaPrimeAtkinSection_function hp F hy
  have hd : DifferentiableAt ℝ (cubicThetaPrimeSectionFunction hp F)
      (cubicThetaMobius (cubicThetaPrimeAtkinMatrix hp) x.val) :=
    (hF.contDiffAt ((isOpen_lt continuous_const continuous_snd).mem_nhds
      (cubicThetaMobius_height_pos _ x.property))).differentiableAt (by norm_num)
  change x.val.2^2*cubicThetaFunctionEnergy
    (cubicThetaPrimeSectionFunction hp (cubicThetaPrimeAtkinSection hp F)) x.val=_
  unfold cubicThetaFunctionEnergy
  rw [he.fderiv_eq]
  exact cubicThetaFunctionEnergy_mobius (cubicThetaPrimeSectionFunction hp F)
    (cubicThetaPrimeAtkinMatrix hp) x.property hd

lemma cubicThetaPrimeSectionRestrict_energy {p : Eisenstein} (hp : primaryPrime p)
    (F : CubicThetaSection) (x : CubicThetaPoint) :
    cubicThetaPrimeSectionEnergy hp (cubicThetaPrimeSectionRestrict hp F) x=
      cubicThetaSectionEnergy F x := rfl

end CubicFirstMoment

end

end OAI

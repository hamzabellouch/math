import OAI.NumberTheory.CubicMoment.Theta.CubicThetaPositiveFourierProfile
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSmoothTests
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaMobiusSmooth

namespace OAI

/-! Smooth positive-cutoff Fourier profiles are actual compact smooth
sections, hence belong to the automorphic energy and mass spaces. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaHorizontalCharacter_contDiff (h : Eisenstein) :
    ContDiff ℝ ∞ (cubicThetaHorizontalCharacter h) := by
  unfold cubicThetaHorizontalCharacter
  simp only [Real.fourierChar_apply]
  unfold tracePair
  have hr : ContDiff ℝ ∞ (fun z : ℂ => 2*Real.pi*(2*(z*cubicThetaRowFrequency h).re)) :=
    contDiff_const.mul (contDiff_const.mul
      (Complex.reCLM.contDiff.comp (contDiff_id.mul contDiff_const)))
  exact Complex.contDiff_exp.comp ((Complex.ofRealCLM.contDiff.comp hr).mul contDiff_const)

lemma cubicThetaFourierProfileTerm_contDiffAt (h : Eisenstein) (W : C_c(ℝ,ℂ))
    (hsm : ContDiff ℝ ∞ (W : ℝ → ℂ)) (r : CubicThetaBottomRow)
    {p : ℂ × ℝ} (hp : 0<p.2) :
    ContDiffAt ℝ ∞ (fun q => cubicThetaFourierProfileTerm h r q W) p := by
  have hrad : ContDiffAt ℝ ∞ (fun q => cubicThetaRadialProfileTerm r q W) p :=
    contDiffAt_const.mul (hsm.contDiffAt.comp p (r.height_contDiffAt hp))
  exact hrad.mul ((cubicThetaHorizontalCharacter_contDiff h).contDiffAt.comp p
    (contDiffAt_fst.comp p (cubicThetaMobius_contDiffAt _ hp)))

lemma cubicThetaPositiveFourierProfile_contDiffOn (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) (hsm : ContDiff ℝ ∞ (W : ℝ → ℂ)) :
    ContDiffOn ℝ ∞ (fun p => cubicThetaFourierProfileSeries h p W) {p : ℂ × ℝ | 0<p.2} := by
  intro p hp
  obtain ⟨K,hKn,hK,hKpos⟩ := cubicThetaPositive_compact_neighborhood hp
  obtain ⟨S,hS⟩ := cubicThetaPositiveFourierProfile_compact_sum h W hε hW hK hKpos
  have he : (fun q => cubicThetaFourierProfileSeries h q W)=ᶠ[𝓝 p]
      (fun q => ∑ r∈S,cubicThetaFourierProfileTerm h r q W) := by
    filter_upwards [hKn] with q hq
    exact hS q hq
  have hd : ContDiffAt ℝ ∞ (fun q => ∑ r∈S,cubicThetaFourierProfileTerm h r q W) p :=
    ContDiffAt.sum (fun r _ => cubicThetaFourierProfileTerm_contDiffAt h W hsm r hp)
  exact (hd.congr_of_eventuallyEq he).contDiffWithinAt

def cubicThetaPositiveFourierProfileTest (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) (hsm : ContDiff ℝ ∞ (W : ℝ → ℂ)) :
    cubicThetaSmoothTests :=
  ⟨cubicThetaPositiveFourierProfileSection h W hε hW,by
    refine ⟨?_,cubicThetaPositiveFourierProfileSection_compact h W hε hW⟩
    apply (cubicThetaPositiveFourierProfile_contDiffOn h W hε hW hsm).congr
    intro y hy
    change cubicThetaFourierProfileSeries h (cubicThetaPointInclusion.symm y).val W=
      cubicThetaFourierProfileSeries h y W
    have he := cubicThetaPointInclusion.right_inv (show y∈cubicThetaPointInclusion.target by
      rwa [cubicThetaPointInclusion_target])
    change (cubicThetaPointInclusion.symm y).val=y at he
    exact congrArg (fun p => cubicThetaFourierProfileSeries h p W) he⟩

lemma cubicThetaPositiveFourierProfileL2_mem (h : Eisenstein) (W : C_c(ℝ,ℂ))
    {ε : ℝ} (hε : 0<ε) (hW : ∀ v≤ε,W v=0) (hsm : ContDiff ℝ ∞ (W : ℝ → ℂ)) :
    cubicThetaPositiveFourierProfileL2 h W hε hW∈cubicThetaAutomorphicL2 := by
  apply Submodule.le_topologicalClosure
  refine ⟨cubicThetaPositiveFourierProfileTest h W hε hW hsm,?_⟩
  rfl

end CubicFirstMoment

end

end OAI

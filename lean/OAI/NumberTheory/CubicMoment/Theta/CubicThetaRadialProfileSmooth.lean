import OAI.NumberTheory.CubicMoment.Theta.CubicThetaRadialProfileSeries
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSmoothTests

namespace OAI

/-! Smooth compact radial profiles produce genuine compact smooth sections. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff CompactlySupported
namespace CubicFirstMoment

lemma cubicThetaRadialProfileTerm_contDiffAt (W : C_c(ℝ,ℂ))
    (hsm : ContDiff ℝ ∞ (W : ℝ → ℂ)) (r : CubicThetaBottomRow)
    {p : ℂ × ℝ} (hp : 0<p.2) :
    ContDiffAt ℝ ∞ (fun q => cubicThetaRadialProfileTerm r q W) p :=
  contDiffAt_const.mul (hsm.contDiffAt.comp p (r.height_contDiffAt hp))

lemma cubicThetaRadialProfileSeries_contDiffOn (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤(1:ℝ), W v=0) (hsm : ContDiff ℝ ∞ (W : ℝ → ℂ)) :
    ContDiffOn ℝ ∞ (fun p => cubicThetaRadialProfileSeries p W) {p : ℂ × ℝ | 0<p.2} := by
  intro p hp
  obtain ⟨K,hKn,hK,hKpos⟩ := cubicThetaPositive_compact_neighborhood hp
  obtain ⟨S,hS⟩ := cubicThetaRadialProfileSeries_compact_sum W hW hK hKpos
  have he : (fun q => cubicThetaRadialProfileSeries q W) =ᶠ[𝓝 p]
      (fun q => ∑ r∈S, cubicThetaRadialProfileTerm r q W) := by
    filter_upwards [hKn] with q hq
    exact hS q hq
  have hd : ContDiffAt ℝ ∞ (fun q => ∑ r∈S, cubicThetaRadialProfileTerm r q W) p :=
    ContDiffAt.sum (fun r _ => cubicThetaRadialProfileTerm_contDiffAt W hsm r hp)
  exact (hd.congr_of_eventuallyEq he).contDiffWithinAt

def cubicThetaRadialProfileTest (W : C_c(ℝ,ℂ))
    (hW : ∀ v≤(1:ℝ), W v=0) (hsm : ContDiff ℝ ∞ (W : ℝ → ℂ)) : cubicThetaSmoothTests :=
  ⟨cubicThetaRadialProfileSection W hW,by
    refine ⟨?_,cubicThetaRadialProfileSection_compact W hW⟩
    apply (cubicThetaRadialProfileSeries_contDiffOn W hW hsm).congr
    intro y hy
    change cubicThetaRadialProfileSeries (cubicThetaPointInclusion.symm y).val W=
      cubicThetaRadialProfileSeries y W
    have he := cubicThetaPointInclusion.right_inv (show y∈cubicThetaPointInclusion.target by
      rwa [cubicThetaPointInclusion_target])
    change (cubicThetaPointInclusion.symm y).val=y at he
    exact congrArg (fun p => cubicThetaRadialProfileSeries p W) he⟩

end CubicFirstMoment

end

end OAI

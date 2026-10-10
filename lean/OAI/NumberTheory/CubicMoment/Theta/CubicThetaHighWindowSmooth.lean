import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHighWindowSeries

namespace OAI

/-! The compact high-cusp forcing is a genuine smooth test section. -/
noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace CubicFirstMoment

lemma cubicThetaIncomingForcing_smooth (s : ℂ) :
    ContDiff ℝ ∞ (cubicThetaIncomingForcing s) := by
  apply contDiff_iff_contDiffAt.mpr
  intro v
  by_cases hv : 0<v
  · exact cubicThetaIncomingForcing_contDiffAt s hv
  · have he : cubicThetaIncomingForcing s =ᶠ[𝓝 v] (fun _ => 0) := by
      filter_upwards [eventually_lt_nhds (show v<1 by linarith)] with t ht
      exact cubicThetaIncomingForcing_zero s (Or.inl ht)
    exact contDiffAt_const.congr_of_eventuallyEq he

lemma cubicThetaWindowDefect_smooth (s : ℂ) :
    ContDiff ℝ ∞ (cubicThetaWindowDefect s) := by
  have hd := (contDiff_infty_iff_deriv.mp (cubicThetaWindowHeight_smooth s)).2
  have hdd := (contDiff_infty_iff_deriv.mp hd).2
  exact ((Complex.ofRealCLM.contDiff.pow 2).mul hdd).sub
    (Complex.ofRealCLM.contDiff.mul hd) |>.sub
      (contDiff_const.mul (cubicThetaWindowHeight_smooth s))

lemma cubicThetaHighWindowForcing_smooth (s : ℂ) :
    ContDiff ℝ ∞ (cubicThetaHighWindowForcing s) :=
  (cubicThetaIncomingForcing_smooth s).sub (cubicThetaWindowDefect_smooth s)

lemma cubicThetaHighWindowSeries_smooth (s : ℂ) :
    ContDiffOn ℝ ∞ (fun p => cubicThetaHighWindowSeries p s) {p : ℂ × ℝ | 0<p.2} := by
  intro p hp
  obtain ⟨K,hKn,hK,hKpos⟩ := cubicThetaPositive_compact_neighborhood hp
  obtain ⟨S,hS⟩ := cubicThetaHighWindowSeries_compact_sum hK hKpos
  have he : (fun q => cubicThetaHighWindowSeries q s) =ᶠ[𝓝 p]
      (fun q => ∑ r∈S, cubicThetaHighWindowTerm r q s) := by
    filter_upwards [hKn] with q hq
    exact hS q hq s
  have hd : ContDiffAt ℝ ∞ (fun q => ∑ r∈S, cubicThetaHighWindowTerm r q s) p := by
    apply ContDiffAt.sum
    intro r _
    exact contDiffAt_const.mul ((cubicThetaHighWindowForcing_smooth s).contDiffAt.comp p
      (r.height_contDiffAt hp))
  exact (hd.congr_of_eventuallyEq he).contDiffWithinAt

def cubicThetaHighWindowTest (s : ℂ) : cubicThetaSmoothTests :=
  ⟨cubicThetaHighWindowSection s,by
    refine ⟨?_,cubicThetaHighWindowSection_compact s⟩
    apply (cubicThetaHighWindowSeries_smooth s).congr
    intro y hy
    change cubicThetaHighWindowSeries (cubicThetaPointInclusion.symm y).val s=
      cubicThetaHighWindowSeries y s
    have he := cubicThetaPointInclusion.right_inv (show y∈cubicThetaPointInclusion.target by
      rwa [cubicThetaPointInclusion_target])
    change (cubicThetaPointInclusion.symm y).val=y at he
    exact congrArg (fun p => cubicThetaHighWindowSeries p s) he⟩

end CubicFirstMoment

end

end OAI

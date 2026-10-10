import OAI.NumberTheory.CubicMoment.Theta.CubicThetaLocalLifts
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaQuotientCharts
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaMobiusSmooth

namespace OAI

/-! On every overlap, quotient coordinates differ locally by the actual
smooth Mobius action of one element of the principal group. -/
noncomputable section
open Filter Topology
open scoped ContDiff
namespace CubicFirstMoment

def cubicThetaChartTransition
    (e f : OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient)
    (y : ℂ × ℝ) : ℂ × ℝ :=
  (f.symm (e (cubicThetaPointInclusion.symm y))).val

def cubicThetaChartTransitionSource
    (e f : OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient) : Set (ℂ × ℝ) :=
  {y | y∈cubicThetaPointInclusion.target ∧
    cubicThetaPointInclusion.symm y∈e.source ∧
    e (cubicThetaPointInclusion.symm y)∈f.target}

lemma cubicThetaChartTransition_deck
    (e f : OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient)
    (he : (e : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap)
    (hf : (f : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap)
    {x : ℂ × ℝ} (hx : x∈cubicThetaChartTransitionSource e f) :
    ∃ g : cubicThetaPrincipalGroup, cubicThetaChartTransition e f =ᶠ[𝓝 x]
      cubicThetaMobius (cubicThetaPrincipalComplex g) := by
  let F : ℂ × ℝ → CubicThetaPoint := cubicThetaPointInclusion.symm
  let G : ℂ × ℝ → CubicThetaPoint := fun y => f.symm (e (F y))
  have hF : ContinuousAt F x := cubicThetaPointInclusion.symm.continuousAt hx.1
  have hE : ContinuousAt (fun y => e (F y)) x := (e.continuousAt hx.2.1).comp hF
  have hG : ContinuousAt G x := (f.symm.continuousAt hx.2.2).comp
    (x:=x) (f:=fun y => e (F y)) hE
  have htarget : ∀ᶠ y in 𝓝 x, e (F y)∈f.target :=
    hE.preimage_mem_nhds (f.open_target.mem_nhds hx.2.2)
  have hq : ∀ᶠ y in 𝓝 x, cubicThetaQuotientMap (G y)=cubicThetaQuotientMap (F y) := by
    filter_upwards [htarget] with y hy
    change cubicThetaQuotientMap (f.symm (e (F y)))=cubicThetaQuotientMap (F y)
    calc
      _ = f (f.symm (e (F y))) := (congrFun hf _).symm
      _ = e (F y) := f.right_inv hy
      _ = cubicThetaQuotientMap (F y) := congrFun he _
  obtain ⟨g,hg⟩ := cubicThetaLocalLifts_deck hG hF hq
  refine ⟨g,?_⟩
  have hpositive : ∀ᶠ y in 𝓝 x, y∈cubicThetaPointInclusion.target :=
    cubicThetaPointInclusion.open_target.mem_nhds hx.1
  filter_upwards [hg,hpositive] with y hy hp
  have hv : (F y).val=y := cubicThetaPointInclusion.right_inv hp
  have hv' := congrArg Subtype.val hy
  change cubicThetaChartTransition e f y=
    cubicThetaMobius (cubicThetaPrincipalComplex g) (F y).val at hv'
  rwa [hv] at hv'

lemma cubicThetaChartTransition_contDiffAt
    (e f : OpenPartialHomeomorph CubicThetaPoint CubicThetaQuotient)
    (he : (e : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap)
    (hf : (f : CubicThetaPoint → CubicThetaQuotient)=cubicThetaQuotientMap)
    {x : ℂ × ℝ} (hx : x∈cubicThetaChartTransitionSource e f) :
    ContDiffAt ℝ ∞ (cubicThetaChartTransition e f) x := by
  obtain ⟨g,hg⟩ := cubicThetaChartTransition_deck e f he hf hx
  have hp : 0<x.2 := by
    have h := hx.1
    rwa [cubicThetaPointInclusion_target] at h
  exact (cubicThetaMobius_contDiffAt (cubicThetaPrincipalComplex g) hp).congr_of_eventuallyEq hg

end CubicFirstMoment

end

end OAI

import OAI.Geometry.Relativity.CKS.LocalConstraints
import OAI.Geometry.Relativity.CKS.VolumeAlgebra

namespace OAI

noncomputable section
open Bundle Manifold Set MeasureTheory
open scoped ContDiff ENNReal
namespace CKSIntrinsicVolume
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

def chartTransition (x z : M) : E → E := (extChartAt I x) ∘ (extChartAt I z).symm

def transitionDeriv (x z : M) (y : E) : E →L[ℝ] E :=
  (mfderiv I 𝓘(ℝ,E) (extChartAt I x) ((extChartAt I z).symm y)).comp (chartFrame z y)

lemma hasFDerivWithinAt_chartTransition (x z : M) {y : E}
    (hz : y ∈ (extChartAt I z).target)
    (hx : (extChartAt I z).symm y ∈ (extChartAt I x).source) :
    HasFDerivWithinAt (chartTransition x z) (transitionDeriv x z y) (range I) y := by
  have hxs : (extChartAt I z).symm y ∈ (chartAt H x).source := by simpa using hx
  exact ((mdifferentiableAt_extChartAt hxs).hasMFDerivAt.comp_hasMFDerivWithinAt y
    (mdifferentiableWithinAt_extChartAt_symm hz).hasMFDerivWithinAt).hasFDerivWithinAt

lemma chartFrame_comp_transitionDeriv (x z : M) {y : E}
    (hx : (extChartAt I z).symm y ∈ (extChartAt I x).source) :
    (chartFrame x (chartTransition x z y)).comp (transitionDeriv x z y) = chartFrame z y := by
  unfold transitionDeriv
  change (mfderivWithin 𝓘(ℝ,E) I (extChartAt I x).symm (range I)
    (extChartAt I x ((extChartAt I z).symm y))).comp
    ((mfderiv I 𝓘(ℝ,E) (extChartAt I x) ((extChartAt I z).symm y)).comp
    (chartFrame z y)) = chartFrame z y
  rw [← ContinuousLinearMap.comp_assoc,
    mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' hx]
  rfl

lemma pullbackInner_transition (g : Metric (M := M)) (x z : M) {y : E}
    (hx : (extChartAt I z).symm y ∈ (extChartAt I x).source) :
    pullbackInner g z y = (pullbackInner g x (chartTransition x z y)).comp
      (transitionDeriv x z y).toLinearMap (transitionDeriv x z y).toLinearMap := by
  ext v w
  change g.inner ((extChartAt I z).symm y) (chartFrame z y v) (chartFrame z y w) =
    g.inner ((extChartAt I x).symm (chartTransition x z y))
      (chartFrame x (chartTransition x z y) (transitionDeriv x z y v))
      (chartFrame x (chartTransition x z y) (transitionDeriv x z y w))
  have hv := congrArg (fun L : E →L[ℝ] E => L v) (chartFrame_comp_transitionDeriv x z hx)
  have hw := congrArg (fun L : E →L[ℝ] E => L w) (chartFrame_comp_transitionDeriv x z hx)
  change chartFrame x (chartTransition x z y) (transitionDeriv x z y v) = _ at hv
  change chartFrame x (chartTransition x z y) (transitionDeriv x z y w) = _ at hw
  rw [hv, hw]
  have heq : (extChartAt I x).symm (chartTransition x z y) = (extChartAt I z).symm y :=
    (extChartAt I x).left_inv hx
  rw [heq]
  rfl

lemma chartDensity_transition (g : Metric (M := M)) (x z : M) {y : E}
    (hx : (extChartAt I z).symm y ∈ (extChartAt I x).source) :
    chartDensity g z y = |(transitionDeriv x z y).det| *
      chartDensity g x (chartTransition x z y) := by
  simp only [chartDensity, chartMatrix_eq_toMatrix]
  rw [pullbackInner_transition g x z hx, sqrt_gram_det_comp]

end CKSIntrinsicVolume

end

end OAI

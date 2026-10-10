import Mathlib
import OAI.Geometry.WeakMTW.Coordinates.PairExpCoordinates
import OAI.Geometry.WeakMTW.Coordinates.ChartGlobalVariation

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal ChartMetric CoordinateGeometry
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 def branchAction (x : M) (e : OpenPartialHomeomorph (Model n × Model n) (Model n × Model n))
    (q : Model n × Model n) : ℝ := chartKinetic x (e.symm q)

 theorem pair_inverse_fst (x y : M)
    (e : OpenPartialHomeomorph (Model n × Model n) (Model n × Model n))
    (he : (e : (Model n × Model n) → (Model n × Model n)) = pairExpCoordinates (n := n) x y)
    {q : Model n × Model n} (hq : q ∈ e.target) : (e.symm q).1 = q.1 := by
  have hh := congrArg Prod.fst (e.right_inv hq)
  simpa only [he,pairExpCoordinates] using hh

 theorem branchAction_smooth (x y : M)
    (e : OpenPartialHomeomorph (Model n × Model n) (Model n × Model n))
    (hes : e.source ⊆ pairExpDomain (n := n) x y)
    (hei : ContDiffOn ℝ ∞ e.symm e.target) : ContDiffOn ℝ ∞ (branchAction x e) e.target :=
  (chartKinetic_smooth x).comp hei (fun _ hq => (hes (e.map_target hq)).1)

 theorem branchAction_derivative (x y : M)
    (e : OpenPartialHomeomorph (Model n × Model n) (Model n × Model n))
    (he : (e : (Model n × Model n) → (Model n × Model n)) = pairExpCoordinates (n := n) x y)
    (hes : e.source ⊆ pairExpDomain (n := n) x y)
    (hei : ContDiffOn ℝ ∞ e.symm e.target)
    {q : Model n × Model n} (hq : q ∈ e.target) (w : Model n × Model n) :
    fderiv ℝ (branchAction x e) q w =
      metric y q.2 (stateChart y (geodesicFlow 1 ((stateChart x).symm (e.symm q)))).2 w.2 -
        metric x q.1 (e.symm q).2 w.1 := by
  let p := e.symm q
  let Φ : (Model n × Model n) → (Model n × Model n) := fun r => stateChart y (geodesicFlow 1 ((stateChart x).symm r))
  have hp : p ∈ e.source := e.map_target hq
  have hd := hes hp
  have hi := ((hei q hq).contDiffAt (e.open_target.mem_nhds hq)).differentiableAt (by simp)
  have hΦ := (chart_flow_smooth x y 1 hd.1 hd.2).differentiableAt (by simp)
  have hk := ((chartKinetic_smooth x p hd.1).contDiffAt
    ((stateChart x).open_target.mem_nhds hd.1)).differentiableAt (by simp)
  have heD : HasFDerivAt e
      ((ContinuousLinearMap.fst ℝ (Model n) (Model n)).prod
        ((ContinuousLinearMap.fst ℝ (Model n) (Model n)).comp (fderiv ℝ Φ p))) p := by
    rw [he]
    exact (hasFDerivAt_fst (p := p)).prodMk hΦ.hasFDerivAt.fst
  have hcomp := heD.comp q hi.hasFDerivAt
  have hident : e ∘ e.symm =ᶠ[𝓝 q] id := by
    filter_upwards [e.open_target.mem_nhds hq] with r hr
    exact e.right_inv hr
  have hdi := hcomp.unique ((hasFDerivAt_id q).congr_of_eventuallyEq hident)
  let k := fderiv ℝ e.symm q w
  have hdw := congrArg (fun L : (Model n × Model n) →L[ℝ] (Model n × Model n) => L w) hdi
  change (k.1,(fderiv ℝ Φ p k).1) = w at hdw
  have hhfirst := congrArg (fun r : Model n × Model n => r.1) hdw
  have hfirst : k.1 = w.1 := hhfirst
  have hhsecond := congrArg (fun r : Model n × Model n => r.2) hdw
  have hsecond : (fderiv ℝ Φ p k).1 = w.2 := hhsecond
  have hPhi₁ : (Φ p).1 = q.2 := by
    have hh := congrArg Prod.snd (e.right_inv hq)
    simpa only [he,pairExpCoordinates] using hh
  have hpair := chart_flow_boundary x y 1 hd.1 hd.2 k
  change metric y (Φ p).1 (Φ p).2 (fderiv ℝ Φ p k).1 =
    metric x p.1 p.2 k.1 + 1 * fderiv ℝ (chartKinetic x) p k at hpair
  rw [hPhi₁,hfirst,hsecond,one_mul,pair_inverse_fst x y e he hq] at hpair
  have hA : HasFDerivAt (branchAction x e) ((fderiv ℝ (chartKinetic x) p).comp (fderiv ℝ e.symm q)) q :=
    hk.hasFDerivAt.comp q hi.hasFDerivAt
  rw [hA.fderiv,ContinuousLinearMap.comp_apply]
  change fderiv ℝ (chartKinetic x) p k = _
  linarith

 theorem branchAction_initial_derivative (x y : M)
    (e : OpenPartialHomeomorph (Model n × Model n) (Model n × Model n))
    (he : (e : (Model n × Model n) → (Model n × Model n)) = pairExpCoordinates (n := n) x y)
    (hes : e.source ⊆ pairExpDomain (n := n) x y)
    (hei : ContDiffOn ℝ ∞ e.symm e.target)
    {q : Model n × Model n} (hq : q ∈ e.target) (w : Model n) :
    fderiv ℝ (branchAction x e) q (w,0) = -metric x q.1 (e.symm q).2 w := by
  rw [branchAction_derivative x y e he hes hei hq]
  simp only [map_zero,zero_sub]

 theorem branchAction_is_kinetic (x y : M)
    (e : OpenPartialHomeomorph (Model n × Model n) (Model n × Model n))
    (he : (e : (Model n × Model n) → (Model n × Model n)) = pairExpCoordinates (n := n) x y)
    {q : Model n × Model n} (hq : q ∈ e.target) :
    branchAction x e q = metric x q.1 (e.symm q).2 (e.symm q).2 / 2 := by
  unfold branchAction chartKinetic
  rw [pair_inverse_fst x y e he hq]

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI

import Mathlib
import OAI.Geometry.WeakMTW.Variations.BranchAction
import OAI.Geometry.WeakMTW.Variations.CovariantActionHessian

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace WeakMTW
noncomputable section
open RiemannianLocal ChartMetric CoordinateGeometry RadialHessianCalculus
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem branch_initial_smooth (x y : M)
    (e : OpenPartialHomeomorph (Model n × Model n) (Model n × Model n))
    (hes : e.source ⊆ pairExpDomain (n := n) x y)
    (hei : ContDiffOn ℝ ∞ e.symm e.target)
    {q : Model n × Model n} (hq : q ∈ e.target) :
    ContDiffAt ℝ ∞ (fun a => branchAction x e (a,q.2)) q.1 :=
  ContDiffAt.comp (f := fun a => (a,q.2)) (g := branchAction x e) q.1
    ((branchAction_smooth x y e hes hei q hq).contDiffAt (e.open_target.mem_nhds hq))
    (contDiffAt_id.prodMk contDiffAt_const)

 theorem branch_initial_gradient (x y : M)
    (e : OpenPartialHomeomorph (Model n × Model n) (Model n × Model n))
    (he : (e : (Model n × Model n) → (Model n × Model n)) = pairExpCoordinates (n := n) x y)
    (hes : e.source ⊆ pairExpDomain (n := n) x y)
    (hei : ContDiffOn ℝ ∞ e.symm e.target)
    {q : Model n × Model n} (hq : q ∈ e.target) (w : Model n) :
    fderiv ℝ (fun a => branchAction x e (a,q.2)) q.1 w = -metric x q.1 (e.symm q).2 w := by
  have hA := ((branchAction_smooth x y e hes hei q hq).contDiffAt
    (e.open_target.mem_nhds hq)).differentiableAt (by simp)
  have hi := (hasFDerivAt_id (𝕜 := ℝ) q.1).prodMk (hasFDerivAt_const (𝕜 := ℝ) q.2 q.1)
  have hd := hA.hasFDerivAt.comp q.1 hi
  have hde := hd.fderiv
  dsimp only [Function.comp_def,id_eq] at hde
  rw [hde]
  change fderiv ℝ (branchAction x e) q (w,0) = _
  exact branchAction_initial_derivative x y e he hes hei hq w

 theorem branch_initial_radial (x y : M)
    (e : OpenPartialHomeomorph (Model n × Model n) (Model n × Model n))
    (he : (e : (Model n × Model n) → (Model n × Model n)) = pairExpCoordinates (n := n) x y)
    (hes : e.source ⊆ pairExpDomain (n := n) x y)
    (hei : ContDiffOn ℝ ∞ e.symm e.target)
    {q : Model n × Model n} (hq : q ∈ e.target) (w : Model n) :
    actionForm (metric x) (fun a => branchAction x e (a,q.2)) q.1 (e.symm q).2
      w (e.symm q).2 = metric x q.1 w (e.symm q).2 := by
  let ν : Model n → Model n := fun a => (e.symm (a,q.2)).2
  let f : Model n → ℝ := fun a => branchAction x e (a,q.2)
  have hν : ContDiffAt ℝ ∞ ν q.1 :=
    ContDiffAt.comp (f := fun a => (a,q.2)) (g := fun z => (e.symm z).2) q.1
      (((hei q hq).contDiffAt (e.open_target.mem_nhds hq)).snd)
      (contDiffAt_id.prodMk contDiffAt_const)
  have hf := branch_initial_smooth x y e hes hei hq
  have hqT : q.1 ∈ (chartAt (Model n) x).target := by
    rw [← pair_inverse_fst x y e he hq]
    exact (stateChart_target x _).mp (hes (e.map_target hq)).1
  have hnear : ∀ᶠ a : Model n in 𝓝 q.1, (a,q.2) ∈ e.target :=
    (continuousAt_id.prodMk continuousAt_const).preimage_mem_nhds (e.open_target.mem_nhds hq)
  have henergy : f =ᶠ[𝓝 q.1] (fun a => metric x a (ν a) (ν a) / 2) := by
    filter_upwards [hnear] with a ha
    exact branchAction_is_kinetic x y e he ha
  have hgrad : ∀ᶠ a in 𝓝 q.1, ∀ w, fderiv ℝ f a w = -metric x a (ν a) w := by
    filter_upwards [hnear] with a ha w
    exact branch_initial_gradient x y e he hes hei ha w
  exact actionForm_radial (metric x) ν f (chartAt (Model n) x).open_target
    ((metric_smooth x).differentiableOn (by simp)) (fun a _ => metric_symmetric x a)
    hqT (fun v hv => metric_positive x hqT hv) (hν.differentiableAt (by simp))
    (hf.of_le (by simp)) henergy hgrad w

end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI

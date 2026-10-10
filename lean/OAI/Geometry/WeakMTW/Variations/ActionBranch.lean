import Mathlib
import OAI.Geometry.WeakMTW.Geodesics.NonconjugateBranches
import OAI.Geometry.WeakMTW.Variations.BranchHessian
import OAI.Geometry.WeakMTW.Coordinates.FocalCoordinates

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

 structure ActionBranch (x y : M) where
  coord : OpenPartialHomeomorph (Model n × Model n) (Model n × Model n)
  map_eq : (coord : (Model n × Model n) → (Model n × Model n)) = pairExpCoordinates (n := n) x y
  domain : coord.source ⊆ pairExpDomain (n := n) x y
  smooth : ContDiffOn ℝ ∞ coord.symm coord.target

 namespace ActionBranch
 variable {x y : M}

 theorem exists_of_nonconjugate {v : TangentSpace (model n) x} (hn : Nonconjugate x v) :
    ∃ B : ActionBranch (n := n) x (exp x v),
      stateChart x (⟨x,v⟩ : TangentBundle (model n) M) ∈ B.coord.source := by
  obtain ⟨e,he,hv,hes,hei⟩ := pairExpCoordinates_inverse_of_nonfocal x (exp x v) hn
    (mem_chart_source (Model n) (exp x v))
  exact ⟨⟨e,he,hes,hei⟩,hv⟩

 def value (B : ActionBranch (n := n) x y) : Model n × Model n → ℝ := branchAction x B.coord

 theorem smooth_value (B : ActionBranch (n := n) x y) :
    ContDiffOn ℝ ∞ B.value B.coord.target := branchAction_smooth x y B.coord B.domain B.smooth

 theorem inverse_state (B : ActionBranch (n := n) x y) (p : TangentBundle (model n) M)
    (hp : p ∈ (stateChart x).source) (hpe : stateChart x p ∈ B.coord.source) :
    B.coord.symm (chartAt (Model n) x p.1,chartAt (Model n) y (exp p.1 p.2)) = stateChart x p := by
  rw [← pairExpCoordinates_state x y p hp,← B.map_eq,B.coord.left_inv hpe]

 theorem target_state (B : ActionBranch (n := n) x y) (p : TangentBundle (model n) M)
    (hp : p ∈ (stateChart x).source) (hpe : stateChart x p ∈ B.coord.source) :
    (chartAt (Model n) x p.1,chartAt (Model n) y (exp p.1 p.2)) ∈ B.coord.target := by
  rw [← pairExpCoordinates_state x y p hp,← B.map_eq]
  exact B.coord.map_source hpe

 theorem gradient_state (B : ActionBranch (n := n) x y) (p : TangentBundle (model n) M)
    (hp : p ∈ (stateChart x).source) (hpe : stateChart x p ∈ B.coord.source) (u : Model n) :
    fderiv ℝ B.value (chartAt (Model n) x p.1,chartAt (Model n) y (exp p.1 p.2)) (u,0) =
      -metric x (chartAt (Model n) x p.1) (stateChart x p).2 u := by
  rw [value,branchAction_initial_derivative x y B.coord B.map_eq B.domain B.smooth
    (B.target_state p hp hpe),B.inverse_state p hp hpe]

 theorem value_state (B : ActionBranch (n := n) x y) (p : TangentBundle (model n) M)
    (hp : p ∈ (stateChart x).source) (hpe : stateChart x p ∈ B.coord.source) :
    B.value (chartAt (Model n) x p.1,chartAt (Model n) y (exp p.1 p.2)) = ‖p.2‖^2/2 := by
  rw [value,branchAction, B.inverse_state p hp hpe]
  unfold chartKinetic
  have hh := stateChart_pairing x p.1 ((stateChart_source x p).mp hp) p.2 p.2
  change metric x (chartAt (Model n) x p.1) (stateChart x p).2 (stateChart x p).2 / 2 = _
  simpa only [real_inner_self_eq_norm_sq] using congrArg (fun a : ℝ => a/2) hh

 theorem gradient_center (B : ActionBranch (n := n) x y) {v : TangentSpace (model n) x}
    (hve : stateChart x (⟨x,v⟩ : TangentBundle (model n) M) ∈ B.coord.source)
    (ξ : TangentSpace (model n) x) :
    fderiv ℝ B.value (chartAt (Model n) x x,chartAt (Model n) y (exp x v))
      (tangentChartLinear x ξ,0) = -inner ℝ v ξ := by
  rw [B.gradient_state ⟨x,v⟩ ((stateChart_source x _).mpr (mem_chart_source (Model n) x)) hve]
  rw [← tangentChartLinear_eq]
  exact congrArg Neg.neg (metric_chart_pair x x (mem_chart_source (Model n) x) v ξ)

 theorem eq_cost_near (B : ActionBranch (n := n) x y)
    {v : TangentSpace (model n) x} (hv : v ∈ injectivityDomain x)
    (hy : exp x v ∈ (chartAt (Model n) y).source)
    (hve : stateChart x (⟨x,v⟩ : TangentBundle (model n) M) ∈ B.coord.source) :
    B.value =ᶠ[𝓝 (chartAt (Model n) x x,chartAt (Model n) y (exp x v))]
      (fun q => cost ((chartAt (Model n) x).symm q.1) ((chartAt (Model n) y).symm q.2)) := by
  filter_upwards [cost_coord_eq_inverse_arbitrary_chart x y hv hy B.coord B.map_eq hve] with q hq
  exact hq.symm

 theorem hessian_limit (B : ActionBranch (n := n) x y)
    {v : TangentSpace (model n) x}
    (hve : stateChart x (⟨x,v⟩ : TangentBundle (model n) M) ∈ B.coord.source)
    (ξ : TangentSpace (model n) x) {w : ℝ → TangentSpace (model n) x} {L : Filter ℝ}
    (hw : Tendsto w L (𝓝 v)) (hI : ∀ᶠ r in L, w r ∈ injectivityDomain x) :
    Tendsto (fun r => actionHessian x (w r) ξ ξ) L (𝓝 (branchHessianDiag x y B.coord v ξ)) := by
  have ht := (branchHessianDiag_continuous x y B.coord B.map_eq B.domain B.smooth hve ξ).tendsto.comp hw
  apply ht.congr'
  have hsrc : ∀ᶠ r in L, verticalCoordinates x (w r) ∈ B.coord.source :=
    (((verticalCoordinates_smooth x).continuous.tendsto v).comp hw)
      (B.coord.open_source.mem_nhds (by simpa only [verticalCoordinates_eq] using hve))
  filter_upwards [hI,hsrc] with r hr hrs
  exact (actionHessian_eq_branch x y B.coord B.map_eq B.domain B.smooth hr
    (by simpa only [verticalCoordinates_eq] using hrs) ξ).symm

 end ActionBranch
end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI

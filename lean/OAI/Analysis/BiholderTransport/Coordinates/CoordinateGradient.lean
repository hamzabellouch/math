import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.IntrinsicGradient

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology
open MeasureTheory
open scoped ContDiff ENNReal

open Set Filter Manifold Bundle ContinuousLinearMap MeasureTheory
open scoped Topology ContDiff Manifold Bundle ENNReal

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology Manifold

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Bundle
open scoped Topology Bundle

open scoped Topology
open Function Manifold Set
open Manifold Bundle
open scoped Manifold Bundle
open Set

open Set Filter
open scoped Topology ContDiff

namespace WeakMTWTransport

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]

lemma coordinate_gradient_of_hasMFDerivAt {a : M} (z : TangentBundle 𝓘(ℝ,E) M)
    (hz : z.1 ∈ (extChartAt 𝓘(ℝ,E) a).source) (f : M → ℝ) (τ : ℝ)
    (hM : HasMFDerivAt 𝓘(ℝ,E) 𝓘(ℝ,ℝ) f z.1 (innerSL ℝ (τ • z.2))) :
    HasFDerivAt (fun q : E => f ((extChartAt 𝓘(ℝ,E) a).symm q))
      (τ • riemannianCoordinateMetric a (extChartAt 𝓘(ℝ,E) a z.1)
        ((extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) (⟨a,0⟩ : TangentBundle 𝓘(ℝ,E) M) z).2))
      (extChartAt 𝓘(ℝ,E) a z.1) := by
  let c := extChartAt 𝓘(ℝ,E) a
  let F : E → ℝ := fun q => f (c.symm q)
  have hc : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ c.symm (c z.1) :=
    (contMDiffOn_extChartAt_symm a).contMDiffAt
      ((isOpen_extChartAt_target a).mem_nhds (c.map_source hz))
  have hm : MDifferentiableAt 𝓘(ℝ,E) 𝓘(ℝ,ℝ) f (c.symm (c z.1)) := by
    rw [c.left_inv hz]; exact hM.mdifferentiableAt
  have hF : DifferentiableAt ℝ F (c z.1) :=
    (hm.comp (c z.1) (hc.mdifferentiableAt (by simp))).differentiableAt
  have hz' : z.1 ∈ (chartAt E a).source := by simpa only [extChartAt_source] using hz
  have hDc := (mdifferentiableAt_extChartAt (I := 𝓘(ℝ,E)) hz').hasMFDerivAt
  have H := hF.hasFDerivAt.hasMFDerivAt.comp z.1 hDc
  have heq : f =ᶠ[𝓝 z.1] (fun y : M => F (c y)) := by
    filter_upwards [(isOpen_extChartAt_source a).mem_nhds hz] with y hy
    dsimp [F]; rw [c.left_inv hy]
  have H' := H.congr_of_eventuallyEq heq
  have hEq := H'.mfderiv.symm.trans hM.mfderiv
  have hsur : Function.Surjective (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) c z.1) := by
    obtain ⟨A,hA⟩ := isInvertible_mfderiv_extChartAt hz
    rw [←hA]
    exact A.surjective
  apply hF.hasFDerivAt.congr_fderiv
  ext u
  obtain ⟨v,rfl⟩ := hsur u
  have hh := congrArg (fun D : TangentSpace 𝓘(ℝ,E) z.1 →L[ℝ] ℝ => D v) hEq
  change fderiv ℝ F (c z.1) (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) c z.1 v) =
    τ * riemannianCoordinateMetric a (c z.1)
      ((extChartAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) (⟨a,0⟩ : TangentBundle 𝓘(ℝ,E) M) z).2)
      (mfderiv 𝓘(ℝ,E) 𝓘(ℝ,E) c z.1 v)
  rw [tangent_chart_apply,←mfderiv_extChartAt_eq_tangentCoordChange hz]
  dsimp only [Prod.snd]
  erw [coordinate_metric_chart_pairing hz z.2 v]
  convert! hh using 1
  simp only [innerSL_apply_apply,real_inner_smul_left]

end

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {M : Type*} [MetricSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]

lemma coordinate_cost_contDiffAt {a : M} {δ : ℝ}
    (hC : ContMDiffOn (𝓘(ℝ,E).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞
      (fun z : M×M => dist z.1 z.2^2/2) (Metric.ball a δ ×ˢ Metric.ball a δ))
    {b : F → M} {v : F} {q : E}
    (hb : ContMDiffAt 𝓘(ℝ,F) 𝓘(ℝ,E) ∞ b v)
    (hbδ : b v ∈ Metric.ball a δ)
    (hq : q ∈ (extChartAt 𝓘(ℝ,E) a).target)
    (hqδ : (extChartAt 𝓘(ℝ,E) a).symm q ∈ Metric.ball a δ) :
    ContDiffAt ℝ ∞ (fun z : F×E => dist (b z.1) ((extChartAt 𝓘(ℝ,E) a).symm z.2)^2/2) (v,q) := by
  have hc : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ (extChartAt 𝓘(ℝ,E) a).symm q :=
    (contMDiffOn_extChartAt_symm a).contMDiffAt ((isOpen_extChartAt_target a).mem_nhds hq)
  have hcost := hC.contMDiffAt ((Metric.isOpen_ball.prod Metric.isOpen_ball).mem_nhds (show (b v,(extChartAt 𝓘(ℝ,E) a).symm q) ∈ Metric.ball a δ ×ˢ Metric.ball a δ from ⟨hbδ,hqδ⟩))
  exact (hcost.comp (v,q) ((hb.comp (v,q) contDiffAt_fst.contMDiffAt).prodMk
    (hc.comp (v,q) contDiffAt_snd.contMDiffAt))).contDiffAt

lemma coordinate_outgoing_cost_contDiffAt {a y : M} {δ : ℝ}
    (hC : ContMDiffOn (𝓘(ℝ,E).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞
      (fun z : M×M => dist z.1 z.2^2/2) (Metric.ball a δ ×ˢ Metric.ball a δ))
    {q : E} (hy : y ∈ Metric.ball a δ)
    (hq : q ∈ (extChartAt 𝓘(ℝ,E) a).target)
    (hqδ : (extChartAt 𝓘(ℝ,E) a).symm q ∈ Metric.ball a δ) :
    ContDiffAt ℝ ∞ (fun q : E => dist ((extChartAt 𝓘(ℝ,E) a).symm q) y^2/2) q := by
  have hc : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,E) ∞ (extChartAt 𝓘(ℝ,E) a).symm q :=
    (contMDiffOn_extChartAt_symm a).contMDiffAt ((isOpen_extChartAt_target a).mem_nhds hq)
  have hcost := hC.contMDiffAt ((Metric.isOpen_ball.prod Metric.isOpen_ball).mem_nhds (show ((extChartAt 𝓘(ℝ,E) a).symm q,y) ∈ Metric.ball a δ ×ˢ Metric.ball a δ from ⟨hqδ,hy⟩))
  exact (hcost.comp q (hc.prodMk contMDiffAt_const)).contDiffAt

end WeakMTWTransport

end

end OAI

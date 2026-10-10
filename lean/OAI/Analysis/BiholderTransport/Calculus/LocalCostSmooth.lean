import Mathlib
import OAI.Analysis.BiholderTransport.Coordinates.JointNormalChart

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

namespace WeakMTWTransport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M]

lemma exists_local_cost_smooth (a : M) :
    ∃ δ : ℝ, 0<δ ∧ ContMDiffOn (𝓘(ℝ,E).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞
      (fun z : M×M => dist z.1 z.2^2/2) (Metric.ball a δ ×ˢ Metric.ball a δ) := by
  obtain ⟨δ,_,τ,hδ,_,_,_,Φ,e,_,_,_,he,_,_,hei,hsrc,_,htarget,hdist⟩ :=
    exists_uniform_metric_normal_coordinates (E := E) a
  let c := extChartAt 𝓘(ℝ,E) a
  let g := riemannianCoordinateMetric (E := E) a
  let V : M×M → E := fun z => (e.symm (c z.1,c z.2)).2
  let f : M×M → ℝ := fun z => (τ^2/2)*g (c z.1) (V z) (V z)
  have heq : ∀ z ∈ Metric.ball a δ ×ˢ Metric.ball a δ, dist z.1 z.2^2/2 = f z := by
    rintro ⟨b,y⟩ ⟨hb,hy⟩
    have ht := htarget b hb y hy
    have hs := e.map_target ht
    have hi := e.right_inv ht
    have hfst : (e.symm (c b,c y)).1=c b := by
      have hh := congrArg Prod.fst hi
      rw [he] at hh
      exact hh
    have hpair : e.symm (c b,c y)=(c b,V (b,y)) := Prod.ext hfst rfl
    rw [hpair] at hs hi
    have hval : (Φ (τ,(c b,V (b,y)))).1=c y := by
      have hh := congrArg Prod.snd hi
      rw [he] at hh
      exact hh
    have hd := hdist b hb y hy (V (b,y)) hs hval
    have hnonneg : 0 ≤ g (c b) (V (b,y)) (V (b,y)) := by
      by_cases hv : V (b,y)=0
      · simp [hv]
      · exact (riemannianCoordinateMetric_positive (c.map_source (hsrc hb)) hv).le
    change dist b y^2/2 = (τ^2/2)*g (c b) (V (b,y)) (V (b,y))
    rw [hd,mul_pow,Real.sq_sqrt hnonneg]
    ring
  refine ⟨δ,hδ,?_⟩
  rintro z hz
  have hc₁ : ContMDiffAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ (fun z : M×M => c z.1) z :=
    (contMDiffAt_extChartAt' (I := 𝓘(ℝ,E)) (by simpa only [extChartAt_source] using hsrc hz.1)).comp z contMDiffAt_fst
  have hc₂ : ContMDiffAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ (fun z : M×M => c z.2) z :=
    (contMDiffAt_extChartAt' (I := 𝓘(ℝ,E)) (by simpa only [extChartAt_source] using hsrc hz.2)).comp z contMDiffAt_snd
  have heSnd : ContDiffAt ℝ ∞ (fun w : E×E => (e.symm w).2) (c z.1,c z.2) :=
    (hei.contDiffAt (e.open_target.mem_nhds (htarget z.1 hz.1 z.2 hz.2))).snd
  have heSndM : ContMDiffAt 𝓘(ℝ,E×E) 𝓘(ℝ,E) ∞
      (fun w : E×E => (e.symm w).2) (c z.1,c z.2) := heSnd.contMDiffAt
  have hV : ContMDiffAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) 𝓘(ℝ,E) ∞ V z :=
    heSndM.comp (f := fun z : M×M => (c z.1,c z.2)) z (hc₁.prodMk_space hc₂)
  have hg : ContMDiffAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) 𝓘(ℝ,E →L[ℝ] E →L[ℝ] ℝ) ∞
      (fun z : M×M => g (c z.1)) z :=
    ((contDiffOn_riemannianCoordinateMetric a).contDiffAt
      ((isOpen_extChartAt_target a).mem_nhds (c.map_source (hsrc hz.1)))).contMDiffAt.comp z hc₁
  have hf : ContMDiffAt (𝓘(ℝ,E).prod 𝓘(ℝ,E)) 𝓘(ℝ,ℝ) ∞ f z :=
    contMDiffAt_const.mul ((hg.clm_apply hV).clm_apply hV)
  exact ((hf.congr_of_eventuallyEq (Filter.eventuallyEq_of_mem
    ((Metric.isOpen_ball.prod Metric.isOpen_ball).mem_nhds hz) heq)).contMDiffWithinAt)

end WeakMTWTransport

end

end OAI

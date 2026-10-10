import Mathlib
import OAI.Analysis.SymmetricDomains.SemialgebraicChartBoundaryData
import OAI.Analysis.SymmetricDomains.NashNormalGraphBoundary

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Topology Metric MeasureTheory
open scoped Classical

def BoundaryOffsetData {s k : ℕ}
    (A : (Fin s → ℝ) → Set (Fin k → ℝ)) (B : Set (Fin s → ℝ))
    (x : Fin s → ℝ) : Prop :=
  (∃ r > 0, ∃ η > 0, ∃ ψ : (Fin s → ℝ) × ℝ → (Fin k → ℝ),
    ball x r ⊆ B ∧ AnalyticOnNhd ℝ ψ (ball x r ×ˢ ball 0 η) ∧
    (∀ y ∈ ball x r, ψ (y,0) = 0) ∧
    ∀ y ∈ ball x r, ∀ t ∈ Ioo (0 : ℝ) η, ψ (y,t) ∈ A y) ∧
  ∃ f : (Fin k → ℝ) → ℝ, LipschitzWith 1 f ∧
    (∀ y, f y ∈ Icc (0 : ℝ) 1) ∧
    (∀ y, Tendsto (fun p : (Fin s → ℝ) × ℝ => offsetDistance A p.1 p.2 y)
      (𝓝[{p : (Fin s → ℝ) × ℝ | 0 < p.2}] (x,0)) (𝓝 (f y))) ∧
    (∀ K : Set (Fin k → ℝ), IsCompact K →
      TendstoUniformlyOn (fun p : (Fin s → ℝ) × ℝ => offsetDistance A p.1 p.2) f
        (𝓝[{p : (Fin s → ℝ) × ℝ | 0 < p.2}] (x,0)) K) ∧
    IsClosed {y | f y = 0} ∧ (0 : Fin k → ℝ) ∈ {y | f y = 0} ∧
    ∀ c : ℝ, 0 < c → ∀ y, f y = 0 ↔ f (c • y) = 0

noncomputable def NashNormalCoordinates.realCoordinates {d m : ℕ}
    {B : Set (Fin d → ℝ)} {q : (Fin d → ℝ) → Affine m} {a : Fin d → ℝ}
    (c : NashNormalCoordinates B q a) :
    Affine m ≃L[ℝ] ((Fin ((c.tangentDim+c.tangentDim)+c.normalDim) → ℝ) × (Fin c.normalDim → ℝ)) :=
  (c.coordinates.toLinearEquiv.restrictScalars ℝ).toContinuousLinearEquiv.trans
    (complexGraphRealEquiv c.tangentDim c.normalDim)

noncomputable def ProjectionNashChart.coordinateDomain {N m s k : ℕ}
    {V : Set (Affine N)} {p : Affine N}
    (c : ProjectionNashChart V p m) (U : Set (Affine N))
    (e : Affine m ≃L[ℝ] ((Fin s → ℝ) × (Fin k → ℝ))) :
    Set ((Fin s → ℝ) × (Fin k → ℝ)) :=
  {z | ‖complexRealEquiv m (e.symm z)‖ < c.radius ∧ c.inverse (e.symm z) ∈ U}

structure NashBoundaryChart {d m N : ℕ} (U V : Set (Affine N))
    (B : Set (Fin d → ℝ)) (q : (Fin d → ℝ) → Affine N) where
  center : Fin d → ℝ
  center_mem : center ∈ B
  chart : ProjectionNashChart V (q center) m
  normal : NashNormalCoordinates B (fun x => chart.projection (q x-q center)) center
  graphRadius : ℝ
  graphRadius_pos : 0 < graphRadius
  graphRadius_le : graphRadius ≤ normal.radius
  domain_semialgebraic : PolynomialSignSet (fun z => Sum.elim z.1 z.2)
    (chart.coordinateDomain U normal.realCoordinates)
  graph_boundary : ∀ s ∈ ball 0 graphRadius,
    (s,normal.graph s) ∈ closure (chart.coordinateDomain U normal.realCoordinates) \
      (chart.coordinateDomain U normal.realCoordinates) ∧
    ‖complexRealEquiv m (normal.realCoordinates.symm (s,normal.graph s))‖ < chart.radius ∧
    chart.inverse (normal.realCoordinates.symm (s,normal.graph s)) = q (normal.parameters.symm s)

namespace NashBoundaryChart
variable {d m N : ℕ} {U V : Set (Affine N)} {B : Set (Fin d → ℝ)}
variable {q : (Fin d → ℝ) → Affine N}
noncomputable def family (c : NashBoundaryChart (m := m) U V B q) :=
  normalOffsetFamily (c.chart.coordinateDomain U c.normal.realCoordinates)
    (ball 0 c.graphRadius) c.normal.graph 1

def GoodAt (c : NashBoundaryChart (m := m) U V B q) (x : Fin d → ℝ) : Prop :=
  x ∈ c.normal.parameters.source ∧ c.normal.parameters x ∈ ball 0 c.graphRadius ∧
  BoundaryOffsetData c.family (ball 0 c.graphRadius) (c.normal.parameters x)

theorem null_bad_parameters (c : NashBoundaryChart (m := m) U V B q) :
    ∃ W : Set (Fin d → ℝ), IsOpen W ∧ c.center ∈ W ∧
      volume {x | x ∈ W ∧ ¬ c.GoodAt x} = 0 := by
  have hb : PolynomialSignSet id (ball (0 : Fin ((c.normal.tangentDim+c.normal.tangentDim)+c.normal.normalDim) → ℝ) c.graphRadius) := by
    simpa only [ball,dist_eq_norm] using polynomialSignSet_real_ball (0 : Fin ((c.normal.tangentDim+c.normal.tangentDim)+c.normal.normalDim) → ℝ) c.graphRadius
  have hφs := c.normal.graph_semialgebraic.mono hb (ball_subset_ball c.graphRadius_le)
  obtain ⟨E,hEB,hE,hdata⟩ := semialgebraic_chart_boundary_data
    (c.chart.coordinateDomain U c.normal.realCoordinates) c.domain_semialgebraic
    (ball 0 c.graphRadius) isOpen_ball hb c.normal.graph
    ((fun x hx => (c.normal.graph_analytic x (ball_subset_ball c.graphRadius_le hx)).continuousAt.continuousWithinAt) : ContinuousOn c.normal.graph (ball 0 c.graphRadius))
    hφs 1 zero_lt_one (fun s hs => (c.graph_boundary s hs).1)
  let W := c.normal.parameters.source ∩ c.normal.parameters ⁻¹' ball 0 c.graphRadius
  have hWo : IsOpen W := c.normal.parameters.isOpen_inter_preimage isOpen_ball
  have haW : c.center ∈ W := by
    refine ⟨c.normal.source_mem,?_⟩
    change c.normal.parameters c.center ∈ ball 0 c.graphRadius
    rw [c.normal.parameter_eq]
    simpa only [sub_self,map_zero,Prod.fst_zero] using (mem_ball_self (x :=
      (0 : Fin ((c.normal.tangentDim+c.normal.tangentDim)+c.normal.normalDim) → ℝ)) c.graphRadius_pos)
  have hnull : volume (c.normal.parameters.source ∩ c.normal.parameters ⁻¹' E) = 0 :=
    partial_homeomorph_preimage_null c.normal.real_dimension c.normal.parameters
      c.normal.inverse_analytic.differentiableOn
      (hEB.trans (ball_subset_ball c.graphRadius_le)) hE
  refine ⟨W,hWo,haW,measure_mono_null ?_ hnull⟩
  intro x hx
  refine ⟨hx.1.1,?_⟩
  by_contra hxE
  exact hx.2 ⟨hx.1.1,hx.1.2,hdata _ hx.1.2 hxE⟩
end NashBoundaryChart

def GoodNashBoundary {d N : ℕ} (m : ℕ) (U V : Set (Affine N))
    (B : Set (Fin d → ℝ)) (q : (Fin d → ℝ) → Affine N) (x : Fin d → ℝ) : Prop :=
  ∃ c : NashBoundaryChart (m := m) U V B q, c.GoodAt x
end Release061

end

end OAI

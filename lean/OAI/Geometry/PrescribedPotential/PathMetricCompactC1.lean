import Mathlib
import OAI.Geometry.PrescribedPotential.PathCoordinateC1

namespace OAI

/-! Path Metric Compact C1. -/

section

noncomputable section
open Set Filter Topology Matrix Metric
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace Anticanonical.SourceSmooth
open KaehlerCalculus EllipticKernel
variable {d : ℕ} {X : Type*} [TopologicalSpace X] [CompactSpace X] [ConnectedSpace X]
  {A : ComplexAtlas d X}

structure PathSolution (g : KaehlerMetric A) (h : SemipositiveAnticanonicalMetric A) where
  t : ℝ
  b : ℝ
  potential : SmoothRealFunction A
  time : t ∈ Icc 0 1
  solves : SolvesVolumePath g h t potential b
namespace PathSolution
variable {g : KaehlerMetric A} {h : SemipositiveAnticanonicalMetric A}
def metric (s : PathSolution g h) : KaehlerMetric A := g.deform s.potential s.solves.choose
end PathSolution

local instance compactC1RealIP : InnerProductSpace ℝ (EC d) := InnerProductSpace.rclikeToReal ℂ (EC d)

lemma path_metric_compact_C1 (g : KaehlerMetric A) (h : SemipositiveAnticanonicalMetric A)
    (i : Fin A.count) {K : Set (EC d)} (hK : IsCompact K)
    (hKU : K ⊆ (A.euclideanChart i).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : PathSolution g h) x, x ∈ K →
      ‖s.metric.matrix i (coordinateEquiv d x)‖ ≤ C ∧
      ‖fderiv ℝ (fun z k l => s.metric.matrix i z k l) (coordinateEquiv d x)‖ ≤ C := by
  classical
  have he (x : K) : ∃ p : CoordinateBall A, p.index = i ∧ x.val ∈ ball p.center p.radius := by
    obtain ⟨r,hr,hs⟩ := Metric.nhds_basis_closedBall.mem_iff.mp ((A.euclideanChart i).open_target.mem_nhds (hKU x.property))
    refine ⟨⟨i,x.val,r/4,by positivity,?_⟩,rfl,mem_ball_self (by positivity)⟩
    convert hs using 1; ring_nf
  choose p hp hx using he
  obtain ⟨S,hS⟩ := hK.elim_finite_subcover (fun x : K => ball (p x).center (p x).radius)
    (fun _ => isOpen_ball) (fun x hxK => mem_iUnion.mpr ⟨⟨x,hxK⟩,hx ⟨x,hxK⟩⟩)
  choose C hC hbound using fun x : K => (p x).path_coordinate_C1_bound g h
  refine ⟨∑ x ∈ S, C x,Finset.sum_nonneg (fun x _ => hC x),?_⟩
  intro s x hxK
  obtain ⟨q,hq,hxq⟩ := mem_iUnion₂.mp (hS hxK)
  have ht : x ∈ (A.euclideanChart (p q).index).target := (p q).ball_sub hxq
  let y := (A.euclideanChart (p q).index).symm x
  have hy : y ∈ (p q).source := ⟨(A.euclideanChart _).symm.mapsTo ht,by
    change A.euclideanChart _ ((A.euclideanChart _).symm x) ∈ ball _ _
    rw [(A.euclideanChart _).right_inv ht]
    exact hxq⟩
  have hz : A.chart (p q).index y = coordinateEquiv d x := by
    have hc := (A.euclideanChart (p q).index).right_inv ht
    change (coordinateEquiv d).symm (A.chart (p q).index y) = x at hc
    exact (coordinateEquiv d).symm.injective (hc.trans ((coordinateEquiv d).symm_apply_apply x).symm)
  have hb := hbound q s.t s.b s.potential s.time s.solves y hy
  rw [hz,hp q] at hb
  have hc := Finset.single_le_sum (fun x _ => hC x) hq
  exact ⟨hb.1.trans hc,hb.2.trans hc⟩
end Anticanonical.SourceSmooth

end
end

end OAI

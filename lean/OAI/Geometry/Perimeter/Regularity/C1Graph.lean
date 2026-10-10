import OAI.Geometry.Perimeter.Regularity.NeighborhoodPlanes
import OAI.Geometry.Perimeter.Regularity.GraphDerivative
import OAI.Geometry.Perimeter.Regularity.UniformDerivativeContinuity

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff InnerProductSpace
namespace RPISingularHarnack
variable {n : ℕ}

theorem c1_graph_from_contraction (hn : 1<n) {q M δ : ℝ}
    (hq : 0<q) (hq1 : q<1) (hM : 0≤M) (hstep : SlabContractionProperty n q M δ)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    {v : Euc n} (hv : ‖v‖=1) {a : ℝ} (ha : 0<a) (haδ : 4*a<δ)
    (ha4 : a<1/4) (haM : 8*M*a≤1/2) (hachord : a*(16*M+1/q)≤1/2)
    (hs : FullSlab E v 8 a) :
    ∃ f : normalPlane v → ℝ,
      ContDiffOn ℝ 1 f (Metric.ball 0 (1/4)) ∧
      (∀ y, ‖y‖<1/4 → |f y|≤a ∧ (y:Euc n)+f y•v∈perimeterSupport E ∩ Metric.ball 0 1) ∧
      (∀ y z, ‖y‖<1/4 → ‖z‖<1/4 → |f y-f z|≤‖y-z‖) ∧
      (∀ (y : normalPlane v) (t : ℝ), ‖y‖<1/4 → ‖(y:Euc n)+t•v‖<1 →
        ((y:Euc n)+t•v∈perimeterSupport E ↔ t=f y)) := by
  have hchord : ∀ p∈perimeterSupport E ∩ Metric.ball 0 1,
      ∀ x∈perimeterSupport E ∩ Metric.ball 0 1,
        |inner ℝ v (x-p)|≤(1/2)*‖x-p‖ := by
    intro p hp x hx
    exact (nearby_chord_bound hq hq1 hM hstep hmin hv ha haδ hs hp hx).trans
      (mul_le_mul_of_nonneg_right hachord (norm_nonneg _))
  obtain ⟨f,hf,hlip,hiff⟩ := single_graph_from_slab hn hmin hv ha.le ha4 hs hchord
  have hwex (y : normalPlane v) : ∃ w : Euc n, ‖y‖<1/4 →
      ‖w-v‖≤8*M*a ∧ ∀ j x, x∈perimeterSupport E → ‖x-((y:Euc n)+f y•v)‖≤2*q^j →
      |inner ℝ w (x-((y:Euc n)+f y•v))|≤4*a*(2*M+1/(4*q))*(1/2)^j*‖x-((y:Euc n)+f y•v)‖ := by
    by_cases hy : ‖y‖<1/4
    · obtain ⟨w,_,hwd,htan⟩ := nearby_full_support_planes hq hq1 hM hstep hmin hv ha haδ hs (hf y hy).2
      exact ⟨w,fun _ ↦ ⟨hwd,htan⟩⟩
    · exact ⟨v,fun h ↦ (hy h).elim⟩
  choose w hw using hwex
  let D : normalPlane v → normalPlane v →L[ℝ] ℝ := fun y ↦ graphTangentLinear v (w y)
  let C : ℝ := 16*a*(2*M+1/(4*q))
  have hrem : ∀ j y, y∈Metric.ball (0:normalPlane v) (1/4) →
      ∀ z, z∈Metric.ball (0:normalPlane v) (1/4) → ‖z-y‖≤q^j →
      |f z-f y-D y (z-y)|≤C*(1/2)^j*‖z-y‖ := by
    intro j y hy z hz hzy
    have hy' : ‖y‖<1/4 := by simpa only [Metric.mem_ball,dist_zero_right] using hy
    have hz' : ‖z‖<1/4 := by simpa only [Metric.mem_ball,dist_zero_right] using hz
    have hh := graph_tangent_remainder hv ((hw y hy').1.trans haM) (hf z hz').2.1
      (hlip z y hz' hy') hzy ((hw y hy').2 j) (by positivity : 0≤4*a*(2*M+1/(4*q)))
    convert hh using 1
    dsimp [C,D]
    ring
  have hD : ∀ y∈Metric.ball (0:normalPlane v) (1/4), HasFDerivAt f (D y) y := by
    intro y hy
    exact hasFDerivAt_of_geometric_remainder Metric.isOpen_ball hy hq (fun j z hz hzy ↦ hrem j y hy z hz hzy)
  have hDC := continuous_derivative_of_geometric_remainder Metric.isOpen_ball hq
    (fun x hx y hy ↦ hlip x y
      (by simpa only [Metric.mem_ball,dist_zero_right] using hx)
      (by simpa only [Metric.mem_ball,dist_zero_right] using hy)) hrem
  refine ⟨f,?_,hf,hlip,hiff⟩
  change ContDiffOn ℝ (0+1) f (Metric.ball 0 (1/4))
  rw [contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn Metric.isOpen_ball.uniqueDiffOn]
  refine ⟨by simp, D,?_,fun y hy ↦ (hD y hy).hasFDerivWithinAt⟩
  exact contDiffOn_zero.mpr (fun y hy ↦ (hDC y hy).continuousWithinAt)

end RPISingularHarnack

end

end OAI

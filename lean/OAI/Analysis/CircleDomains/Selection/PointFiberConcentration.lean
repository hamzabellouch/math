import OAI.Analysis.CircleDomains.Topology.ConcentratedCutoffs
import OAI.Analysis.CircleDomains.Rigidity.PriorityPointTrace

namespace OAI

/-! Closed inverse projections turn concentration of source supports into
concentration of the selected target values at every singleton fiber. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem closed_map_singleton_value_neighborhood
    {X Y : Type*} [TopologicalSpace X] [PseudoMetricSpace Y]
    {P : X → Y} (hP : IsClosedMap P) {p : X}
    (hfiber : P ⁻¹' {P p} = {p}) {a : X → ℝ} (ha : ContinuousAt a p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ z, dist (P z) (P p) < δ → ‖a z-a p‖ < ε := by
  have hn : a ⁻¹' ball (a p) ε ∈ 𝓝 p := ha.preimage_mem_nhds (ball_mem_nhds _ hε)
  obtain ⟨U, hUn, hU, hpU⟩ := mem_nhds_iff.mp hn
  have hV : IsOpen (kernImage P U) := isClosedMap_iff_kernImage.mp hP hU
  have hpV : P p ∈ kernImage P U := by
    intro z hz
    have hzmem : z ∈ P ⁻¹' {P p} := hz
    rw [hfiber] at hzmem
    simpa only [mem_singleton_iff.mp hzmem] using hpU
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hpV)
  refine ⟨δ, hδ, ?_⟩
  intro z hz
  have hzU : z ∈ U := hball hz rfl
  simpa only [mem_preimage, mem_ball, dist_eq_norm] using hUn hzU

 theorem closed_map_section_value_continuousAt
    {X Y : Type*} [TopologicalSpace X] [PseudoMetricSpace Y]
    {P : X → Y} (hP : IsClosedMap P) {p : X}
    (hfiber : P ⁻¹' {P p} = {p}) {a : X → ℝ} (ha : ContinuousAt a p)
    (s : Y → X) (hs : ∀ y, P (s y) = y) :
    ContinuousAt (a ∘ s) (P p) := by
  have hsp : s (P p) = p := by
    have hh : s (P p) ∈ P ⁻¹' {P p} := hs (P p)
    rwa [hfiber, mem_singleton_iff] at hh
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hnear⟩ := closed_map_singleton_value_neighborhood hP hfiber ha hε
  filter_upwards [ball_mem_nhds (P p) hδ] with y hy
  simpa only [comp_apply, hsp, dist_eq_norm] using hnear (s y) (by rwa [hs y])

 theorem concentrated_fiber_values
    {X Y : Type*} [TopologicalSpace X] [PseudoMetricSpace Y]
    {P : X → Y} (hP : IsClosedMap P) {p : X}
    (hfiber : P ⁻¹' {P p} = {p}) {a : X → ℝ} (ha : ContinuousAt a p)
    (z : ℕ → X) (b : ℕ → Y) (hz : ∀ n, P (z n) = b n)
    (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0))
    (χ : ℕ → Y → ℝ) (hs : ∀ n, support (χ n) ⊆ ball (b n) (r n)) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ᶠ y in 𝓝 (P p),
      ∀ n, N ≤ n → χ n y ≠ 0 → ‖a (z n)-a p‖ ≤ ε := by
  intro ε hε
  obtain ⟨δ, hδ, hnear⟩ := closed_map_singleton_value_neighborhood hP hfiber ha hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hr.eventually (gt_mem_nhds (show 0 < δ/2 by linarith)))
  refine ⟨N, ?_⟩
  filter_upwards [ball_mem_nhds (P p) (show 0 < δ/2 by linarith)] with y hy
  intro n hn hχ
  apply (hnear (z n) ?_).le
  rw [hz n]
  calc
    dist (b n) (P p) ≤ dist (b n) y+dist y (P p) := dist_triangle _ _ _
    _ < δ/2+δ/2 := add_lt_add (by simpa only [dist_comm] using (hs n hχ).trans (hN n hn)) hy
    _ = δ := by ring

 theorem priority_continuousAt_singleton_fiber
    {X Y : Type*} [TopologicalSpace X] [PseudoMetricSpace Y]
    {P : X → Y} (hP : IsClosedMap P) {p : X}
    (hfiber : P ⁻¹' {P p} = {p}) {a : X → ℝ} (ha : ContinuousAt a p)
    (z : ℕ → X) (b : ℕ → Y) (hz : ∀ n, P (z n) = b n)
    (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0))
    (χ : ℕ → Y → ℝ) (hs : ∀ n, support (χ n) ⊆ ball (b n) (r n))
    (hχc : ∀ n, ContinuousAt (χ n) (P p))
    (hχ : ∀ y n, χ n y ∈ Icc (0 : ℝ) 1)
    {B : ℝ} (hb : ∀ n, ‖a (z n)‖ ≤ B) {x : Y → ℝ}
    (hx : ContinuousAt x (P p)) (hxp : x (P p) = a p) :
    ContinuousAt (fun y => priorityInfiniteValue (fun n => χ n y) (fun n => a (z n)) (x y)) (P p) := by
  apply priorityInfiniteValue_continuousAt_point_trace χ (fun n => a (z n)) x hχc hχ hb hx
  rw [hxp]
  exact concentrated_fiber_values hP hfiber ha z b hz r hr χ hs

end CircleDomainRigidity

end

end OAI

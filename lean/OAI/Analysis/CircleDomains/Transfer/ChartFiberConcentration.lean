import OAI.Analysis.CircleDomains.Selection.PointFiberConcentration

namespace OAI

/-! Concentrating Euclidean supports control selected values through a
closed sphere projection. No comparison of chart and sphere metrics is
needed. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem concentrated_fiber_values_in_chart
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [PseudoMetricSpace Z]
    {P : X → Y} (hP : IsClosedMap P) (e : Z → Y) (he : Continuous e)
    {p : X} {q : Z} (_hpq : P p = e q) (hfiber : P ⁻¹' {e q} = {p})
    {a : X → ℝ} (ha : ContinuousAt a p)
    (z : ℕ → X) (b : ℕ → Z) (hz : ∀ n, P (z n) = e (b n))
    (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0))
    (χ : ℕ → Z → ℝ) (hs : ∀ n, support (χ n) ⊆ ball (b n) (r n)) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ᶠ y in 𝓝 q,
      ∀ n, N ≤ n → χ n y ≠ 0 → ‖a (z n)-a p‖ ≤ ε := by
  intro ε hε
  obtain ⟨U, hUnear, hU, hpU⟩ := mem_nhds_iff.mp
    (ha.preimage_mem_nhds (ball_mem_nhds _ hε))
  have hV : IsOpen (kernImage P U) := isClosedMap_iff_kernImage.mp hP hU
  have hqV : e q ∈ kernImage P U := by
    intro x hx
    have hx' : x ∈ P ⁻¹' {e q} := hx
    rw [hfiber, mem_singleton_iff] at hx'
    exact hx' ▸ hpU
  have hpre : e ⁻¹' kernImage P U ∈ 𝓝 q :=
    (hV.preimage he).mem_nhds hqV
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hpre
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hr.eventually (gt_mem_nhds (show 0 < δ/2 by linarith)))
  refine ⟨N, ?_⟩
  filter_upwards [ball_mem_nhds q (show 0 < δ/2 by linarith)] with y hy
  intro n hn hχ
  have hb : b n ∈ ball q δ := by
    calc
      dist (b n) q ≤ dist (b n) y+dist y q := dist_triangle _ _ _
      _ < δ/2+δ/2 := add_lt_add (by simpa only [dist_comm] using (hs n hχ).trans (hN n hn)) hy
      _ = δ := by ring
  have hzU : z n ∈ U := hball hb (hz n)
  exact (show ‖a (z n)-a p‖ < ε by
    simpa only [mem_preimage, mem_ball, dist_eq_norm] using hUnear hzU).le

 theorem priority_continuousAt_singleton_fiber_in_chart
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [PseudoMetricSpace Z]
    {P : X → Y} (hP : IsClosedMap P) (e : Z → Y) (he : Continuous e)
    {p : X} {q : Z} (hpq : P p = e q) (hfiber : P ⁻¹' {e q} = {p})
    {a : X → ℝ} (ha : ContinuousAt a p)
    (z : ℕ → X) (b : ℕ → Z) (hz : ∀ n, P (z n) = e (b n))
    (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 0))
    (χ : ℕ → Z → ℝ) (hs : ∀ n, support (χ n) ⊆ ball (b n) (r n))
    (hχc : ∀ n, ContinuousAt (χ n) q) (hχ : ∀ y n, χ n y ∈ Icc (0 : ℝ) 1)
    {K : ℝ} (hb : ∀ n, ‖a (z n)‖ ≤ K) {x : Z → ℝ}
    (hx : ContinuousAt x q) (hxq : x q = a p) :
    ContinuousAt (fun y => priorityInfiniteValue (fun n => χ n y) (fun n => a (z n)) (x y)) q := by
  apply priorityInfiniteValue_continuousAt_point_trace χ (fun n => a (z n)) x hχc hχ hb hx
  rw [hxq]
  exact concentrated_fiber_values_in_chart hP e he hpq hfiber ha z b hz r hr χ hs

end CircleDomainRigidity

end

end OAI

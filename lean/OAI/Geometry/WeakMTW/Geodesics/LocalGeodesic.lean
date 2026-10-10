import Mathlib
import OAI.Geometry.WeakMTW.Geodesics.UniformNormal
import OAI.Geometry.WeakMTW.Coordinates.NormalCurve
import OAI.Geometry.WeakMTW.Coordinates.CoordinateLocal

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff ENNReal Manifold
namespace RiemannianLocal
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ, E) x)]
  [IsRiemannianManifold 𝓘(ℝ, E) M]
open NormalNeighborhood NormalFlow ChartMetric CoordinateGeometry

 theorem coordinate_geodesic_locally_minimizes (x : M)
    {U : Set ℝ} (hU : IsOpen U) {q : ℝ → E × E}
    (hqsm : ContDiffOn ℝ ∞ q U)
    (hq : ∀ t ∈ U, (q t).1 ∈ (chartAt E x).target ∧
      HasDerivAt q (geodesicSpray (metric x) (q t)) t)
    {t₀ : ℝ} (ht₀ : t₀ ∈ U) :
    ∃ δ : ℝ, 0 < δ ∧ Metric.ball t₀ δ ⊆ U ∧
      ∀ s ∈ Metric.ball t₀ δ, ∀ r ∈ Metric.ball t₀ δ,
        dist ((chartAt E x).symm (q s).1) ((chartAt E x).symm (q r).1) =
          Real.sqrt (metric x (q t₀).1 (q t₀).2 (q t₀).2) * |s - r| := by
  let c := chartAt E x
  let γ : ℝ → M := fun t => c.symm (q t).1
  let z₀ := γ t₀
  have hz₀ : z₀ ∈ c.source := c.map_target (hq t₀ ht₀).1
  have hcz₀ : c z₀ = (q t₀).1 := c.right_inv (hq t₀ ht₀).1
  obtain ⟨N⟩ := exists_normalFlow c.open_target (metric_smooth x)
    (fun z hz v hv => metric_positive x hz hv) (c.map_source hz₀)
  obtain ⟨ε, R, hε, hR, hballs⟩ := uniform_normal_radius x z₀ hz₀ N
  have hqc : ContinuousAt q t₀ := ((hqsm t₀ ht₀).contDiffAt (hU.mem_nhds ht₀)).continuousAt
  have hγc : ContinuousAt γ t₀ := ContinuousAt.comp
    (g := (c.symm : E → M)) (f := fun t : ℝ => (q t).1)
    (c.symm.continuousAt (hq t₀ ht₀).1) hqc.fst
  obtain ⟨δU, hδU, hδUs⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds ht₀)
  obtain ⟨δγ, hδγ, hδγs⟩ := Metric.mem_nhds_iff.mp
    (hγc.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hε)))
  let F : ℝ × ℝ → E × E := fun p => ((q p.1).1, ((p.2 - p.1) / N.time) • (q p.1).2)
  have hFc : ContinuousAt F (t₀, t₀) := by
    have hq₁ := hqc.comp (continuousAt_fst : ContinuousAt (Prod.fst : ℝ × ℝ → ℝ) (t₀, t₀))
    exact hq₁.fst.prodMk (((continuousAt_snd.sub continuousAt_fst).div_const N.time).smul hq₁.snd)
  have hF₀ : F (t₀, t₀) ∈ N.normal.source := by simpa [F, hcz₀] using N.center_mem
  obtain ⟨δF, hδF, hδFs⟩ := Metric.mem_nhds_iff.mp
    (hFc.preimage_mem_nhds (N.normal.open_source.mem_nhds hF₀))
  let C : ℝ := Real.sqrt (metric x (q t₀).1 (q t₀).2 (q t₀).2)
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  let δL : ℝ := R / (4 * (C + 1))
  have hδL : 0 < δL := div_pos hR (by positivity)
  have hδLC : δL * (4 * (C + 1)) = R := div_mul_cancel₀ _ (by positivity : 4 * (C + 1) ≠ 0)
  let δ := min δU (min δγ (min δF δL))
  have hδ : 0 < δ := lt_min hδU (lt_min hδγ (lt_min hδF hδL))
  have hsubU : Metric.ball t₀ δ ⊆ U :=
    (Metric.ball_subset_ball (show δ ≤ δU from min_le_left _ _)).trans hδUs
  refine ⟨δ, hδ, hsubU, ?_⟩
  intro s hs r hr
  have hsU := hsubU hs
  have hsδU : s ∈ Metric.ball t₀ δU :=
    (Metric.ball_subset_ball (show δ ≤ δU from min_le_left _ _)) hs
  have hγs : γ s ∈ Metric.ball z₀ ε :=
    hδγs ((Metric.ball_subset_ball
      (show δ ≤ δγ from (min_le_right _ _).trans (min_le_left _ _))) hs)
  obtain ⟨hcs, hzeros, hballss⟩ := hballs (γ s) hγs
  have hcγs : c (γ s) = (q s).1 := c.right_inv (hq s hsU).1
  have hp : (s, r) ∈ Metric.ball (t₀, t₀) δF := by
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    exact ⟨lt_of_lt_of_le hs ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))),
      lt_of_lt_of_le hr ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))⟩
  have hFsr := hδFs hp
  let v : E := ((r - s) / N.time) • (q s).2
  have hv : v ∈ (N.normalAt (q s).1).source := hFsr
  have hvM : v ∈ (normalChart x (γ s) N).source := by
    rw [normalChart_source, hcγs]
    exact hv
  have hE : metric x (q s).1 (q s).2 (q s).2 = metric x (q t₀).1 (q t₀).2 (q t₀).2 :=
    geodesic_energy_on_connected c.open_target ((metric_smooth x).differentiableOn (by simp))
      (fun z _ => metric_symmetric x z) (fun z hz v hv => metric_positive x hz hv)
      Metric.isOpen_ball (convex_ball t₀ δU).isPreconnected
      (fun t ht => hq t (hδUs ht)) hsδU (Metric.mem_ball_self hδU)
  have hlen : N.time * Real.sqrt (metric x (c (γ s)) v v) = |r - s| * C := by
    rw [hcγs]
    dsimp only [v]
    rw [radial_scale_radius _ _ N.time_pos, hE]
  have hsmall : N.time * Real.sqrt (metric x (c (γ s)) v v) < R := by
    rw [hlen]
    have hsL : dist s t₀ < δL := lt_of_lt_of_le hs
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    have hrL : dist r t₀ < δL := lt_of_lt_of_le hr
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    have hd := dist_triangle r t₀ s
    rw [dist_comm t₀ s, Real.dist_eq] at hd
    have hmul : |r - s| * C ≤ (2 * δL) * C :=
      mul_le_mul_of_nonneg_right (by linarith) hC
    nlinarith
  have he := N.normal_rescaled_curve c.open_target (metric_smooth x)
    (fun z hz v hv => metric_positive x hz hv)
    (a := s) (b := (r - s) / N.time)
    (fun t ht => hq _ (hsubU (affine_time_mem_convex (convex_ball t₀ δ) hs hr N.time_pos ht))) hv
  have htend : s + (r - s) / N.time * N.time = r := by
    rw [div_mul_cancel₀ _ N.time_pos.ne']
    ring
  rw [htend] at he
  have hend : normalChart x (γ s) N v = γ r := by
    rw [normalChart_apply, hcγs, he]
  have hd := normal_distance_of_ball x (γ s) N hcs hzeros hR hballss hvM hsmall
  rw [hend, hlen] at hd
  calc
    _ = |r - s| * C := hd
    _ = _ := by rw [abs_sub_comm s r]; exact mul_comm _ _

end
end RiemannianLocal
end

end WeakMTWGlobalSupport

end OAI

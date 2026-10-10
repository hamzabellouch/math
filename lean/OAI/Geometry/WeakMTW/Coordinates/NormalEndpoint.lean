import Mathlib
import OAI.Geometry.WeakMTW.Geodesics.IntrinsicExp
import OAI.Geometry.WeakMTW.Coordinates.CoordinateIdentification

namespace OAI

namespace WeakMTWGlobalSupport

section

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold
namespace RiemannianLocal
 theorem open_interval_around_segment {S : Set ℝ} (hS : IsOpen S) {T : ℝ} (hT : 0 ≤ T)
    (hseg : Icc (0 : ℝ) T ⊆ S) :
    ∃ a b : ℝ, a < 0 ∧ T < b ∧ Ioo a b ⊆ S := by
  obtain ⟨a,c,hac,hacS⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hS.mem_nhds (hseg ⟨le_rfl,hT⟩))
  obtain ⟨d,b,hdb,hdbS⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hS.mem_nhds (hseg ⟨hT,le_rfl⟩))
  refine ⟨a,b,hac.1,hdb.2,?_⟩
  intro t ht
  by_cases h0 : 0 ≤ t
  · by_cases h1 : t ≤ T
    · exact hseg ⟨h0,h1⟩
    · exact hdbS ⟨hdb.1.trans (lt_of_not_ge h1),ht.2⟩
  · exact hacS ⟨ht.1,(lt_of_not_ge h0).trans hac.2⟩
end RiemannianLocal

namespace WeakMTW
noncomputable section
open RiemannianLocal NormalNeighborhood NormalFlow ChartMetric CoordinateGeometry
variable {n : ℕ} {M : Type*} [MetricSpace M] [ChartedSpace (Model n) M]
  [IsManifold (model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace (model n) x)]
  [IsContMDiffRiemannianBundle (model n) ∞ (Model n) (fun x : M => TangentSpace (model n) x)]
  [IsRiemannianManifold (model n) M] [CompactSpace M]

 theorem geodesic_normal_endpoint (x : M) {y₀ : Model n}
    (N : NormalFlow (metric x) (chartAt (Model n) x).target y₀)
    {y v : Model n} (hv : v ∈ (N.normalAt y).source) :
    geodesic ((stateChart (E := Model n) x).symm (y,v)) N.time =
      (chartAt (Model n) x).symm (N.normalAt y v) := by
  let c := chartAt (Model n) x
  let q : ℝ → Model n × Model n := fun t => N.flow (t,(y,v))
  let S : Set ℝ := {t | (t,(y,v)) ∈ N.domain}
  have hS : IsOpen S := N.domain_open.preimage (continuous_id.prodMk continuous_const)
  obtain ⟨a,b,ha,hb,hJ⟩ := open_interval_around_segment hS N.time_pos.le (N.source_stays (y,v) hv)
  let J := Ioo a b
  have h0J : (0 : ℝ) ∈ J := ⟨ha,lt_trans N.time_pos hb⟩
  have hTJ : N.time ∈ J := ⟨lt_trans ha N.time_pos,hb⟩
  have hqs : ContDiffOn ℝ ∞ q J := N.flow_smooth.comp
    (contDiffOn_id.prodMk contDiffOn_const) hJ
  have hqe : ∀ t ∈ J, (q t).1 ∈ c.target ∧ HasDerivAt q (geodesicSpray (metric x) (q t)) t :=
    fun t ht => N.ode _ (hJ ht)
  have hqzero : q 0 = (y,v) := N.initial _ (hJ h0J)
  have hh := geodesic_eq_coordinate x isOpen_Ioo (convex_Ioo a b).isPreconnected hqs hqe h0J
  rw [hqzero] at hh
  simpa only [q, N.normalAt_apply] using hh hTJ

 theorem locally_exists_minimizing_vector (z : M) :
    ∀ᶠ y in 𝓝 z, ∃ v : TangentSpace (model n) z, exp z v = y ∧ ‖v‖ = dist z y := by
  let c := chartAt (Model n) z
  have hz : z ∈ c.source := mem_chart_source (Model n) z
  obtain ⟨N⟩ := exists_normalFlow c.open_target (metric_smooth z)
    (fun x hx v hv => metric_positive z hx hv) (c.map_source hz)
  have ht : z ∈ (normalChart z z N).target := normalChart_target_center z z N hz N.center_mem
  have he := eventually_dist_normal z z N hz N.center_mem
  filter_upwards [(normalChart z z N).open_target.mem_nhds ht,he] with y hy hey
  let w := (normalChart z z N).symm y
  have hw : w ∈ (N.normalAt (c z)).source := by
    simpa only [normalChart_source] using (normalChart z z N).map_target hy
  let p := (stateChart (E := Model n) z).symm (c z,w)
  have hp : p.1 = z := by
    dsimp only [p]
    rw [stateChart_symm z (c.map_source hz)]
    exact c.left_inv hz
  have hnorm : Real.sqrt (metric z (c z) w w) = ‖p.2‖ := stateChart_energy z (q := (c z,w)) (c.map_source hz)
  have hgeo := geodesic_normal_endpoint z N hw
  rw [← exp_mul_eq_geodesic] at hgeo
  have hepy : exp p.1 (N.time • p.2) = y := by
    change exp p.1 (N.time • p.2) = _ at hgeo
    exact hgeo.trans ((normalChart z z N).right_inv hy)
  have hepn : ‖N.time • p.2‖ = dist z y := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos N.time_pos,← hnorm]
    exact hey.symm
  obtain ⟨z',v⟩ := p
  dsimp only at hp hepy hepn
  subst z'
  exact ⟨N.time • v,hepy,hepn⟩
end
end WeakMTW
end

end WeakMTWGlobalSupport

end OAI

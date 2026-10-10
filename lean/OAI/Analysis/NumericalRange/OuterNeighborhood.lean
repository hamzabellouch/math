import OAI.Analysis.NumericalRange.BoundaryNormals

namespace OAI

noncomputable section

namespace CompleteCrouzeix

universe u_28 u_29

open Complex Metric Set Filter Real
open scoped Topology ComplexConjugate
open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate
open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate
open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate
open Set Filter Metric
open scoped Topology
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex
open scoped Topology
open Set Metric Filter Topology
open Set Metric Filter Topology
open Set Filter Topology Complex
open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open Set Metric Filter Complex
open scoped Topology BigOperators ComplexConjugate
open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open Set Filter Metric Complex
open scoped Topology

section
open Set Filter Metric Complex
open scoped Topology ComplexConjugate

lemma exteriorCoordinate_analytic {U : Set ℂ} (E : ExteriorCoordinate U) :
    AnalyticOnNhd ℂ (exteriorMap E.leading E.constant E.regular)
      {t | E.radius⁻¹ < ‖t‖} := by
  intro t ht
  have hr : 0 < E.radius := zero_lt_one.trans E.radius_gt
  have ht0 : t ≠ 0 := by intro he; simp only [mem_ofPred_eq,he,norm_zero] at ht; exact (not_lt_of_ge (inv_nonneg.mpr hr.le)) ht
  have hi : t⁻¹ ∈ ball (0:ℂ) E.radius := by
    rw [mem_ball_zero_iff,norm_inv]
    exact (inv_lt_comm₀ (norm_pos_iff.mpr ht0) hr).mpr ht
  exact ((analyticAt_const.mul analyticAt_id).add analyticAt_const).add
    ((E.analytic_regular t⁻¹ hi).comp (analyticAt_id.inv ht0))

lemma barrier_exterior_coordinate {ι : Type u_28} [Fintype ι] {c : ℝ} (hc : 0 < c)
    (l : ι → ℂ →L[ℝ] ℝ) (b : ι → ℝ) {a : ℂ} (ha : convexBarrier c l b a < 1) :
    Nonempty (ExteriorCoordinate {z | convexBarrier c l b z < 1}) := by
  let U := {z | convexBarrier c l b z < 1}
  have hU : IsOpen U := convexBarrier_sublevel_open c l b
  have hcv : Convex ℝ U := convexBarrier_sublevel_convex hc.le l b
  have hcl : closure U = {z | convexBarrier c l b z ≤ 1} :=
    convexOn_closure_sublevel (convexBarrier_convex hc.le l b) (convexBarrier_continuous c l b) ha
  have hK : IsCompact (closure U) := isCompact_iff_isClosed_bounded.mpr
    ⟨isClosed_closure,hcl ▸ convexBarrier_sublevel_bounded hc l b⟩
  obtain ⟨D⟩ := barrier_exterior_disk_coordinate hc l b ha
  exact exteriorCoordinate_of_disk_inversion hU hK ha
    ((hcv.interior_closure_eq_interior_of_nonempty_interior (by rw [hU.interior_eq]; exact ⟨a,ha⟩)).trans hU.interior_eq) D

lemma barrier_exterior_support {ι : Type u_29} [Fintype ι] {c : ℝ} (hc : 0 < c)
    (l : ι → ℂ →L[ℝ] ℝ) (b : ι → ℝ) {a : ℂ} (ha : convexBarrier c l b a < 1)
    (E : ExteriorCoordinate {z | convexBarrier c l b z < 1}) :
    ∀ t ∈ sphere (0:ℂ) 1, ∀ z ∈ closure {z | convexBarrier c l b z < 1},
      0 ≤ (conj (t*deriv (exteriorMap E.leading E.constant E.regular) t)*
        (exteriorMap E.leading E.constant E.regular t-z)).re := by
  let q := convexBarrier c l b
  let G := exteriorMap E.leading E.constant E.regular
  have hr : 0 < E.radius := zero_lt_one.trans E.radius_gt
  have hri : E.radius⁻¹ < 1 := (inv_lt_one₀ hr).mpr E.radius_gt
  have hcl : closure {z | q z < 1} = {z | q z ≤ 1} :=
    convexOn_closure_sublevel (convexBarrier_convex hc.le l b) (convexBarrier_continuous c l b) ha
  have hb : ∀ t : ℂ, ‖t‖ = 1 → q (G t) = 1 := by
    intro t ht
    have hg : G t ∈ frontier {z | q z < 1} := E.boundary_image ▸ mem_image_of_mem G (mem_sphere_zero_iff_norm.mpr ht)
    dsimp [q] at hg ⊢
    simpa only [convexOn_frontier_sublevel (convexBarrier_convex hc.le l b)
      (convexBarrier_continuous c l b) ha,mem_ofPred_eq] using hg
  intro t ht z hz
  have htn := mem_sphere_zero_iff_norm.mp ht
  have htX : E.radius⁻¹ < ‖t‖ := by rwa [htn]
  apply analytic_convex_boundary_normal (convexBarrier_convex hc.le l b) htn
    (exteriorCoordinate_analytic E t htX).differentiableAt (E.noncritical t htX)
    (convexBarrier_analytic c l b (G t)).differentiableAt
    (convexBarrier_boundary_regular hc.le l b ha (hb t htn)) hb ?_ z (show q z ≤ 1 from (show z ∈ {z | q z ≤ 1} from hcl ▸ hz))
  have hrc : ContinuousAt (fun r : ℝ => ‖(r:ℂ)*t‖) 1 := by fun_prop
  have hnear : ∀ᶠ r : ℝ in 𝓝 1, E.radius⁻¹ < ‖(r:ℂ)*t‖ :=
    hrc.eventually (lt_mem_nhds (by simpa using htX))
  filter_upwards [hnear.filter_mono nhdsWithin_le_nhds,
    (lt_mem_nhds (zero_lt_one : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with r hrx hr0 hr1
  change r ≤ 1 at hr1
  by_cases hre : r = 1
  · subst r; simpa using (hb t htn).le
  · have hrlt : r < 1 := lt_of_le_of_ne hr1 hre
    have hball : (r:ℂ)*t ∈ ball (0:ℂ) 1 := by
      simp only [mem_ball_zero_iff,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr0,htn,mul_one]
      exact hrlt
    exact le_of_lt ((E.interior_iff _ hrx).mpr hball)

end

open Set Filter Metric Complex
open scoped Topology ComplexConjugate

structure AdmissibleDomain where
  domain : Set ℂ
  isOpen : IsOpen domain
  convex : Convex ℝ domain
  compact_closure : IsCompact (closure domain)
  base : ℂ
  base_mem : base ∈ domain
  interior : DiskCoordinate domain base
  exterior : ExteriorCoordinate domain
  support : ∀ t ∈ sphere (0:ℂ) 1, ∀ z ∈ closure domain,
    0 ≤ (conj (t*deriv (exteriorMap exterior.leading exterior.constant exterior.regular) t)*
      (exteriorMap exterior.leading exterior.constant exterior.regular t-z)).re

lemma exists_admissible_neighborhood {K U : Set ℂ} (hK : IsCompact K)
    (hne : K.Nonempty) (hcv : Convex ℝ K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ D : AdmissibleDomain, K ⊆ D.domain ∧ closure D.domain ⊆ U := by
  obtain ⟨N,c,l,b,hc,hsub,hout⟩ := exists_convex_barrier hK hne hcv hU hKU
  obtain ⟨a,ha⟩ := hne
  have haq := hsub a ha
  obtain ⟨D⟩ := barrier_interior_disk_coordinate hc l b haq
  obtain ⟨E⟩ := barrier_exterior_coordinate hc l b haq
  have hcl := convexOn_closure_sublevel (convexBarrier_convex hc.le l b)
    (convexBarrier_continuous c l b) haq
  refine ⟨⟨{z | convexBarrier c l b z < 1},convexBarrier_sublevel_open c l b,
    convexBarrier_sublevel_convex hc.le l b,
    isCompact_iff_isClosed_bounded.mpr ⟨isClosed_closure,hcl ▸ convexBarrier_sublevel_bounded hc l b⟩,
    a,haq,D,E,barrier_exterior_support hc l b haq E⟩,hsub,?_⟩
  change closure {z | convexBarrier c l b z < 1} ⊆ U
  simpa only [hcl] using hout


end CompleteCrouzeix

end

end OAI

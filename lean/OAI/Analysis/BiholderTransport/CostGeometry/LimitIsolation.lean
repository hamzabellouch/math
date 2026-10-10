import Mathlib
import OAI.Analysis.BiholderTransport.Contact.GraphCompact
import OAI.Analysis.BiholderTransport.CostGeometry.BranchActiveGrowth
import OAI.Analysis.BiholderTransport.Coordinates.CutCharacterization
import OAI.Analysis.BiholderTransport.Regularity.LimitGeometry

namespace OAI

noncomputable section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

namespace WeakMTWTransport
variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.isolated_graph_fiber_at_left_limit
    (hmtw : WeakMTW (n := n) (M := M)) {v : M → ℝ} (hv : Continuous v)
    {T : ℝ} (hT : 0<T) (hT1 : T<1)
    (hinj : ∀ t ∈ Ioo (0:ℝ) T, Function.Injective (graphProjection (n := n) (cTransform v) t))
    (z : subgradientGraph (n := n) (cTransform v)) :
    ∀ᶠ w in 𝓝 z, graphProjection (cTransform v) T w=graphProjection (cTransform v) T z → w=z := by
  have hglobal := graph_global_min_at_left_limit (continuous_cTransform hv) hT hinj
  have hmin (x : M) : ∀ p ∈ convexHull ℝ (activeLogs (n := n) v x), T • p ∈ minimizingVectors x := by
    intro p hp
    exact (hglobal ⟨⟨x,p⟩,active_hull_subset_normalSubdifferential hv x hp⟩).1
  have hp := normalSubdifferential_subset_active_hull hv z.1.1 z.2
  have hreg := hmtw.active_hull_nonconjugate_of_minimizing hT hT1 (hmin z.1.1) hp
  obtain ⟨G,hG,hagree⟩ := exists_smooth_cost_branch (tangentScale T z.1) hreg
  have hbranch := cost_branch_agrees_on_minimizing hG hagree
  have hbase := hmtw.active_hull_branch_strict_growth hv hp hT hT1
    (active_hull_interior_below_minimizing hT (hmin z.1.1)) hG hagree
  obtain ⟨U,hU,hzU,hUinj⟩ := joint_exp_locally_injective_of_nonconjugate (tangentScale T z.1) hreg
  have hscale : Continuous (fun w : subgradientGraph (n := n) (cTransform v) => tangentScale T w.1) :=
    contMDiff_tangentScale.continuous.comp (continuous_const.prodMk continuous_subtype_val)
  have hproj : Continuous (fun w : subgradientGraph (n := n) (cTransform v) => w.1.1) :=
    (FiberBundle.continuous_proj _ _).comp continuous_subtype_val
  have hcostz : cost z.1.1 (graphProjection (cTransform v) T z)=
      G (z.1.1,graphProjection (cTransform v) T z) :=
    hbranch.self_of_nhds (hglobal z).1
  filter_upwards [hscale.continuousAt.eventually hbranch,
    hscale.continuousAt.preimage_mem_nhds (hU.mem_nhds hzU),
    hproj.continuousAt.eventually hbase] with w hwG hwU hwbase he
  have hcostw : cost w.1.1 (graphProjection (cTransform v) T w)=
      G (w.1.1,graphProjection (cTransform v) T w) := hwG (hglobal w).1
  have hsame : w.1.1=z.1.1 := by
    by_contra hn
    have hlt := hwbase hn
    change cTransform v z.1.1+G (z.1.1,graphProjection (cTransform v) T z)/T <
      cTransform v w.1.1+G (w.1.1,graphProjection (cTransform v) T z)/T at hlt
    rw [he] at hcostw
    rw [←hcostz,←hcostw] at hlt
    have hle := (hglobal w).2 z.1.1
    rw [he] at hle
    exact (not_lt_of_ge hle) hlt
  apply Subtype.ext
  apply tangentScale_injective hT.ne'
  exact hUinj hwU hzU (Prod.ext hsame he)

lemma WeakMTW.injective_graphProjection_at_left_limit
    (hmtw : WeakMTW (n := n) (M := M)) {v : M → ℝ} (hv : Continuous v)
    {T : ℝ} (hT : 0<T) (hT1 : T<1)
    (hinj : ∀ t ∈ Ioo (0:ℝ) T, Function.Injective (graphProjection (n := n) (cTransform v) t)) :
    Function.Injective (graphProjection (n := n) (cTransform v) T) := by
  let : CompactSpace (subgradientGraph (n := n) (cTransform v)) :=
    isCompact_iff_compactSpace.mp (isCompact_subgradientGraph hv)
  let : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace (Model n) M
  let : T2Space (TangentBundle 𝓘(ℝ,Model n) M) := bundle_totalSpace_t2
  have hclosure : T ∈ closure {t | Function.Bijective (graphProjection (n := n) (cTransform v) t)} := by
    apply mem_closure_of_frequently_of_tendsto
      (f := fun t : ℝ => t) (b := 𝓝[<] T)
    · apply Filter.Eventually.frequently
      filter_upwards [(eventually_gt_nhds hT).filter_mono nhdsWithin_le_nhds,
        self_mem_nhdsWithin] with t ht htT
      exact ⟨hinj t ⟨ht,htT⟩,surjective_graphProjection (continuous_cTransform hv) ht⟩
    · exact tendsto_id.mono_right nhdsWithin_le_nhds
  intro z w he
  have hconn := isPreconnected_fiber_of_mem_closure_bijective
    (graphProjection (n := n) (cTransform v)) (continuous_graphProjection_family _) hclosure
    (graphProjection (cTransform v) T z)
  have hs : {q : subgradientGraph (n := n) (cTransform v) | graphProjection (cTransform v) T q=graphProjection (cTransform v) T z}.Subsingleton := by
    apply fiber_subsingleton_of_preconnected_isolated hconn
    intro q hq
    obtain ⟨U,hUP,hU,hqU⟩ := mem_nhds_iff.mp (hmtw.isolated_graph_fiber_at_left_limit hv hT hT1 hinj q)
    refine ⟨U,hU,hqU,?_⟩
    intro r hr
    exact hUP hr.1 (hr.2.trans hq.symm)
  exact hs rfl he.symm

lemma WeakMTW.active_hull_precut_at_left_limit
    (hmtw : WeakMTW (n := n) (M := M)) {v : M → ℝ} (hv : Continuous v)
    {T : ℝ} (hT : 0<T) (hT1 : T<1)
    (hinj : ∀ t ∈ Ioo (0:ℝ) T, Function.Injective (graphProjection (n := n) (cTransform v) t)) :
    ∀ x : M, ∀ p ∈ convexHull ℝ (activeLogs (n := n) v x), T • p ∈ injectivityDomain x := by
  have hTI := hmtw.injective_graphProjection_at_left_limit hv hT hT1 hinj
  have hglobal := global_min_of_injective_graphProjection (continuous_cTransform hv) hT hTI
  have hmin (x : M) : ∀ p ∈ convexHull ℝ (activeLogs (n := n) v x), T • p ∈ minimizingVectors x := by
    intro p hp
    exact (hglobal ⟨⟨x,p⟩,active_hull_subset_normalSubdifferential hv x hp⟩).1
  intro x p hp
  apply mem_injectivityDomain_of_nonconjugate_unique
    (hmtw.active_hull_nonconjugate_of_minimizing hT hT1 (hmin x) hp)
  intro q hq he
  let z : subgradientGraph (n := n) (cTransform v) :=
    ⟨⟨x,p⟩,active_hull_subset_normalSubdifferential hv x hp⟩
  exact unique_minimizing_direction_of_injective_graphProjection hT hTI z (hglobal z).2 hq he

end WeakMTWTransport

end

end OAI

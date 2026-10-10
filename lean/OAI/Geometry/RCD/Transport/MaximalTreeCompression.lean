import OAI.Geometry.RCD.Transport.MaximalCompressionChildren
import OAI.Geometry.RCD.Transport.RenyiTreeCompression

namespace OAI

/-! # The sharp uniform budget for any actual maximal tree

This estimate depends on endpoint density and transport length, not on a
pre-existing compression constant for the full ambient plan.
-/

open Set Filter MeasureTheory Metric TopologicalSpace
open scoped ENNReal Topology
noncomputable section
namespace RegularPointCoordinates
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem NoncollapsedRCD.maximal_tree_dyadic_compression
    (K : ℝ) (n : ℕ) (hn : 2≤n) (hX : NoncollapsedRCD K n X)
    {q : ℝ} (hq0 : 0<q) (hq1 : q<1) (m : ℕ) :
    ∀ (a : RenyiTransportNode n X) (π : Measure C(Time,X)) (_hπ : IsProbabilityMeasure π),
      (∀ᵐ γ ∂π, IsGeodesic γ) →
      IsOptimalCoupling a.left a.right (π.map (fun γ => (γ 0,γ 1))) →
      RenyiDyadicMaximal (hausdorff n X) q (fun t => π.map (fun γ => γ t)) m →
      ∀ t∈dyadicGrid m, π.map (fun γ => γ t)≤compressionBudget K n a.distance a.capacity • hausdorff n X := by
  let : SeparableSpace X := hX.separable
  let : CompleteSpace X := hX.complete
  induction m with
  | zero =>
    intro a π hπ hg hp hm t ht
    have he := optimalPlan_endpoints a.left a.right π hp
    have hb := le_compressionBudget K n a.distance a.capacity (Nat.cast_nonneg _) a.distance_nonneg
    rcases ht with rfl | ht
    · rw [he.1]
      exact a.left_bound.trans (by intro B; exact mul_le_mul' hb le_rfl)
    · have ht' : t=1 := ht
      subst t
      rw [he.2]
      exact a.right_bound.trans (by intro B; exact mul_le_mul' hb le_rfl)
  | succ m ih =>
    intro a π hπ hg hp hm t ht
    let := hπ
    let : Nonempty X := ⟨a.center⟩
    let := a.left_probability
    let := a.right_probability
    have he := optimalPlan_endpoints a.left a.right π hp
    have hr := hm.1
    dsimp only at hr
    rw [he.1,he.2] at hr
    obtain ⟨a₀,a₁,h00,h0m,h1m,h11,hd0,hd1,hc0,hc1⟩ :=
      hX.maximal_compression_children K n hn a π hg hp hq0 hq1 hr
    have hpp : IsOptimalCoupling (π.map (fun γ => γ 0)) (π.map (fun γ => γ 1))
        (π.map (fun γ => (γ 0,γ 1))) := by rw [he.1,he.2]; exact hp
    have hfin := finite_second_moment_cost
      (finiteSecondMoment_of_bounded a.left a.center a.left_support)
      (finiteSecondMoment_of_bounded a.right a.center a.right_support) hp.1 hp.2.1
    obtain ⟨hL,hgL,hpL⟩ := geodesic_subpath_law π hg hpp hfin 0 midpointTime
    obtain ⟨hR,hgR,hpR⟩ := geodesic_subpath_law π hg hpp hfin midpointTime 1
    have hpL' : IsOptimalCoupling a₀.left a₀.right
        ((π.map (subpath 0 midpointTime)).map (fun γ => (γ 0,γ 1))) := by rw [h00,h0m]; exact hpL
    have hpR' : IsOptimalCoupling a₁.left a₁.right
        ((π.map (subpath midpointTime 1)).map (fun γ => (γ 0,γ 1))) := by rw [h1m,h11]; exact hpR
    have hmL := hm.2.1.congr (fun s => (subpath_map_eval π 0 midpointTime s).symm)
    have hmR := hm.2.2.congr (fun s => (subpath_map_eval π midpointTime 1 s).symm)
    rcases ht with ⟨s,hs,rfl⟩ | ⟨s,hs,rfl⟩
    · have hh := ih a₀ _ hL hgL hpL' hmL s hs
      simpa only [subpath_map_eval,hd0,hc0,compressionBudget_halve] using hh
    · have hh := ih a₁ _ hR hgR hpR' hmR s hs
      simpa only [subpath_map_eval,hd1,hc1,compressionBudget_halve] using hh

theorem NoncollapsedRCD.maximal_tree_compression
    (K : ℝ) (n : ℕ) (hn : 2≤n) (hX : NoncollapsedRCD K n X)
    {q : ℝ} (hq0 : 0<q) (hq1 : q<1)
    (a : RenyiTransportNode n X) (π : Measure C(Time,X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling a.left a.right (π.map (fun γ => (γ 0,γ 1))))
    (hm : ∀ m, RenyiDyadicMaximal (hausdorff n X) q (fun t => π.map (fun γ => γ t)) m) :
    ∀ t, π.map (fun γ => γ t)≤compressionBudget K n a.distance a.capacity • hausdorff n X := by
  let : SeparableSpace X := hX.separable
  let : ProperSpace X := hX.proper K n hn
  let := a.left_probability
  let := a.right_probability
  let μ := hausdorff n X
  let B := closedBall a.center (3*a.radius)
  let : IsFiniteMeasure (μ.restrict B) := ⟨by
    simpa [μ,B] using hX.finiteOnBounded B isBounded_closedBall⟩
  let v : ProbabilityMeasure C(Time,X) := ⟨π,inferInstance⟩
  let cap := compressionBudget K n a.distance a.capacity
  have hcap : cap≠∞ := compressionBudget_ne_top K n a.distance a.capacity_finite
  have hs (t : Time) : ∀ᵐ x ∂π.map (fun γ => γ t), x∈B := by
    apply (ae_map_iff (measurable_path_eval t).aemeasurable measurableSet_closedBall).mpr
    exact (optimal_geodesic_plan_bounded a.left a.right π hg hp a.center a.radius_nonneg
      a.left_support a.right_support).mono (fun γ hγ => hγ.2 t)
  let T : Set Time := {t | π.map (fun γ => γ t)≤cap • μ.restrict B}
  have hT : IsClosed T := (isClosed_probability_domination (μ.restrict B) hcap).preimage
    (continuous_time_marginals v)
  have hd : (⋃ m, dyadicGrid m)⊆T := by
    intro t ht
    obtain ⟨m,htm⟩ := mem_iUnion.mp ht
    exact (compression_iff_localized μ _ (hs t) cap).mp
      (hX.maximal_tree_dyadic_compression K n hn hq0 hq1 m a π inferInstance hg hp (hm m) t htm)
  have hall := closure_minimal hd hT
  rw [dense_dyadicGrid.closure_eq] at hall
  exact fun t => (compression_iff_localized μ _ (hs t) cap).mpr (hall (mem_univ t))

end RegularPointCoordinates

end

end OAI

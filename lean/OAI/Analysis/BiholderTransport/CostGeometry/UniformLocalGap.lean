import Mathlib
import OAI.Analysis.BiholderTransport.Contact.GraphProjection
import OAI.Analysis.BiholderTransport.Coordinates.ActiveHullUniform

namespace OAI

noncomputable section

namespace WeakMTWTransport

section
open Set Filter Manifold Bundle
open scoped Topology ContDiff

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.uniform_local_scaled_gap
    (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {T : ℝ} (hT : T < 1)
    (hID : ∀ x : M, ∀ p ∈ convexHull ℝ (activeLogs (n := n) v x),
      ∀ t ∈ Icc (0:ℝ) T, t • p ∈ injectivityDomain x) :
    ∃ δ > 0, ∀ x z : M, dist x z < δ → x ≠ z →
      ∀ p ∈ convexHull ℝ (activeLogs (n := n) v x), ∀ t ∈ Icc (0:ℝ) T,
        0 < t * (cTransform v z-cTransform v x) +
          cost z (riemannianExp x (t • p)) - cost x (riemannianExp x (t • p)) := by
  have : IsContinuousRiemannianBundle (Model n)
      (fun x : M => TangentSpace 𝓘(ℝ,Model n) x) :=
    continuousRiemannianBundle_of_smooth (IB := 𝓘(ℝ,Model n))
  let P := fun z : TangentBundle 𝓘(ℝ,Model n) M =>
    ∀ p ∈ convexHull ℝ (activeLogs (n := n) v z.1), ∀ t ∈ Icc (0:ℝ) T,
      riemannianExp z.1 z.2 ≠ z.1 →
      0 < t * (cTransform v (riemannianExp z.1 z.2)-cTransform v z.1) +
        cost (riemannianExp z.1 z.2) (riemannianExp z.1 (t • p)) -
        cost z.1 (riemannianExp z.1 (t • p))
  have H : ∀ᶠ r : ℝ in 𝓝 0, ∀ z : TangentBundle 𝓘(ℝ,Model n) M,
      z.2 ∈ minimizingVectors z.1 → ‖z.2‖=r → P z := by
    apply compact_eventually_fiberwise (isCompact_total_minimizingVectors (n := n) (M := M))
      continuous_bundle_norm (continuousAt_id (x := (0:ℝ)))
    rintro ⟨a,q⟩ _ he
    have hq : q = 0 := norm_eq_zero.mp he
    subst q
    obtain ⟨K,hKn,hKa,hK⟩ := local_compact_nhds
      ((isOpen_extChartAt_source (I := 𝓘(ℝ,Model n)) a).mem_nhds (mem_extChartAt_source a))
    have HG := hmtw.active_hull_uniform_strict_growth hv hK hKa hT
      (fun x _ p hp t ht => hID x p hp t ht)
    let χ := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
      (⟨a,0⟩ : TangentBundle 𝓘(ℝ,Model n) M)
    have hχ0 : (χ (⟨a,0⟩ : TangentBundle 𝓘(ℝ,Model n) M)).2 = 0 :=
      map_zero (tangentCoordChange 𝓘(ℝ,Model n) a a a)
    have hc : Tendsto (fun q : ℝ × TangentBundle 𝓘(ℝ,Model n) M => (χ q.2).2)
        (𝓝 (0,⟨a,0⟩)) (𝓝 0) := by
      have hχ : ContinuousAt χ (⟨a,0⟩ : TangentBundle 𝓘(ℝ,Model n) M) := continuousAt_extChartAt _
      have hh := hχ.snd.comp
        (f := fun q : ℝ × TangentBundle 𝓘(ℝ,Model n) M => q.2) (x := (0,⟨a,0⟩)) continuousAt_snd
      convert hh.tendsto using 1 <;> simp only [Function.comp_def,hχ0]
    have hbase : ∀ᶠ q : ℝ × TangentBundle 𝓘(ℝ,Model n) M in 𝓝 (0,⟨a,0⟩), q.2.1 ∈ K :=
      ((FiberBundle.continuous_proj _ _).comp continuous_snd).continuousAt.preimage_mem_nhds hKn
    filter_upwards [hc.eventually HG,hbase] with q hG hqK p hp t ht hne
    have hm : movingNormal a (extChartAt 𝓘(ℝ,Model n) a q.2.1,(χ q.2).2) =
        riemannianExp q.2.1 q.2.2 := movingNormal_chart (hKa hqK) q.2.2
    have hn : (χ q.2).2 ≠ 0 := by
      intro hz
      rw [hz,movingNormal_zero ((extChartAt 𝓘(ℝ,Model n) a).map_source (hKa hqK)),
        (extChartAt 𝓘(ℝ,Model n) a).left_inv (hKa hqK)] at hm
      exact hne hm.symm
    have hh := hG q.2.1 hqK p hp t ht hn
    simpa only [hm] using hh
  obtain ⟨δ,hδ,Hδ⟩ := Metric.eventually_nhds_iff.mp H
  refine ⟨δ,hδ,?_⟩
  intro x z hxz hne p hp t ht
  obtain ⟨q,hq,hqz⟩ := exists_minimizing_vector (n := n) x z
  have hnq : ‖q‖ = dist x z := by rw [←hq,hqz]
  have hr : dist (dist x z) 0 < δ := by simpa only [Real.dist_eq,sub_zero,abs_of_nonneg dist_nonneg] using hxz
  have hh := Hδ hr ⟨x,q⟩ hq hnq p hp t ht (by rw [hqz]; exact hne.symm)
  simpa only [hqz] using hh

end

open Set Filter Manifold Bundle
open scoped Topology ContDiff

variable {n : ℕ} {M : Type*} [MetricSpace M] [CompactSpace M]
  [ChartedSpace (Model n) M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M]

lemma WeakMTW.uniform_graph_fiber_separation
    (hmtw : WeakMTW (n := n) (M := M))
    {v : M → ℝ} (hv : Continuous v) {T : ℝ} (hT : T < 1)
    (hID : ∀ x : M, ∀ p ∈ convexHull ℝ (activeLogs (n := n) v x),
      ∀ t ∈ Icc (0:ℝ) T, t • p ∈ injectivityDomain x) :
    ∃ δ > 0, ∀ t ∈ Ioc (0:ℝ) T,
      ∀ z w : subgradientGraph (n := n) (cTransform v),
        dist z.1.1 w.1.1 < δ →
        graphProjection (cTransform v) t z = graphProjection (cTransform v) t w → z = w := by
  obtain ⟨δ,hδ,Hδ⟩ := hmtw.uniform_local_scaled_gap hv hT hID
  refine ⟨δ,hδ,?_⟩
  rintro t ht ⟨⟨x,p⟩,hp⟩ ⟨⟨z,q⟩,hq⟩ hdist he
  have hpH := normalSubdifferential_subset_active_hull hv x hp
  have hqH := normalSubdifferential_subset_active_hull hv z hq
  change riemannianExp x (t • p) = riemannianExp z (t • q) at he
  have hxz : x = z := by
    by_contra hn
    have h1 := Hδ x z hdist hn p hpH t ⟨ht.1.le,ht.2⟩
    have h2 := Hδ z x (by rwa [dist_comm]) (Ne.symm hn) q hqH t ⟨ht.1.le,ht.2⟩
    rw [he] at h1
    linarith
  subst z
  have hpq : t • p = t • q := riemannianExp_injOn_injectivityDomain x
    (hID x p hpH t ⟨ht.1.le,ht.2⟩) (hID x q hqH t ⟨ht.1.le,ht.2⟩) he
  have hpq' : p = q := (smul_right_injective _ ht.1.ne') hpq
  subst q
  rfl

lemma graphProjection_base_dist {v : M → ℝ} (hv : Continuous v)
    {t : ℝ} (ht : 0 ≤ t) (z : subgradientGraph (n := n) (cTransform v)) :
    dist z.1.1 (graphProjection (cTransform v) t z) ≤ t * Metric.diam (univ : Set M) := by
  apply (dist_riemannianExp_le z.1.1 (t • z.1.2)).trans
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht]
  exact mul_le_mul_of_nonneg_left
    (active_hull_norm_le_diam (normalSubdifferential_subset_active_hull hv z.1.1 z.2)) ht

lemma WeakMTW.exists_short_injective_graphProjection
    (hmtw : WeakMTW (n := n) (M := M)) {v : M → ℝ} (hv : Continuous v) :
    ∃ τ > 0, τ < 1 ∧ ∀ t ∈ Ioc (0:ℝ) τ,
      Function.Injective (graphProjection (n := n) (cTransform v) t) := by
  obtain ⟨T,hT,hT1,H⟩ := exists_uniform_short_active_hull_contraction (n := n) (M := M)
  obtain ⟨δ,hδ,Hδ⟩ := hmtw.uniform_graph_fiber_separation hv hT1
    (fun x p hp t ht => H v x p hp t ht.1 ht.2)
  let D := Metric.diam (univ : Set M)
  have hD : 0 ≤ D := Metric.diam_nonneg
  let τ := min T (δ/(4*(D+1)))
  have hτ : 0 < τ := lt_min hT (div_pos hδ (by positivity))
  refine ⟨τ,hτ,(min_le_left _ _).trans_lt hT1,?_⟩
  intro t ht z w he
  apply Hδ t ⟨ht.1,ht.2.trans (min_le_left _ _)⟩ z w _ he
  have hz := graphProjection_base_dist hv ht.1.le z
  have hw := graphProjection_base_dist hv ht.1.le w
  rw [←he] at hw
  have hd := dist_triangle z.1.1 (graphProjection (cTransform v) t z) w.1.1
  rw [dist_comm (graphProjection (cTransform v) t z) w.1.1] at hd
  have htδ : t * (4*(D+1)) ≤ δ :=
    (le_div_iff₀ (by positivity : 0 < 4*(D+1))).mp (ht.2.trans (min_le_right _ _))
  change dist z.1.1 (graphProjection (cTransform v) t z) ≤ t*D at hz
  change dist w.1.1 (graphProjection (cTransform v) t z) ≤ t*D at hw
  nlinarith [mul_nonneg ht.1.le hD]

end WeakMTWTransport

end

end OAI

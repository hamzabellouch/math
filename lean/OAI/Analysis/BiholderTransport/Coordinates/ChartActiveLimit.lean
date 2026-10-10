import Mathlib
import OAI.Analysis.BiholderTransport.Regularity.GraphInverse
import OAI.Analysis.BiholderTransport.Regularity.ActiveLimit
import OAI.Analysis.BiholderTransport.Coordinates.GraphCoordinates

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

omit [Nonempty M] [IsManifold 𝓘(ℝ,Model n) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,Model n) ∞ (Model n)
    (fun x : M => TangentSpace 𝓘(ℝ,Model n) x)]
  [IsRiemannianManifold 𝓘(ℝ,Model n) M] in
lemma compact_in_chart_tail {x : ℕ → M} {a y : M} (hx : Tendsto x atTop (𝓝 y))
    (hy : y∈(extChartAt 𝓘(ℝ,Model n) a).source) :
    ∃ K : Set M,IsCompact K ∧ K⊆(extChartAt 𝓘(ℝ,Model n) a).source ∧
      ∃ N : ℕ,∀ k,x (k+N)∈K := by
  obtain ⟨r,hr,hs⟩ := Metric.isOpen_iff.mp (isOpen_extChartAt_source (I := 𝓘(ℝ,Model n)) a) y hy
  have hhalf : 0<r/2 := half_pos hr
  have he := hx.eventually (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hhalf))
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  exact ⟨Metric.closedBall y (r/2),isCompact_closedBall y (r/2),
    (Metric.closedBall_subset_ball (half_lt_self hr)).trans hs,N,
    fun k=>Metric.ball_subset_closedBall (hN (k+N) (Nat.le_add_left N k))⟩

lemma WeakMTW.graph_coordinate_limit_in_chart
    (hmtw : WeakMTW (n := n) (M := M)) {v : M → ℝ} (hv : Continuous v)
    {t : ℝ} (ht : 0<t) (ht1 : t<1)
    {q : ℕ → subgradientGraph (n := n) (cTransform v)}
    {q₀ : subgradientGraph (n := n) (cTransform v)}
    (hz : Tendsto (fun k=>graphProjection (cTransform v) t (q k)) atTop
      (𝓝 (graphProjection (cTransform v) t q₀)))
    {a : M} (ha : q₀.1.1∈(extChartAt 𝓘(ℝ,Model n) a).source) :
    Tendsto (fun k=>graphBaseCoordinate a (q k).1) atTop (𝓝 (graphBaseCoordinate a q₀.1)) ∧
    Tendsto (fun k=>graphVelocityCoordinate a (q k).1) atTop (𝓝 (graphVelocityCoordinate a q₀.1)) := by
  let χ := extChartAt (𝓘(ℝ,Model n).prod 𝓘(ℝ,Model n))
    (⟨a,0⟩ : TangentBundle 𝓘(ℝ,Model n) M)
  have hs : q₀.1∈χ.source := (tangent_chart_source_iff _ _).mpr ha
  have H := ((continuousOn_extChartAt _).continuousAt
    ((isOpen_extChartAt_source _).mem_nhds hs)).tendsto.comp
      (hmtw.graph_points_tendsto hv ht ht1 hz)
  exact ⟨H.fst_nhds,H.snd_nhds⟩

lemma WeakMTW.active_barycentric_limit_in_chart
    (hmtw : WeakMTW (n := n) (M := M)) {v : M → ℝ} (hv : Continuous v)
    {t : ℝ} (ht : 0<t) (ht1 : t<1)
    (q : ℕ → subgradientGraph (n := n) (cTransform v))
    (q₀ : subgradientGraph (n := n) (cTransform v))
    (hz : Tendsto (fun k=>graphProjection (cTransform v) t (q k)) atTop
      (𝓝 (graphProjection (cTransform v) t q₀)))
    {a : M} (ha : q₀.1.1∈(extChartAt 𝓘(ℝ,Model n) a).source)
    {K : Set M} (hK : IsCompact K) (hKa : K⊆(extChartAt 𝓘(ℝ,Model n) a).source)
    (hqK : ∀ k,(q k).1.1∈K) :
    ∃ pj : ℕ → Fin (Module.finrank ℝ (Model n)+1) → Model n,
    ∃ w : ℕ → Fin (Module.finrank ℝ (Model n)+1) → ℝ,
    ∃ p₀ : Fin (Module.finrank ℝ (Model n)+1) → Model n,
    ∃ w₀ : Fin (Module.finrank ℝ (Model n)+1) → ℝ,
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      (∀ k,(∀ i,(graphBaseCoordinate a (q k).1,pj k i)∈activeCoordinates v a K) ∧
        (∀ i,0≤w k i) ∧ ∑ i,w k i=1 ∧ ∑ i,w k i • pj k i=graphVelocityCoordinate a (q k).1) ∧
      Tendsto (pj ∘ σ) atTop (𝓝 p₀) ∧ Tendsto (w ∘ σ) atTop (𝓝 w₀) ∧
      (∀ i,(graphBaseCoordinate a q₀.1,p₀ i)∈activeCoordinates v a K) ∧ (∀ i,0≤w₀ i) ∧
      ∑ i,w₀ i=1 ∧ ∑ i,w₀ i • p₀ i=graphVelocityCoordinate a q₀.1 := by
  obtain ⟨hbase,hvel⟩ := hmtw.graph_coordinate_limit_in_chart hv ht ht1 hz ha
  have hrep : ∀ k,graphVelocityCoordinate a (q k).1∈convexHull ℝ
      {p | (graphBaseCoordinate a (q k).1,p)∈activeCoordinates v a K} := by
    intro k
    let L : TangentSpace 𝓘(ℝ,Model n) (q k).1.1 →ₗ[ℝ] Model n :=
      (tangentCoordChange 𝓘(ℝ,Model n) (q k).1.1 a (q k).1.1).toLinearMap
    have hh : L (q k).1.2 ∈ L '' convexHull ℝ (activeLogs v (q k).1.1) :=
      mem_image_of_mem L (normalSubdifferential_subset_active_hull hv _ (q k).2)
    rw [L.image_convexHull] at hh
    apply convexHull_mono (t := {p | (graphBaseCoordinate a (q k).1,p)∈activeCoordinates v a K}) ?_ hh
    rintro p ⟨r,hr,rfl⟩
    exact ⟨⟨(q k).1.1,r⟩,⟨hr,hqK k⟩,rfl⟩
  exact compact_barycentric_limit (isCompact_active_coordinates hv hK hKa) hbase hvel hrep

lemma WeakMTW.active_barycentric_tail_limit_in_chart
    (hmtw : WeakMTW (n := n) (M := M)) {v : M → ℝ} (hv : Continuous v)
    {t : ℝ} (ht : 0<t) (ht1 : t<1)
    (q : ℕ → subgradientGraph (n := n) (cTransform v))
    (q₀ : subgradientGraph (n := n) (cTransform v))
    (hz : Tendsto (fun k=>graphProjection (cTransform v) t (q k)) atTop
      (𝓝 (graphProjection (cTransform v) t q₀)))
    {a : M} (ha : q₀.1.1∈(extChartAt 𝓘(ℝ,Model n) a).source) :
    ∃ K : Set M,IsCompact K ∧ K⊆(extChartAt 𝓘(ℝ,Model n) a).source ∧
    ∃ pj : ℕ → Fin (Module.finrank ℝ (Model n)+1) → Model n,
    ∃ w : ℕ → Fin (Module.finrank ℝ (Model n)+1) → ℝ,
    ∃ p₀ : Fin (Module.finrank ℝ (Model n)+1) → Model n,
    ∃ w₀ : Fin (Module.finrank ℝ (Model n)+1) → ℝ,
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      (∀ k,(∀ i,(graphBaseCoordinate a (q (σ k)).1,pj k i)∈activeCoordinates v a K) ∧
        (∀ i,0≤w k i) ∧ ∑ i,w k i=1 ∧ ∑ i,w k i • pj k i=graphVelocityCoordinate a (q (σ k)).1) ∧
      Tendsto pj atTop (𝓝 p₀) ∧ Tendsto w atTop (𝓝 w₀) ∧
      (∀ i,(graphBaseCoordinate a q₀.1,p₀ i)∈activeCoordinates v a K) ∧ (∀ i,0≤w₀ i) ∧
      ∑ i,w₀ i=1 ∧ ∑ i,w₀ i • p₀ i=graphVelocityCoordinate a q₀.1 := by
  have hbase := (FiberBundle.continuous_proj (Model n)
    (TangentSpace 𝓘(ℝ,Model n))).tendsto q₀.1 |>.comp
      (hmtw.graph_points_tendsto hv ht ht1 hz)
  obtain ⟨K,hK,hKs,N,hN⟩ := compact_in_chart_tail hbase ha
  have hshift : Tendsto (fun k:ℕ=>k+N) atTop atTop := tendsto_add_atTop_nat N
  obtain ⟨pj,w,p₀,w₀,σ,hσ,hs,hp,hw,hact,hn,h1,hb⟩ :=
    hmtw.active_barycentric_limit_in_chart hv ht ht1 (fun k=>q (k+N)) q₀
      (hz.comp hshift) ha hK hKs hN
  exact ⟨K,hK,hKs,pj ∘ σ,w ∘ σ,p₀,w₀,fun k=>σ k+N,
    fun i j hij=>Nat.add_lt_add_right (hσ hij) N,fun k=>hs (σ k),hp,hw,hact,hn,h1,hb⟩

end WeakMTWTransport

end

end OAI

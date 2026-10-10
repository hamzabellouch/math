import Mathlib
import OAI.Analysis.BiholderTransport.LocalFlow.SmoothCoordinateFlow
import OAI.Analysis.BiholderTransport.Coordinates.NormalCoordinates
import OAI.Analysis.BiholderTransport.LocalFlow.LocalMetricNormal
import OAI.Analysis.BiholderTransport.Coordinates.TangentLift
import OAI.Analysis.BiholderTransport.Coordinates.FiberwiseHomeomorphism

namespace OAI

noncomputable section

open Set MeasureTheory Manifold Bundle
open scoped ContDiff Manifold ENNReal NNReal Topology

open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology

open Set Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology

open Set
open scoped Topology

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter ContinuousLinearMap InnerProductSpace
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff
open scoped NNReal

open Set Filter ContinuousLinearMap
open scoped Topology ContDiff

open Set Filter ContinuousLinearMap
open scoped Topology
open MeasureTheory
open scoped ContDiff ENNReal

open Set Filter Manifold Bundle ContinuousLinearMap MeasureTheory
open scoped Topology ContDiff Manifold Bundle ENNReal

open Set Filter Manifold MeasureTheory Bundle
open scoped ENNReal ContDiff Topology Manifold

open Set Filter Manifold Bundle ContinuousLinearMap
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Manifold Bundle
open scoped Topology ContDiff Manifold Bundle

open Set Filter Bundle
open scoped Topology Bundle

open scoped Topology
open Function Manifold Set
open Manifold Bundle
open scoped Manifold Bundle

namespace WeakMTWTransport

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma exists_joint_smooth_normal_chart
    {g : E → E →L[ℝ] E →L[ℝ] ℝ} {S : Set E} (hS : IsOpen S)
    (hg : ContDiffOn ℝ ∞ g S)
    (hpos : ∀ x ∈ S, ∀ v : E, v ≠ 0 → 0 < g x v v)
    (hsym : ∀ x ∈ S, ∀ u v, g x u v = g x v u)
    {x : E} (hx : x ∈ S) :
    ∃ r : ℝ, 0 < r ∧ ∃ Φ : ℝ × (E × E) → E × E,
      ContDiffOn ℝ ∞ Φ (Ioo (-r) r ×ˢ Metric.ball (x,0) r) ∧
      (∀ z ∈ Metric.ball (x,0) r, Φ (0,z) = z) ∧
      (∀ t ∈ Ioo (-r) r, ∀ z ∈ Metric.ball (x,0) r,
        (Φ (t,z)).1 ∈ S ∧
        HasDerivAt (fun q => (Φ (q,z)).1) (Φ (t,z)).2 t ∧
        HasDerivAt (fun q => (Φ (q,z)).2)
          (-coordinateChristoffel g (Φ (t,z)).1 (Φ (t,z)).2 (Φ (t,z)).2) t) ∧
      ∃ τ : ℝ, 0 < τ ∧ τ < r ∧ ∃ e : OpenPartialHomeomorph (E × E) (E × E),
        (e : (E × E) → (E × E)) = (fun z => (z.1,(Φ (τ,z)).1)) ∧
        (x,0) ∈ e.source ∧
        e.source ⊆ Metric.ball (x,0) r ∧
        ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  have hi : ∀ y ∈ S, (g y).IsInvertible :=
    fun y hy => metricDual_isInvertible (g y) (hpos y hy)
  obtain ⟨r,hr,Φ,hΦ,hΦ0,hΦode⟩ := exists_smooth_coordinate_flow hS hg hi x 0 hx
  have hball : ∀ v ∈ Metric.ball (0:E) r, (x,v) ∈ Metric.ball (x,0) r := by
    intro v hv
    simpa only [Metric.mem_ball,Prod.dist_eq,dist_self,max_lt_iff] using And.intro hr hv
  have hΦc : ContDiffOn ℝ ∞ (fun z : ℝ × E => Φ (z.1,(x,z.2)))
      (Ioo (-r) r ×ˢ Metric.ball 0 r) :=
    hΦ.comp (contDiffOn_fst.prodMk (contDiffOn_const.prodMk contDiffOn_snd))
      (fun z hz => ⟨hz.1,hball z.2 hz.2⟩)
  have h0 : (0:ℝ) ∈ Ioo (-r) r := ⟨neg_neg_of_pos hr,hr⟩
  have hτ : r/2 ∈ Ioo (-r) r := ⟨by linarith,by linarith⟩
  have hinv := coordinate_endpoint_isInvertible (x := x) hS hg hpos hsym hr hΦc.fst hΦc.snd
    (fun t ht v hv => (hΦode t ht (x,v) (hball v hv)).1)
    (fun t ht v hv => (hΦode t ht (x,v) (hball v hv)).2)
    h0 (fun v hv => congrArg Prod.fst (hΦ0 (x,v) (hball v hv)))
    (fun v hv => congrArg Prod.snd (hΦ0 (x,v) (hball v hv)))
    hτ (by linarith : r/2 ≠ 0)
  have hψ : ContDiffOn ℝ ∞ (fun z => (Φ (r/2,z)).1) (Metric.ball (x,0) r) :=
    (hΦ.comp (contDiffOn_const.prodMk contDiffOn_id) (fun z hz => ⟨hτ,hz⟩)).fst
  have hψa := (hψ.contDiffAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))).differentiableAt
    (by simp)
  have hinv' := first_coordinate_preserving_derivative_invertible hψa hinv
  obtain ⟨e,he,hes,hesub,hed,hei⟩ := exists_smooth_local_diffeomorphism
    Metric.isOpen_ball (contDiffOn_fst.prodMk hψ) (Metric.mem_ball_self hr) hinv'
  exact ⟨r,hr,Φ,hΦ,hΦ0,hΦode,r/2,by positivity,hτ.2,e,he,hes,hesub,hed,hei⟩

end
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  {M : Type*} [MetricSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ,E) ∞ E (fun x : M => TangentSpace 𝓘(ℝ,E) x)]
  [IsRiemannianManifold 𝓘(ℝ,E) M]

lemma exists_uniform_metric_normal_coordinates (a : M) :
    ∃ δ r τ : ℝ, 0 < δ ∧ 0 < r ∧ 0 < τ ∧ τ < r ∧
    ∃ Φ : ℝ × (E × E) → E × E,
    ∃ e : OpenPartialHomeomorph (E × E) (E × E),
      ContDiffOn ℝ ∞ Φ (Ioo (-r) r ×ˢ Metric.ball (extChartAt 𝓘(ℝ,E) a a,0) r) ∧
      (∀ z ∈ Metric.ball (extChartAt 𝓘(ℝ,E) a a,0) r, Φ (0,z) = z) ∧
      (∀ t ∈ Ioo (-r) r, ∀ z ∈ Metric.ball (extChartAt 𝓘(ℝ,E) a a,0) r,
        (Φ (t,z)).1 ∈ (extChartAt 𝓘(ℝ,E) a).target ∧
        HasDerivAt (fun q => Φ (q,z))
          (coordinateGeodesicField (riemannianCoordinateMetric a) (Φ (t,z))) t) ∧
      (e : (E × E) → (E × E)) = (fun z => (z.1,(Φ (τ,z)).1)) ∧
      e.source ⊆ Metric.ball (extChartAt 𝓘(ℝ,E) a a,0) r ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      (Metric.ball a δ ⊆ (extChartAt 𝓘(ℝ,E) a).source) ∧
      (∀ b ∈ Metric.ball a δ, (extChartAt 𝓘(ℝ,E) a b,0) ∈ e.source) ∧
      (∀ b ∈ Metric.ball a δ, ∀ y ∈ Metric.ball a δ,
        (extChartAt 𝓘(ℝ,E) a b,extChartAt 𝓘(ℝ,E) a y) ∈ e.target) ∧
      (∀ b ∈ Metric.ball a δ, ∀ y ∈ Metric.ball a δ, ∀ v : E,
        (extChartAt 𝓘(ℝ,E) a b,v) ∈ e.source →
        (Φ (τ,(extChartAt 𝓘(ℝ,E) a b,v))).1 = extChartAt 𝓘(ℝ,E) a y →
        dist b y = τ * Real.sqrt (riemannianCoordinateMetric a
          (extChartAt 𝓘(ℝ,E) a b) v v)) := by
  let c := extChartAt 𝓘(ℝ,E) a
  let g := riemannianCoordinateMetric (E := E) a
  have hS : IsOpen c.target := isOpen_extChartAt_target a
  have hg : ContDiffOn ℝ ∞ g c.target := contDiffOn_riemannianCoordinateMetric a
  have hpos : ∀ x ∈ c.target, ∀ v : E, v ≠ 0 → 0 < g x v v :=
    fun _ hx _ hv => riemannianCoordinateMetric_positive hx hv
  have hsym : ∀ x ∈ c.target, ∀ u v : E, g x u v = g x v u :=
    fun x _ u v => riemannianCoordinateMetric_symm a x u v
  obtain ⟨r,hr,Φ,hΦ,hΦ0,hode,τ,hτ,hτr,e,he,hes,hesub,hed,hei⟩ :=
    exists_joint_smooth_normal_chart hS hg hpos hsym (mem_extChartAt_target a)
  have h0 : (0:ℝ) ∈ Ioo (-r) r := ⟨by linarith,hr⟩
  have ht : τ ∈ Ioo (-r) r := ⟨by linarith,hτr⟩
  have hepres : ∀ z : E × E, (e z).1 = z.1 := by
    intro z
    rw [he]
  have hzero : ∀ x ∈ Metric.ball (c a) r, (Φ (τ,(x,0))).1 = x := by
    intro x hx
    have hz : (x,(0:E)) ∈ Metric.ball (c a,0) r := by
      simpa only [Metric.mem_ball,Prod.dist_eq,dist_self,max_lt_iff] using And.intro hx hr
    have hz0 := hΦ0 (x,0) hz
    have hh := coordinate_geodesic_zero_velocity
      (fun t ht => (hg.contDiffAt (hS.mem_nhds (hode t ht (x,0) hz).1)).differentiableAt (by simp))
      (fun t ht => metricDual_isInvertible _ (hpos _ (hode t ht (x,0) hz).1))
      (fun t ht => hpos _ (hode t ht (x,0) hz).1)
      (fun t ht => hsym _ (hode t ht (x,0) hz).1)
      (fun t ht => (hode t ht (x,0) hz).2) h0
      (show (Φ (0,(x,0))).2 = 0 from congrArg Prod.snd hz0) ht
    exact hh.1.trans (congrArg Prod.fst hz0)
  have hediag : e (c a,0) = (c a,c a) := by
    rw [he]
    exact Prod.ext rfl (hzero _ (Metric.mem_ball_self hr))
  have hat : (c a,c a) ∈ e.target := hediag ▸ e.map_source hes
  have hc : ContinuousAt c a := continuousAt_extChartAt a
  have hn₁ : {p : M × M | p.1 ∈ c.source ∧ p.2 ∈ c.source} ∈ 𝓝 (a,a) :=
    inter_mem (continuousAt_fst.preimage_mem_nhds ((isOpen_extChartAt_source a).mem_nhds (mem_extChartAt_source a)))
      (continuousAt_snd.preimage_mem_nhds ((isOpen_extChartAt_source a).mem_nhds (mem_extChartAt_source a)))
  have hn₂ : {p : M × M | (c p.1,0) ∈ e.source} ∈ 𝓝 (a,a) :=
    ((hc.comp continuousAt_fst).prodMk continuousAt_const).preimage_mem_nhds
      (e.open_source.mem_nhds hes)
  have hn₃ : {p : M × M | (c p.1,c p.2) ∈ e.target} ∈ 𝓝 (a,a) :=
    ((hc.comp continuousAt_fst).prodMk (hc.comp continuousAt_snd)).preimage_mem_nhds
      (e.open_target.mem_nhds hat)
  obtain ⟨R,hR,hgood⟩ := Metric.mem_nhds_iff.mp (inter_mem hn₁ (inter_mem hn₂ hn₃))
  have hgood' : ∀ b ∈ Metric.ball a R, ∀ y ∈ Metric.ball a R,
      b ∈ c.source ∧ y ∈ c.source ∧ (c b,0) ∈ e.source ∧ (c b,c y) ∈ e.target := by
    intro b hb y hy
    have hh := hgood (show (b,y) ∈ Metric.ball (a,a) R by
      simpa only [Metric.mem_ball,Prod.dist_eq,max_lt_iff] using And.intro hb hy)
    exact ⟨hh.1.1,hh.1.2,hh.2.1,hh.2.2⟩
  let δ := R/4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδR : δ < R := by dsimp [δ]; linarith
  have hballR : Metric.ball a δ ⊆ Metric.ball a R := Metric.ball_subset_ball hδR.le
  refine ⟨δ,r,τ,hδ,hr,hτ,hτr,Φ,e,hΦ,hΦ0,?_,he,hesub,hed,hei,?_,?_,?_,?_⟩
  · intro t ht z hz
    exact ⟨(hode t ht z hz).1,(hode t ht z hz).2.1.prodMk (hode t ht z hz).2.2⟩
  · intro b hb
    exact (hgood' b (hballR hb) a (Metric.mem_ball_self hR)).1
  · intro b hb
    exact (hgood' b (hballR hb) a (Metric.mem_ball_self hR)).2.2.1
  · intro b hb y hy
    exact (hgood' b (hballR hb) y (hballR hy)).2.2.2
  · intro b hb y hy v hv hval
    let f := fiberwiseHomeomorph e hepres (c b)
    have hbg := hgood' b (hballR hb) a (Metric.mem_ball_self hR)
    have hcb : c b ∈ Metric.ball (c a) r := by
      exact (max_lt_iff.mp (show max (dist (c b) (c a)) (dist (0:E) 0) < r
        from hesub hbg.2.2.1)).1
    have hball : ∀ w ∈ Metric.ball (0:E) r, (c b,w) ∈ Metric.ball (c a,0) r := by
      intro w hw
      simpa only [Metric.mem_ball,Prod.dist_eq,max_lt_iff] using And.intro hcb hw
    have hΦb : ContDiffOn ℝ ∞ (fun z : ℝ × E => Φ (z.1,(c b,z.2)))
        (Ioo (-r) r ×ˢ Metric.ball 0 r) :=
      hΦ.comp (contDiffOn_fst.prodMk (contDiffOn_const.prodMk contDiffOn_snd))
        (fun z hz => ⟨hz.1,hball z.2 hz.2⟩)
    have hf : (f : E → E) = (fun w => (Φ (τ,(c b,w))).1) := by
      funext w
      change (e (c b,w)).2 = _
      rw [he]
    have hfb : Metric.ball b (2*δ) ⊆ c.source ∩ c ⁻¹' f.target := by
      intro z hz
      have hzR : z ∈ Metric.ball a R := by
        have ht' := dist_triangle z b a
        have hb' : dist b a < δ := hb
        have hz' : dist z b < 2*δ := hz
        change dist z a < R
        dsimp [δ] at *
        linarith
      have hh := hgood' b (hballR hb) z hzR
      exact ⟨hh.2.1,hh.2.2.2⟩
    have hby : dist b y < 2*δ := by
      have ht' := dist_triangle b a y
      have hb' : dist b a < δ := hb
      have hy' : dist a y < δ := by simpa only [Metric.mem_ball,dist_comm] using hy
      linarith
    have hnorm := riemannian_coordinate_normal_chart_dist hS hg hpos hsym (Subset.refl _)
      (fun _ _ _ _ => rfl) hΦb.fst hΦb.snd
      (fun t ht w hw => (hode t ht (c b,w) (hball w hw)).1)
      (fun t ht w hw => (hode t ht (c b,w) (hball w hw)).2) h0
      (fun w hw => (congrArg Prod.fst (hΦ0 (c b,w) (hball w hw)) : _ = c b))
      (fun w hw => congrArg Prod.snd (hΦ0 (c b,w) (hball w hw))) ht hτ.le f hf
      (by rw [hf]; exact hzero _ hcb) hbg.2.2.1
      (fun w hw => (max_lt_iff.mp (show max (dist (c b) (c a)) (dist w 0) < r
        from hesub hw)).2)
      (fiberwiseHomeomorph_contDiffOn hepres (c b) hed)
      (fiberwiseHomeomorph_symm_contDiffOn hepres (c b) hei) hfb hby
    have hv' : f.symm (c y) = v := by
      have hfval : f v = c y := by rw [hf]; exact hval
      rw [←hfval]
      exact f.left_inv hv
    rw [hv'] at hnorm
    exact hnorm

end WeakMTWTransport
open Set

end

end OAI

import OAI.Geometry.NodalSets.Elliptic.QuadraticFamily

namespace OAI

noncomputable section

namespace Yau.Geometry

section

open Filter
open scoped ContDiff Topology
open Yau.Jets
attribute [local instance] clmTopology clmAdd clmModule

lemma actual_connection_symmetric (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (hg : ContDiff ℝ ∞ g) (hs : ∀ x u v, g x u v = g x v u)
    (hp : ∀ x v, v ≠ 0 → 0 < g x v v) (y u v : Coord) :
    metricConnection (g y) (fderiv ℝ g y) u v = metricConnection (g y) (fderiv ℝ g y) v u := by
  rw [metricConnection_eq (g y) (hp y)]
  exact christoffelTensor_symmetric _ _
    (metric_derivative_symmetric g _ y (hg.differentiable (by simp) y).hasFDerivAt hs) u v

lemma actual_connection_cancel (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (hg : ContDiff ℝ ∞ g) (hs : ∀ x u v, g x u v = g x v u)
    (hp : ∀ x v, v ≠ 0 → 0 < g x v v) (y w u v : Coord) :
    fderiv ℝ g y w u v =
      g y (metricConnection (g y) (fderiv ℝ g y) w u) v +
      g y u (metricConnection (g y) (fderiv ℝ g y) w v) := by
  rw [metricConnection_eq (g y) (hp y)]
  exact christoffelTensor_cancel (positiveMetricEquiv (g y) (hp y)) (hs y) _
    (metric_derivative_symmetric g _ y (hg.differentiable (by simp) y).hasFDerivAt hs) w u v

def actualFrameConnection (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (y : Coord) (e : Coord ≃L[ℝ] Coord) : Coord →L[ℝ] Coord →L[ℝ] Coord :=
  frameConnection (metricConnection (g y) (fderiv ℝ g y)) e

def actualMetricChart (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (y : Coord) (e : Coord ≃L[ℝ] Coord) : OpenPartialHomeomorph Coord Coord :=
  quadraticChart y e (actualFrameConnection g y e)

lemma actualMetricChart_metric_first_zero (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (hg : ContDiff ℝ ∞ g) (hs : ∀ x u v, g x u v = g x v u)
    (hp : ∀ x v, v ≠ 0 → 0 < g x v v) (y : Coord) (e : Coord ≃L[ℝ] Coord) (u v : Coord) :
    fderiv ℝ (fun x ↦ pullbackMetric g (actualMetricChart g y e) x u v) 0 = 0 := by
  exact quadratic_chart_metric_first_zero g _ y (hg.differentiable (by simp) y).hasFDerivAt e _
    (fun u v ↦ actual_connection_symmetric g hg hs hp y (e u) (e v))
    (fun w u v ↦ actual_connection_cancel g hg hs hp y (e w) (e u) (e v)) u v

variable {T : Type*} [TopologicalSpace T]

lemma actualFrameConnection_continuous (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ)
    (hg : ContDiff ℝ ∞ g) (hp : ∀ x v, v ≠ 0 → 0 < g x v v)
    (y : T → Coord) (hy : Continuous y) (e : T → Coord ≃L[ℝ] Coord)
    (he : Continuous (fun t ↦ (e t).toContinuousLinearMap)) :
    Continuous (fun t ↦ actualFrameConnection g (y t) (e t)) :=
  frameConnection_continuous _ _ ((smooth_metric_connection_continuous g hg hp).comp hy) he

theorem exists_actual_adapted_chart_family
    (g : Coord → Coord →L[ℝ] Coord →L[ℝ] ℝ) (hg : ContDiff ℝ ∞ g)
    (hs : ∀ x u v, g x u v = g x v u) (hpos : ∀ x v, v ≠ 0 → 0 < g x v v)
    (y p q : T → Coord) (hy : Continuous y) (hp : Continuous p) (hq : Continuous q)
    (hp0 : ∀ t, p t ≠ 0) (hq0 : ∀ t, q t ≠ 0)
    (hpq : ∀ t, g (y t) (p t) (q t) = 0) (t0 : T) :
    ∃ U : Set T, U ∈ 𝓝 t0 ∧ ∃ e : U → Coord ≃L[ℝ] Coord,
      Continuous (fun t ↦ (e t).toContinuousLinearMap) ∧
      (∀ t, e t (Pi.single 0 1) = metricNormalize (g (y t)) (p t) ∧
        e t (Pi.single 1 1) = metricNormalize (g (y t)) (q t)) ∧
      (∀ t : U, 0 ∈ (actualMetricChart g (y t) (e t)).source ∧
        actualMetricChart g (y t) (e t) 0 = y t ∧
        ContDiffAt ℝ ∞ (actualMetricChart g (y t) (e t)).symm (y t)) ∧
      (∀ (t : U) i j, pullbackMetric g (actualMetricChart g (y t) (e t)) 0
        (Pi.single i 1) (Pi.single j 1) = if i = j then 1 else 0) ∧
      (∀ (t : U) u v, fderiv ℝ (fun x ↦ pullbackMetric g (actualMetricChart g (y t) (e t)) x u v) 0 = 0) ∧
      (∀ k, Continuous (fun z : U × Coord ↦ iteratedFDeriv ℝ k
        (actualMetricChart g (y z.1) (e z.1) : Coord → Coord) z.2)) ∧
      ∀ k, Continuous (fun z : U × Coord ↦ iteratedFDeriv ℝ k
        (pulledForm g (y z.1, (e z.1).toContinuousLinearMap,
          actualFrameConnection g (y z.1) (e z.1))) z.2) := by
  obtain ⟨U, v, hU, hv, haxes, ho⟩ := exists_continuous_adapted_frame
    (fun t ↦ g (y t)) (hg.continuous.comp hy) (fun t ↦ hs (y t))
    (fun t ↦ hpos (y t)) p q hp hq hp0 hq0 hpq t0
  let e : U → Coord ≃L[ℝ] Coord := fun t ↦ frameEquiv (g (y t)) (v t) (ho t t.property)
  have he : Continuous (fun t ↦ (e t).toContinuousLinearMap) :=
    frameEquiv_continuous (fun t : U ↦ g (y t)) (fun t : U ↦ v t)
      (fun i ↦ continuousOn_iff_continuous_domRestrict.mp (hv i)) (fun t : U ↦ ho t t.property)
  have hy' : Continuous (fun t : U ↦ y t) := hy.comp continuous_subtype_val
  have hB := actualFrameConnection_continuous g hg hpos (fun t : U ↦ y t) hy' e he
  refine ⟨U, hU, e, he, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    simp only [e, ← ContinuousLinearEquiv.coe_coe, frameEquiv_coe, frameMap_axis]
    exact haxes t
  · intro t
    exact ⟨quadraticChart_source _ _ _, quadraticChartMap_zero _ _ _, quadraticChart_inverse_smooth _ _ _⟩
  · intro t i j
    rw [show (actualMetricChart g (y t) (e t) : Coord → Coord) =
      quadraticChartMap (y t) (e t) (actualFrameConnection g (y t) (e t)) from rfl,
      pullbackMetric_quadratic_zero]
    change g (y t) (frameMap (v t) (Pi.single i 1)) (frameMap (v t) (Pi.single j 1)) = _
    rw [frameMap_axis, frameMap_axis]
    exact ho t t.property i j
  · intro t u v
    exact actualMetricChart_metric_first_zero g hg hs hpos (y t) (e t) u v
  · intro k
    exact quadratic_family_spatial_jets _ hy' e he _ hB k
  · intro k
    exact pulled_metric_spatial_jets g hg _ hy' e he _ hB k

end

open Set Filter
open scoped ContDiff Topology
variable {T E F : Type*} [TopologicalSpace T]
  [NormedAddCommGroup E]
  [TopologicalSpace F]

lemma compact_family_common_radius {s : Set T} (hs : IsCompact s)
    (f : T × E → F) (hf : Continuous f) {V : Set F} (hV : IsOpen V)
    (h0 : ∀ t ∈ s, f (t,0) ∈ V) :
    ∃ r > 0, ∀ t ∈ s, ∀ x : E, ‖x‖ < r → f (t,x) ∈ V := by
  obtain ⟨U,W,_,hW,hsU,h0W,hUW⟩ := generalized_tube_lemma hs (isCompact_singleton (x := (0:E)))
    (hV.preimage hf) (by rintro ⟨t,x⟩ ⟨ht,hx⟩; obtain rfl := mem_singleton_iff.mp hx; exact h0 t ht)
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds (h0W (mem_singleton 0)))
  refine ⟨r,hr,fun t ht x hx ↦ hUW ⟨hsU ht, hball ?_⟩⟩
  simpa only [Metric.mem_ball, dist_zero_right] using hx

variable [NormedSpace ℝ E] [CompleteSpace E]

theorem compact_quadratic_chart_domain {s : Set T} (hs : IsCompact s)
    (y : T → E) (hy : Continuous y)
    (e : T → E ≃L[ℝ] E) (he : Continuous (fun t ↦ (e t).toContinuousLinearMap))
    (B : T → E →L[ℝ] E →L[ℝ] E) (hB : Continuous B)
    {U : Set E} (hU : IsOpen U) (hyU : ∀ t ∈ s, y t ∈ U) :
    ∃ r > 0, ∀ t ∈ s, ∀ x : E, ‖x‖ < r →
      quadraticChartMap (y t) (e t) (B t) x ∈ U ∧
      ∃ J : E ≃L[ℝ] E, J.toContinuousLinearMap =
        fderiv ℝ (quadraticChartMap (y t) (e t) (B t)) x := by
  have hF : Continuous (fun z : T × E ↦ quadraticChartMap (y z.1) (e z.1) (B z.1) z.2) :=
    rawQuadratic_smooth.continuous.comp
      (((hy.comp continuous_fst).prodMk ((he.comp continuous_fst).prodMk
        (hB.comp continuous_fst))).prodMk continuous_snd)
  have hJ : Continuous (fun z : T × E ↦ fderiv ℝ
      (quadraticChartMap (y z.1) (e z.1) (B z.1)) z.2) :=
    (smooth_spatial_fderiv rawQuadratic rawQuadratic_smooth).continuous.comp
      (((hy.comp continuous_fst).prodMk ((he.comp continuous_fst).prodMk
        (hB.comp continuous_fst))).prodMk continuous_snd)
  obtain ⟨r,hr,hri⟩ := compact_family_common_radius hs _ hF hU
    (fun t ht ↦ by simpa [quadraticChartMap_zero] using hyU t ht)
  obtain ⟨d,hd,hdj⟩ := compact_family_common_radius hs _ hJ ContinuousLinearEquiv.isOpen
    (fun t _ ↦ ⟨e t, (quadraticChartMap_deriv_zero (y t) (e t) (B t)).fderiv.symm⟩)
  refine ⟨min r d, lt_min hr hd, ?_⟩
  intro t ht x hx
  exact ⟨hri t ht x (lt_of_lt_of_le hx (min_le_left _ _)),
    hdj t ht x (lt_of_lt_of_le hx (min_le_right _ _))⟩

end Yau.Geometry

end

end OAI

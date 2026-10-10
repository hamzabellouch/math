import OAI.Geometry.KahlerSplitting.Boxes

namespace OAI

section
noncomputable section
open scoped Manifold ContDiff
open Set
noncomputable section
open Set Topology Filter Metric

namespace UniversalCoverSplitting
section MetricCharts
variable {n : ℕ} {X : ComplexManifold n}

def continuousMetricInChart (g : RealMetricField X) (c : X.Carrier) (z : Model n) :
    Model n →L[ℝ] Model n →L[ℝ] ℝ :=
  let e := extChartAt (model n) c
  let q := (mfderiv (model n) (model n) e.symm z).restrictScalars ℝ
  LinearMap.toContinuousLinearMap
    (LinearMap.toContinuousLinearMap.toLinearMap.comp
      ((g (e.symm z)).compl₁₂ q.toLinearMap q.toLinearMap))

@[simp] theorem continuousMetricInChart_apply (g : RealMetricField X) (c : X.Carrier)
    (z u v : Model n) : continuousMetricInChart g c z u v = metricInChart g c z u v := rfl

theorem KahlerMetric.continuous_metricInChart (g : KahlerMetric X) (c : X.Carrier) :
    ContinuousOn (continuousMetricInChart g.metric c) (extChartAt (model n) c).target := by
  apply continuousOn_clm_apply.mpr
  intro u
  apply continuousOn_clm_apply.mpr
  intro v
  exact (g.smooth c u v).continuousOn

theorem KahlerMetric.continuous_quadraticInChart (g : KahlerMetric X) (c : X.Carrier) :
    ContinuousOn (fun p : Model n × Model n ↦ metricInChart g.metric c p.1 p.2 p.2)
      ((extChartAt (model n) c).target ×ˢ univ) := by
  exact ((g.continuous_metricInChart c).comp continuousOn_fst (fun _ hp ↦ hp.1)).clm_apply
    continuousOn_snd |>.clm_apply continuousOn_snd

theorem metricInChart_smul (g : RealMetricField X) (c : X.Carrier)
    (z u : Model n) (r : ℝ) :
    metricInChart g c z (r • u) (r • u) = r ^ 2 * metricInChart g c z u u := by
  change continuousMetricInChart g c z (r • u) (r • u) =
    r ^ 2 * continuousMetricInChart g c z u u
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

theorem chart_inverse_derivative_injective (c : X.Carrier) {z : Model n}
    (hz : z ∈ (extChartAt (model n) c).target) :
    Function.Injective (mfderiv (model n) (model n) (extChartAt (model n) c).symm z) := by
  let e := extChartAt (model n) c
  have hsource : e.symm z ∈ e.source := e.map_target hz
  have heq := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm' hsource
  change (mfderiv (model n) (model n) e (e.symm z)).comp
    (mfderivWithin (model n) (model n) e.symm (Set.range (model n)) (e (e.symm z))) =
      ContinuousLinearMap.id ℂ (Model n) at heq
  have heq' : (mfderiv (model n) (model n) e (e.symm z)).comp
      (mfderiv (model n) (model n) e.symm z) = ContinuousLinearMap.id ℂ _ := by
    simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at heq
    erw [e.right_inv hz] at heq
    exact heq
  intro u v huv
  have hv := congrArg (mfderiv (model n) (model n) e (e.symm z)) huv
  change ((mfderiv (model n) (model n) e (e.symm z)).comp
    (mfderiv (model n) (model n) e.symm z)) u =
    ((mfderiv (model n) (model n) e (e.symm z)).comp
    (mfderiv (model n) (model n) e.symm z)) v at hv
  rw [heq'] at hv
  exact hv

theorem KahlerMetric.positive_quadraticInChart (g : KahlerMetric X) (c : X.Carrier)
    {z u : Model n} (hz : z ∈ (extChartAt (model n) c).target) (hu : u ≠ 0) :
    0 < metricInChart g.metric c z u u := by
  apply g.positive
  intro hzero
  apply hu
  exact chart_inverse_derivative_injective c hz (hzero.trans (map_zero _).symm)

theorem metricInChart_forward (g : RealMetricField X) (c : X.Carrier)
    {x : X.Carrier} (hx : x ∈ (extChartAt (model n) c).source) (u v : Tangent X x) :
    metricInChart g c ((extChartAt (model n) c) x)
      ((mfderiv (model n) (model n) (extChartAt (model n) c) x) u)
      ((mfderiv (model n) (model n) (extChartAt (model n) c) x) v) = g x u v := by
  let e := extChartAt (model n) c
  let p := mfderiv (model n) (model n) e x
  let q := mfderiv (model n) (model n) e.symm (e x)
  have hi : q.comp p = ContinuousLinearMap.id ℂ _ := by
    simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
      mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' hx
  have hu : q (p u) = u := congrArg (fun L : Tangent X x →L[ℂ] Tangent X x ↦ L u) hi
  have hv : q (p v) = v := congrArg (fun L : Tangent X x →L[ℂ] Tangent X x ↦ L v) hi
  change g (e.symm (e x)) (q (p u)) (q (p v)) = g x u v
  rw [e.left_inv hx]
  change g x (q (p u)) (q (p v)) = g x u v
  rw [hu,hv]

theorem projectionInChart_forward (P : ProjectionField X) (c : X.Carrier)
    {x : X.Carrier} (hx : x ∈ (extChartAt (model n) c).source) (u : Tangent X x) :
    projectionInChart P c ((extChartAt (model n) c) x)
      ((mfderiv (model n) (model n) (extChartAt (model n) c) x) u) =
    (mfderiv (model n) (model n) (extChartAt (model n) c) x) (P x u) := by
  let e := extChartAt (model n) c
  let p := mfderiv (model n) (model n) e x
  let q := mfderiv (model n) (model n) e.symm (e x)
  have hi : q.comp p = ContinuousLinearMap.id ℂ _ := by
    simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
      mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt' hx
  have hu : q (p u) = u := congrArg (fun L : Tangent X x →L[ℂ] Tangent X x ↦ L u) hi
  change (mfderiv (model n) (model n) e (e.symm (e x))) (P (e.symm (e x))
    (q (p u))) = p (P x u)
  rw [e.left_inv hx]
  change p (P x (q (p u))) = p (P x u)
  rw [hu]

theorem KahlerMetric.exists_projection_bound_on_chartCompact (g : KahlerMetric X)
    (P : ProjectionField X) (hP : HolomorphicProjection P) (c : X.Carrier)
    {K : Set (Model n)} (hK : IsCompact K) (hKt : K ⊆ (extChartAt (model n) c).target) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ (extChartAt (model n) c).source,
      (extChartAt (model n) c) x ∈ K → ∀ u : Tangent X x,
      g.metric x (P x u) (P x u) ≤ C * g.metric x u u := by
  have hm := (g.continuous_quadraticInChart c).mono (prod_mono hKt Subset.rfl)
  have hp : ContinuousOn (fun z ↦ (projectionInChart P c z).restrictScalars ℝ) K :=
    (ContinuousLinearMap.restrictScalarsL ℂ (Model n) (Model n) ℝ ℝ).continuous.comp_continuousOn
      ((hP c).continuousOn.mono hKt)
  obtain ⟨C,hC,hbound⟩ := exists_quadratic_operator_bound hK
    (fun z u ↦ metricInChart g.metric c z u u)
    (fun z ↦ (projectionInChart P c z).restrictScalars ℝ) hm hp
    (fun z hz u hu ↦ g.positive_quadraticInChart c (hKt hz) hu)
    (fun z _ r u ↦ metricInChart_smul g.metric c z u r)
  refine ⟨C,hC,fun x hx hxK u ↦ ?_⟩
  have hb := hbound ((extChartAt (model n) c) x) hxK
    ((mfderiv (model n) (model n) (extChartAt (model n) c) x) u)
  change metricInChart g.metric c ((extChartAt (model n) c) x)
    (projectionInChart P c ((extChartAt (model n) c) x)
      ((mfderiv (model n) (model n) (extChartAt (model n) c) x) u))
    (projectionInChart P c ((extChartAt (model n) c) x)
      ((mfderiv (model n) (model n) (extChartAt (model n) c) x) u)) ≤
    C * metricInChart g.metric c ((extChartAt (model n) c) x)
      ((mfderiv (model n) (model n) (extChartAt (model n) c) x) u)
      ((mfderiv (model n) (model n) (extChartAt (model n) c) x) u) at hb
  rw [projectionInChart_forward P c hx u,
    metricInChart_forward g.metric c hx, metricInChart_forward g.metric c hx] at hb
  exact hb

theorem KahlerMetric.nonnegative (g : KahlerMetric X) (x : X.Carrier) (u : Tangent X x) :
    0 ≤ g.metric x u u := by
  by_cases hu : u = 0
  · simp [hu]
  · exact (g.positive x u hu).le

theorem KahlerMetric.exists_uniform_projection_quadraticBound [CompactSpace X.Carrier]
    (g : KahlerMetric X) (P : ProjectionField X) (hP : HolomorphicProjection P) :
    ∃ C : ℝ, 0 < C ∧ ∀ x (u : Tangent X x),
      g.metric x (P x u) (P x u) ≤ C * g.metric x u u := by
  classical
  have hlocal : ∀ x : X.Carrier, ∃ (C : ℝ) (U : Set X.Carrier),
      0 < C ∧ U ∈ 𝓝 x ∧ ∀ y ∈ U, ∀ u : Tangent X y,
        g.metric y (P y u) (P y u) ≤ C * g.metric y u u := by
    intro x
    let e := extChartAt (model n) x
    obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp (isOpen_extChartAt_target x)
      (e x) (mem_extChartAt_target x)
    have hr2 : 0 < r / 2 := half_pos hr
    have hK : closedBall (e x) (r / 2) ⊆ e.target :=
      (closedBall_subset_ball (by linarith : r / 2 < r)).trans hball
    obtain ⟨C,hC,hbound⟩ := g.exists_projection_bound_on_chartCompact P hP x
      (isCompact_closedBall (e x) (r / 2)) hK
    refine ⟨C, e.source ∩ e ⁻¹' ball (e x) (r / 2),hC,?_,?_⟩
    · exact inter_mem (extChartAt_source_mem_nhds x)
        ((continuousAt_extChartAt x).preimage_mem_nhds (ball_mem_nhds (e x) hr2))
    · intro y hy u
      exact hbound y hy.1 (ball_subset_closedBall hy.2) u
  choose C U hC hU hbound using hlocal
  obtain ⟨t,_,ht⟩ := isCompact_univ.elim_nhds_subcover U (fun x _ ↦ hU x)
  have hsum : 0 ≤ ∑ x ∈ t, C x := Finset.sum_nonneg (fun x _ ↦ (hC x).le)
  refine ⟨1 + ∑ x ∈ t, C x,by linarith,fun y u ↦ ?_⟩
  obtain ⟨x,hxt,hy⟩ := mem_iUnion₂.mp (ht (mem_univ y))
  have hle : C x ≤ 1 + ∑ z ∈ t, C z := by
    have hcx : C x ≤ ∑ z ∈ t, C z := Finset.single_le_sum (fun z _ ↦ (hC z).le) hxt
    linarith
  exact (hbound x y hy u).trans (mul_le_mul_of_nonneg_right hle (g.nonnegative y u))

def metricNorm (g : KahlerMetric X) (x : X.Carrier) (u : Tangent X x) : ℝ :=
  Real.sqrt (g.metric x u u)

theorem KahlerMetric.exists_uniform_projection_normBound [CompactSpace X.Carrier]
    (g : KahlerMetric X) (P : ProjectionField X) (hP : HolomorphicProjection P) :
    ∃ C : ℝ, 0 < C ∧ ∀ x (u : Tangent X x),
      metricNorm g x (P x u) ≤ C * metricNorm g x u := by
  obtain ⟨C,hC,hbound⟩ := g.exists_uniform_projection_quadraticBound P hP
  refine ⟨Real.sqrt C,Real.sqrt_pos.mpr hC,fun x u ↦ ?_⟩
  dsimp [metricNorm]
  have hb := Real.sqrt_le_sqrt (hbound x u)
  rwa [Real.sqrt_mul hC.le] at hb

@[instance_reducible]
def KahlerMetric.realInnerCore (g : KahlerMetric X) (x : X.Carrier) :
    PreInnerProductSpace.Core ℝ (Tangent X x) where
  inner u v := g.metric x u v
  conj_inner_symm u v := by simpa using g.symmetric x v u
  re_inner_nonneg u := g.nonnegative x u
  add_left u v w := by simp only [map_add, LinearMap.add_apply]
  smul_left u v r := by simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, conj_trivial]

theorem metricNorm_add_le (g : KahlerMetric X) (x : X.Carrier) (u v : Tangent X x) :
    metricNorm g x (u + v) ≤ metricNorm g x u + metricNorm g x v := by
  let := g.realInnerCore x
  let := InnerProductSpace.Core.toNorm (𝕜 := ℝ) (F := Tangent X x)
  exact (InnerProductSpace.Core.toSeminormedSpaceCore (g.realInnerCore x)).norm_triangle u v

theorem metric_abs_le (g : KahlerMetric X) (x : X.Carrier) (u v : Tangent X x) :
    |g.metric x u v| ≤ metricNorm g x u * metricNorm g x v := by
  let := g.realInnerCore x
  exact InnerProductSpace.Core.norm_inner_le_norm (𝕜 := ℝ) u v

theorem KahlerMetric.orthogonal_I (g : KahlerMetric X) (x : X.Carrier) (u : Tangent X x) :
    g.metric x (Complex.I • u) u = 0 := by
  have hh := g.hermitian x (Complex.I • u) u
  simp only [smul_smul, Complex.I_mul_I, neg_one_smul, map_neg, LinearMap.neg_apply] at hh
  rw [g.symmetric x u (Complex.I • u)] at hh
  linarith

theorem KahlerMetric.quadratic_complex_smul (g : KahlerMetric X) (x : X.Carrier)
    (u : Tangent X x) (z : ℂ) :
    g.metric x (z • u) (z • u) = ‖z‖ ^ 2 * g.metric x u u := by
  have hzu : z • u = z.re • u + z.im • (Complex.I • u) := by
    rw [← Complex.coe_smul, ← Complex.coe_smul, smul_smul, ← add_smul, Complex.re_add_im]
  have hui : g.metric x u (Complex.I • u) = 0 := by
    rw [g.symmetric x u (Complex.I • u)]
    exact g.orthogonal_I x u
  rw [hzu]
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [hui,g.orthogonal_I x u,g.hermitian x u u,Complex.sq_norm,Complex.normSq_apply]
  ring

theorem metricNorm_complex_smul (g : KahlerMetric X) (x : X.Carrier)
    (u : Tangent X x) (z : ℂ) :
    metricNorm g x (z • u) = ‖z‖ * metricNorm g x u := by
  dsimp [metricNorm]
  rw [g.quadratic_complex_smul, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

end MetricCharts
end UniversalCoverSplitting
namespace UniversalCoverSplitting
section ComplementProjection
universe u
variable {n r₁ r₂ : ℕ}
variable {X : ComplexManifold.{u} n}

theorem projectionInChart_sub_id (P : ProjectionField X) (c : X.Carrier)
    {z : Model n} (hz : z ∈ (extChartAt (model n) c).target) :
    projectionInChart (fun x ↦ ContinuousLinearMap.id ℂ (Tangent X x) - P x) c z =
      ContinuousLinearMap.id ℂ (Model n) - projectionInChart P c z := by
  let e := extChartAt (model n) c
  have heq := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm' (e.map_target hz)
  change (mfderiv (model n) (model n) e (e.symm z)).comp
    (mfderivWithin (model n) (model n) e.symm (Set.range (model n)) (e (e.symm z))) =
      ContinuousLinearMap.id ℂ (Model n) at heq
  have heq' : (mfderiv (model n) (model n) e (e.symm z)).comp
      (mfderiv (model n) (model n) e.symm z) = ContinuousLinearMap.id ℂ _ := by
    simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at heq
    erw [e.right_inv hz] at heq
    exact heq
  ext u : 1
  change (mfderiv (model n) (model n) e (e.symm z))
    (((ContinuousLinearMap.id ℂ (Tangent X (e.symm z)) - P (e.symm z)))
      ((mfderiv (model n) (model n) e.symm z) u)) = _
  simp only [sub_apply, ContinuousLinearMap.id_apply, map_sub]
  have hh := congrArg (fun L : Model n →L[ℂ] Model n ↦ L u) heq'
  change (mfderiv (model n) (model n) e (e.symm z))
    ((mfderiv (model n) (model n) e.symm z) u) = u at hh
  rw [hh]
  rfl

theorem HolomorphicProjection.complement {P : ProjectionField X}
    (hP : HolomorphicProjection P) :
    HolomorphicProjection (fun x ↦ ContinuousLinearMap.id ℂ (Tangent X x) - P x) := by
  intro c
  apply ((differentiableOn_const (c := ContinuousLinearMap.id ℂ (Model n))).sub (hP c)).congr
  intro z hz
  exact projectionInChart_sub_id P c hz

theorem HolomorphicSplitting.complement_holomorphic (S : HolomorphicSplitting X r₁ r₂) :
    HolomorphicProjection (complementaryProjection S) := S.holomorphic.complement

theorem KahlerMetric.exists_uniform_splitting_bound [CompactSpace X.Carrier]
    (g : KahlerMetric X) (S : HolomorphicSplitting X r₁ r₂) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      (∀ x (u : Tangent X x), metricNorm g x (S.projection x u) ≤ C₁ * metricNorm g x u) ∧
      (∀ x (u : Tangent X x),
        metricNorm g x (complementaryProjection S x u) ≤ C₂ * metricNorm g x u) := by
  obtain ⟨C₁,hC₁,h₁⟩ := g.exists_uniform_projection_normBound S.projection S.holomorphic
  obtain ⟨C₂,hC₂,h₂⟩ := g.exists_uniform_projection_normBound
    (complementaryProjection S) S.complement_holomorphic
  exact ⟨C₁,C₂,hC₁,hC₂,h₁,h₂⟩

theorem mixed_direction_metric_norm_le (g : KahlerMetric X) (x : X.Carrier)
    (P : Tangent X x →L[ℂ] Tangent X x) (D : (ℂ × ℂ) →L[ℂ] Tangent X x)
    (h₁ : P (D (1, 0)) = D (1, 0)) (h₂ : P (D (0, 1)) = 0)
    (C₁ C₂ : ℝ)
    (hC₁ : ∀ u, metricNorm g x (P u) ≤ C₁ * metricNorm g x u)
    (hC₂ : ∀ u, metricNorm g x ((ContinuousLinearMap.id ℂ (Tangent X x) - P) u) ≤
      C₂ * metricNorm g x u)
    (a₁ a₂ b₁ b₂ : ℂ) (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) :
    metricNorm g x (D (a₁, a₂)) ≤
      (‖a₁/b₁‖ * C₁ + ‖a₂/b₂‖ * C₂) * metricNorm g x (D (b₁,b₂)) := by
  have split (c₁ c₂ : ℂ) : D (c₁, c₂) = c₁ • D (1, 0) + c₂ • D (0, 1) := by
    calc
      D (c₁, c₂) = D (c₁ • (1, 0) + c₂ • (0, 1)) := by congr 1; ext <;> simp
      _ = c₁ • D (1, 0) + c₂ • D (0, 1) := by rw [map_add, map_smul, map_smul]
  have hid : D (a₁,a₂) = (a₁/b₁) • P (D (b₁,b₂)) +
      (a₂/b₂) • ((ContinuousLinearMap.id ℂ (Tangent X x) - P) (D (b₁,b₂))) := by
    rw [split a₁ a₂, split b₁ b₂]
    simp only [map_add, map_smul, h₁, h₂, smul_zero, add_zero,
      sub_apply, ContinuousLinearMap.id_apply]
    simp only [sub_self, sub_zero, smul_zero, zero_add, smul_smul,
      div_mul_cancel₀ _ hb₁, div_mul_cancel₀ _ hb₂]
  rw [hid]
  calc
    _ ≤ metricNorm g x ((a₁/b₁) • P (D (b₁,b₂))) +
        metricNorm g x ((a₂/b₂) • ((ContinuousLinearMap.id ℂ (Tangent X x) - P) (D (b₁,b₂)))) :=
      metricNorm_add_le g x _ _
    _ = ‖a₁/b₁‖ * metricNorm g x (P (D (b₁,b₂))) +
        ‖a₂/b₂‖ * metricNorm g x ((ContinuousLinearMap.id ℂ (Tangent X x) - P) (D (b₁,b₂))) := by
      rw [metricNorm_complex_smul, metricNorm_complex_smul]
    _ ≤ ‖a₁/b₁‖ * (C₁ * metricNorm g x (D (b₁,b₂))) +
        ‖a₂/b₂‖ * (C₂ * metricNorm g x (D (b₁,b₂))) :=
      add_le_add (mul_le_mul_of_nonneg_left (hC₁ _) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (hC₂ _) (norm_nonneg _))
    _ = _ := by ring

end ComplementProjection
end UniversalCoverSplitting

noncomputable section
open Set Metric
namespace UniversalCoverSplitting
variable {B E : Type*} [TopologicalSpace B] [NormedAddCommGroup E]
  [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_quadratic_comparison {K : Set B} (hK : IsCompact K)
    (Q T : B → E → ℝ)
    (hQ : ContinuousOn (fun p : B × E ↦ Q p.1 p.2) (K ×ˢ univ))
    (hT : ContinuousOn (fun p : B × E ↦ T p.1 p.2) (K ×ˢ univ))
    (hpos : ∀ x ∈ K, ∀ u, u ≠ 0 → 0 < Q x u)
    (hhom : ∀ x ∈ K, ∀ (r : ℝ) u, Q x (r • u) = r ^ 2 * Q x u)
    (hThom : ∀ x ∈ K, ∀ (r : ℝ) u, T x (r • u) = r ^ 2 * T x u) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ K, ∀ u, T x u ≤ C * Q x u := by
  let L : Set (B × E) := K ×ˢ sphere 0 1
  have hL : IsCompact L := hK.prod (isCompact_sphere 0 1)
  have hQL : ContinuousOn (fun p : B × E ↦ Q p.1 p.2) L :=
    hQ.mono (prod_mono_right (subset_univ _))
  have hnum : ContinuousOn (fun p : B × E ↦ T p.1 p.2) L :=
    hT.mono (prod_mono_right (subset_univ _))
  have hden : ∀ p ∈ L, Q p.1 p.2 ≠ 0 := by
    intro p hp
    apply ne_of_gt (hpos p.1 hp.1 p.2 _)
    intro he
    have hn : ‖p.2‖ = (1:ℝ) := by simpa using hp.2
    simp [he] at hn
  obtain ⟨C,hC⟩ := hL.bddAbove_image (hnum.div hQL hden)
  refine ⟨max C 1, by positivity, fun x hx u ↦ ?_⟩
  have hzero : Q x 0 = 0 := by simpa using hhom x hx 0 (0:E)
  have hTzero : T x 0 = 0 := by simpa using hThom x hx 0 (0:E)
  by_cases hu : u = 0
  · simp [hu,hzero,hTzero]
  have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu
  let v := ‖u‖⁻¹ • u
  have hvnorm : ‖v‖ = 1 := by
    dsimp [v]
    rw [norm_smul_of_nonneg (inv_nonneg.mpr hn.le), inv_mul_cancel₀ hn.ne']
  have hv : v ∈ sphere (0:E) 1 := by simpa using hvnorm
  have hb : T x v / Q x v ≤ max C 1 :=
    (hC ⟨(x,v),⟨hx,hv⟩,rfl⟩).trans (le_max_left _ _)
  have hvpos : 0 < Q x v := hpos x hx v (by intro hh; simp [hh] at hvnorm)
  have hquad : T x v ≤ max C 1 * Q x v := (div_le_iff₀ hvpos).mp hb
  have huv : ‖u‖ • v = u := by
    dsimp [v]
    rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  calc
    T x u = ‖u‖ ^ 2 * T x v := by
      conv_lhs => rw [← huv]
      exact hThom x hx ‖u‖ v
    _ ≤ ‖u‖ ^ 2 * (max C 1 * Q x v) := mul_le_mul_of_nonneg_left hquad (sq_nonneg _)
    _ = max C 1 * Q x u := by
      have hs : Q x u = ‖u‖ ^ 2 * Q x v := by rw [← hhom x hx ‖u‖ v, huv]
      rw [hs]
      ring

end UniversalCoverSplitting

namespace UniversalCoverSplitting
open Set Metric
variable {n : ℕ} {X : ComplexManifold n}

theorem KahlerMetric.exists_chart_metric_comparison (g : KahlerMetric X) (c : X.Carrier)
    {K : Set (Model n)} (hK : IsCompact K) (he : K ⊆ (extChartAt (model n) c).target) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ z ∈ K, ∀ u : Model n,
      ‖u‖ ^ 2 ≤ C * metricInChart g.metric c z u u ∧
      metricInChart g.metric c z u u ≤ D * ‖u‖ ^ 2 := by
  have hN : ContinuousOn (fun p : Model n × Model n ↦ ‖p.2‖ ^ 2) (K ×ˢ univ) :=
    (continuous_snd.norm.pow 2).continuousOn
  have hQ := (g.continuous_quadraticInChart c).mono (prod_mono_left he)
  have hnormhom (z : Model n) (_ : z ∈ K) (r : ℝ) (u : Model n) :
      ‖r • u‖ ^ 2 = r ^ 2 * ‖u‖ ^ 2 := by rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have hnormpos (z : Model n) (_ : z ∈ K) (u : Model n) (hu : u ≠ 0) :
      0 < ‖u‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hu)
  obtain ⟨C,hC,hCb⟩ := exists_quadratic_comparison hK
    (fun z u ↦ metricInChart g.metric c z u u) (fun _ u ↦ ‖u‖ ^ 2) hQ hN
    (fun z hz u hu ↦ g.positive_quadraticInChart c (he hz) hu)
    (fun z _ r u ↦ metricInChart_smul g.metric c z u r) hnormhom
  obtain ⟨D,hD,hDb⟩ := exists_quadratic_comparison hK
    (fun _ u ↦ ‖u‖ ^ 2) (fun z u ↦ metricInChart g.metric c z u u) hN hQ
    hnormpos hnormhom (fun z _ r u ↦ metricInChart_smul g.metric c z u r)
  exact ⟨C,D,hC,hD,fun z hz u ↦ ⟨hCb z hz u,hDb z hz u⟩⟩

theorem KahlerMetric.exists_chart_speed_comparison (g : KahlerMetric X) (c : X.Carrier)
    {K : Set (Model n)} (hK : IsCompact K) (he : K ⊆ (extChartAt (model n) c).target) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ x ∈ (extChartAt (model n) c).source,
      (extChartAt (model n) c) x ∈ K → ∀ v : Tangent X x,
      (@norm (Model n) _ (mfderiv (model n) (model n) (extChartAt (model n) c) x v)) ≤ C * metricNorm g x v ∧
      metricNorm g x v ≤ D * (@norm (Model n) _ (mfderiv (model n) (model n) (extChartAt (model n) c) x v)) := by
  obtain ⟨C,D,hC,hD,hb⟩ := g.exists_chart_metric_comparison c hK he
  refine ⟨Real.sqrt C,Real.sqrt D,Real.sqrt_pos.mpr hC,Real.sqrt_pos.mpr hD,?_⟩
  intro x hx hxK v
  obtain ⟨hCv,hDv⟩ := hb _ hxK (mfderiv (model n) (model n) (extChartAt (model n) c) x v)
  rw [metricInChart_forward g.metric c hx] at hCv hDv
  have hsq : Real.sqrt ((@norm (Model n) _ (mfderiv (model n) (model n) (extChartAt (model n) c) x v)) ^ 2) =
      @norm (Model n) _ (mfderiv (model n) (model n) (extChartAt (model n) c) x v) :=
    Real.sqrt_sq (norm_nonneg (show Model n from mfderiv (model n) (model n) (extChartAt (model n) c) x v))
  constructor
  · have hh := Real.sqrt_le_sqrt hCv
    rw [hsq, Real.sqrt_mul hC.le] at hh
    exact hh
  · have hh := Real.sqrt_le_sqrt hDv
    rw [Real.sqrt_mul hD.le, hsq] at hh
    exact hh

end UniversalCoverSplitting

namespace UniversalCoverSplitting
open Filter Topology Metric MeasureTheory
open scoped Manifold ENNReal
variable {n : ℕ} {X : ComplexManifold n}

def curveSpeed (g : KahlerMetric X) (f : ℂ → X.Carrier) (z : ℂ) : ℝ :=
  metricNorm g (f z) (mfderiv 𝓘(ℂ, ℂ) (model n) f z (1 : ℂ))

def curveArea (g : KahlerMetric X) (f : ℂ → X.Carrier) (U : Set ℂ) : ℝ≥0∞ :=
  ∫⁻ z in U, ENNReal.ofReal (curveSpeed g f z ^ 2)

theorem curveSpeed_nonneg (g : KahlerMetric X) (f : ℂ → X.Carrier) (z : ℂ) :
    0 ≤ curveSpeed g f z := Real.sqrt_nonneg _

theorem chart_deriv_curve {f : ℂ → X.Carrier} {z : ℂ}
    (hf : MDifferentiableAt 𝓘(ℂ, ℂ) (model n) f z)
    (c : X.Carrier) (hc : f z ∈ (extChartAt (model n) c).source) :
    deriv ((extChartAt (model n) c) ∘ f) z =
      mfderiv (model n) (model n) (extChartAt (model n) c) (f z)
        (mfderiv 𝓘(ℂ, ℂ) (model n) f z (1 : ℂ)) := by
  have he : MDifferentiableAt (model n) (model n) (extChartAt (model n) c) (f z) :=
    mdifferentiableAt_extChartAt (by simpa only [extChartAt_source] using hc)
  rw [← fderiv_apply_one_eq_deriv, ← mfderiv_eq_fderiv, mfderiv_comp z he hf]
  rfl

theorem curveSpeed_eq_chart (g : KahlerMetric X) {f : ℂ → X.Carrier} {z : ℂ}
    (hf : MDifferentiableAt 𝓘(ℂ, ℂ) (model n) f z)
    (c : X.Carrier) (hc : f z ∈ (extChartAt (model n) c).source) :
    curveSpeed g f z = Real.sqrt (metricInChart g.metric c
      ((extChartAt (model n) c) (f z)) (deriv ((extChartAt (model n) c) ∘ f) z)
      (deriv ((extChartAt (model n) c) ∘ f) z)) := by
  rw [chart_deriv_curve hf c hc, metricInChart_forward g.metric c hc]
  rfl

theorem curveSpeed_continuousOn (g : KahlerMetric X) {f : ℂ → X.Carrier}
    {U : Set ℂ} (hU : IsOpen U)
    (hf : MDifferentiableOn 𝓘(ℂ, ℂ) (model n) f U) :
    ContinuousOn (curveSpeed g f) U := by
  intro z hz
  let c := f z
  let e := extChartAt (model n) c
  have hcf : ContinuousAt f z := (hf.mdifferentiableAt (hU.mem_nhds hz)).continuousAt
  have hN : U ∩ f ⁻¹' e.source ∈ 𝓝 z := inter_mem (hU.mem_nhds hz)
    (hcf (extChartAt_source_mem_nhds (I := model n) c))
  obtain ⟨r,hr,hrs⟩ := Metric.mem_nhds_iff.mp hN
  have hd : DifferentiableOn ℂ (e ∘ f) (ball z r) := by
    intro w hw
    have he : MDifferentiableAt (model n) (model n) e (f w) :=
      mdifferentiableAt_extChartAt (by simpa only [e, extChartAt_source, mem_preimage] using (hrs hw).2)
    exact (he.comp w (hf.mdifferentiableAt (hU.mem_nhds (hrs hw).1))).differentiableAt.differentiableWithinAt
  have hcchart : ContinuousOn (fun w ↦ ((e (f w)), deriv (e ∘ f) w)) (ball z r) :=
    hd.continuousOn.prodMk (hd.deriv isOpen_ball).continuousOn
  have hQ : ContinuousOn (fun w ↦ Real.sqrt (metricInChart g.metric c
      (e (f w)) (deriv (e ∘ f) w) (deriv (e ∘ f) w))) (ball z r) :=
    (g.continuous_quadraticInChart c |>.comp hcchart
      (fun w hw ↦ ⟨e.map_source (hrs hw).2, mem_univ _⟩)).sqrt
  have hS : ContinuousOn (curveSpeed g f) (ball z r) := hQ.congr (fun w hw ↦
    curveSpeed_eq_chart g (hf.mdifferentiableAt (hU.mem_nhds (hrs hw).1)) c (hrs hw).2)
  exact (hS.continuousAt (ball_mem_nhds z hr)).continuousWithinAt

theorem curveSpeed_affine (g : KahlerMetric X) {f : ℂ → X.Carrier}
    (p b z : ℂ) (hf : MDifferentiableAt 𝓘(ℂ, ℂ) (model n) f (p + b * z)) :
    curveSpeed g (fun w ↦ f (p + b * w)) z = ‖b‖ * curveSpeed g f (p + b * z) := by
  have ha : HasDerivAt (fun w : ℂ ↦ p + b * w) b z := by
    convert! ((hasDerivAt_id z).const_mul b).const_add p using 1; simp
  unfold curveSpeed
  have he : (fun w ↦ f (p + b * w)) = f ∘ (fun w : ℂ ↦ p + b * w) := rfl
  rw [he, mfderiv_comp z hf ha.differentiableAt.mdifferentiableAt,
    mfderiv_eq_fderiv]
  change metricNorm g (f (p + b * z))
    (mfderiv 𝓘(ℂ, ℂ) (model n) f (p + b * z) (fderiv ℂ (fun w : ℂ ↦ p + b * w) z 1)) = _
  rw [fderiv_apply_one_eq_deriv, ha.deriv]
  let D : ℂ →L[ℂ] Tangent X (f (p + b * z)) := mfderiv 𝓘(ℂ, ℂ) (model n) f (p + b * z)
  change metricNorm g (f (p + b*z)) (D b) = ‖b‖ * metricNorm g (f (p + b*z)) (D (1 : ℂ))
  have hDb : D b = b • D (1 : ℂ) := by
    simpa only [smul_eq_mul, mul_one] using D.map_smul b (1 : ℂ)
  rw [hDb,metricNorm_complex_smul]

end UniversalCoverSplitting
end
end
end
end

end OAI

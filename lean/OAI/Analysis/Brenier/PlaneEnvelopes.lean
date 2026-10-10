import Mathlib

namespace OAI

noncomputable section

open scoped Topology

namespace Problem358.MovingHyperplaneChart

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Projection onto an affine hyperplane along a fixed transverse direction. -/
def chart (v n : V) (c : ℝ) (z : V) : V :=
  z - ((inner ℝ z n + c) / inner ℝ v n) • v

/-- The chart takes values in its target plane whenever the direction is transverse. -/
theorem chart_mem (v n : V) (c : ℝ) (z : V) (h : inner ℝ v n ≠ 0) :
    inner ℝ (chart v n c z) n + c = 0 := by
  simp only [chart, inner_sub_left, real_inner_smul_left]
  field_simp
  ring

/-- A point already on the target plane is fixed. -/
theorem chart_eq_self {v n z : V} {c : ℝ} (hz : inner ℝ z n + c = 0) :
    chart v n c z = z := by
  simp [chart, hz]

/-- Projection is invariant under translation parallel to its direction. -/
theorem chart_add_smul (v n : V) (c a : ℝ) (z : V) (h : inner ℝ v n ≠ 0) :
    chart v n c (z + a • v) = chart v n c z := by
  have hs : (inner ℝ (z + a • v) n + c) / inner ℝ v n =
      (inner ℝ z n + c) / inner ℝ v n + a := by
    simp only [inner_add_left, real_inner_smul_left]
    field_simp
    ring
  simp only [chart, hs]
  module

/-- Two successive charts with the same transverse direction collapse to the last one. -/
theorem chart_chart (v n₁ n₂ : V) (c₁ c₂ : ℝ) (z : V)
    (h₂ : inner ℝ v n₂ ≠ 0) :
    chart v n₂ c₂ (chart v n₁ c₁ z) = chart v n₂ c₂ z := by
  conv_lhs => arg 4; unfold chart
  rw [sub_eq_add_neg, ← neg_smul]
  exact chart_add_smul v n₂ c₂ _ z h₂

/-- A reverse chart recovers every point of the original plane. -/
theorem inverse_chart {v n₀ n z : V} {c₀ c : ℝ}
    (h₀ : inner ℝ v n₀ ≠ 0) (hz : inner ℝ z n₀ + c₀ = 0) :
    chart v n₀ c₀ (chart v n c z) = z := by
  rw [chart_chart _ _ _ _ _ _ h₀]
  exact chart_eq_self hz

/-- Restricting the chart to a plane transverse to its direction is injective. -/
theorem chart_injOn {v n₀ n : V} {c₀ c : ℝ} (h₀ : inner ℝ v n₀ ≠ 0) :
    Set.InjOn (chart v n c) {z | inner ℝ z n₀ + c₀ = 0} := by
  intro z hz w hw heq
  have hh := congrArg (chart v n₀ c₀) heq
  simpa only [inverse_chart h₀ hz, inverse_chart h₀ hw] using hh

/-- The chart maps one transverse plane onto the other. -/
theorem chart_bijOn {v n₀ n : V} {c₀ c : ℝ}
    (h₀ : inner ℝ v n₀ ≠ 0) (h : inner ℝ v n ≠ 0) :
    Set.BijOn (chart v n c) {z | inner ℝ z n₀ + c₀ = 0}
      {z | inner ℝ z n + c = 0} := by
  refine ⟨fun z _ => chart_mem _ _ _ _ h, chart_injOn h₀, ?_⟩
  intro z hz
  refine ⟨chart v n₀ c₀ z, chart_mem _ _ _ _ h₀, ?_⟩
  exact inverse_chart h hz

/-- For fixed plane parameters the chart is a continuous affine map. -/
theorem continuous_chart (v n : V) (c : ℝ) : Continuous (chart v n c) := by
  unfold chart
  fun_prop

/-- The geometric identification of any two planes transverse to the same direction. -/
def planeHomeomorph (v n₀ n : V) (c₀ c : ℝ)
    (h₀ : inner ℝ v n₀ ≠ 0) (h : inner ℝ v n ≠ 0) :
    {z : V // inner ℝ z n₀ + c₀ = 0} ≃ₜ {z : V // inner ℝ z n + c = 0} where
  toFun z := ⟨chart v n c z, chart_mem _ _ _ _ h⟩
  invFun z := ⟨chart v n₀ c₀ z, chart_mem _ _ _ _ h₀⟩
  left_inv z := Subtype.ext (inverse_chart h₀ z.property)
  right_inv z := Subtype.ext (inverse_chart h z.property)
  continuous_toFun := (continuous_chart v n c).comp continuous_subtype_val |>.subtype_mk _
  continuous_invFun := (continuous_chart v n₀ c₀).comp continuous_subtype_val |>.subtype_mk _

/-- Joint continuity in the varying plane and the original point. -/
theorem continuousAt_chart_joint (v : V) {p : (V × ℝ) × V}
    (h : inner ℝ v p.1.1 ≠ 0) :
    ContinuousAt (fun q : (V × ℝ) × V => chart v q.1.1 q.1.2 q.2) p := by
  unfold chart
  fun_prop (disch := assumption)

/-- A uniform quantitative estimate for the moving chart on a bounded part of the old plane. -/
theorem norm_chart_sub_le {v n₀ n z : V} {c₀ c R : ℝ}
    (hz : inner ℝ z n₀ + c₀ = 0) (hR : ‖z‖ ≤ R) :
    ‖chart v n c z - z‖ ≤
      ((R * ‖n - n₀‖ + |c - c₀|) / |inner ℝ v n|) * ‖v‖ := by
  have heq : inner ℝ z n + c = inner ℝ z (n - n₀) + (c - c₀) := by
    rw [inner_sub_right]
    linarith
  have hnum : |inner ℝ z n + c| ≤ R * ‖n - n₀‖ + |c - c₀| := by
    rw [heq]
    calc
      |inner ℝ z (n - n₀) + (c - c₀)| ≤
          |inner ℝ z (n - n₀)| + |c - c₀| := abs_add_le _ _
      _ ≤ ‖z‖ * ‖n - n₀‖ + |c - c₀| := by
        exact add_le_add (by simpa only [Real.norm_eq_abs] using
          (norm_inner_le_norm (𝕜 := ℝ) z (n - n₀))) le_rfl
      _ ≤ R * ‖n - n₀‖ + |c - c₀| := by gcongr
  have hnorm : ‖chart v n c z - z‖ =
      (|inner ℝ z n + c| / |inner ℝ v n|) * ‖v‖ := by
    simp [chart, sub_sub_cancel_left, norm_smul]
  rw [hnorm]
  exact mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hnum (abs_nonneg _)) (norm_nonneg _)

/-- Nearby affine planes converge uniformly on every bounded part of the original plane. -/
theorem tendstoUniformlyOn_chart {v n₀ : V} {c₀ R : ℝ} {S : Set V}
    (h₀ : inner ℝ v n₀ ≠ 0)
    (hplane : ∀ z ∈ S, inner ℝ z n₀ + c₀ = 0)
    (hR : ∀ z ∈ S, ‖z‖ ≤ R) :
    TendstoUniformlyOn (fun p : V × ℝ => chart v p.1 p.2) id (𝓝 (n₀, c₀)) S := by
  have hc : ContinuousAt
      (fun p : V × ℝ => ((R * ‖p.1 - n₀‖ + |p.2 - c₀|) / |inner ℝ v p.1|) * ‖v‖)
      (n₀, c₀) := by
    fun_prop (disch := exact abs_ne_zero.mpr h₀)
  have ht : Filter.Tendsto
      (fun p : V × ℝ => ((R * ‖p.1 - n₀‖ + |p.2 - c₀|) / |inner ℝ v p.1|) * ‖v‖)
      (𝓝 (n₀, c₀)) (𝓝 0) := by
    simpa using hc.tendsto
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with p hp z hz
  calc
    dist (id z) (chart v p.1 p.2 z) = ‖chart v p.1 p.2 z - z‖ := by
      rw [id_eq, dist_eq_norm, norm_sub_rev]
    _ ≤ ((R * ‖p.1 - n₀‖ + |p.2 - c₀|) / |inner ℝ v p.1|) * ‖v‖ :=
      norm_chart_sub_le (hplane z hz) (hR z hz)
    _ < ε := hp

/-- Compact parts of the original plane satisfy the uniform convergence statement. -/
theorem tendstoUniformlyOn_chart_of_isCompact {v n₀ : V} {c₀ : ℝ} {S : Set V}
    (h₀ : inner ℝ v n₀ ≠ 0) (hS : IsCompact S)
    (hplane : ∀ z ∈ S, inner ℝ z n₀ + c₀ = 0) :
    TendstoUniformlyOn (fun p : V × ℝ => chart v p.1 p.2) id (𝓝 (n₀, c₀)) S := by
  obtain ⟨R, hR⟩ := hS.isBounded.exists_norm_le
  exact tendstoUniformlyOn_chart h₀ hplane hR

end Problem358.MovingHyperplaneChart

end

noncomputable section

open MeasureTheory Set Metric
open scoped RealInnerProductSpace

namespace Problem358.TangentEnvelope

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Orthogonal projection bounds the tangent coordinate independently of the
normal displacement used to straighten a moving face. -/
theorem norm_tangent_le_two_radius {u z w : V} {t R : ℝ}
    (horth : ⟪w, u⟫ = 0) (hz : ‖z‖ ≤ R)
    (hx : ‖z + w + t • u‖ ≤ R) : ‖w‖ ≤ 2 * R := by
  have horth' : ⟪w, t • u⟫ = 0 := by simp [inner_smul_right, horth]
  have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero w (t • u) horth'
  have hproj : ‖w‖ ≤ ‖w + t • u‖ := by
    nlinarith [sq_nonneg ‖t • u‖, norm_nonneg w, norm_nonneg (w + t • u)]
  have hid : w + t • u = (z + w + t • u) - z := by abel
  have hbound : ‖w + t • u‖ ≤ ‖z + w + t • u‖ + ‖z‖ := by
    rw [hid]
    exact norm_sub_le _ _
  linarith

/-- A body inside a radius-R ball pulls back to a fixed radius-2R support in
tangent coordinates, uniformly for every normal displacement. -/
theorem tangent_mem_closedBall_of_mem {u z : V} {K : Set V} {R t : ℝ}
    (hK : ∀ x ∈ K, ‖x‖ ≤ R) (hz : z ∈ K)
    (w : (ℝ ∙ u)ᗮ) (hx : z + (w : V) + t • u ∈ K) :
    w ∈ closedBall (0 : (ℝ ∙ u)ᗮ) (2 * R) := by
  rw [mem_closedBall, dist_zero_right]
  exact norm_tangent_le_two_radius (V := V) (w := (w : V)) (u := u) (z := z) (t := t)
    (Submodule.mem_orthogonal_singleton_iff_inner_left.mp w.property)
    (hK z hz) (hK _ hx)

/-- A bounded test function restricted to the source body has one compact
surface envelope valid for all moving-strip normal coordinates. -/
theorem norm_body_indicator_le_tangent_envelope {F : Type*}
    [NormedAddCommGroup F] {u z : V} {K : Set V} {R B t : ℝ}
    (hK : ∀ x ∈ K, ‖x‖ ≤ R) (hz : z ∈ K) (hB : 0 ≤ B)
    {f : V → F} (hf : ∀ x ∈ K, ‖f x‖ ≤ B) (w : (ℝ ∙ u)ᗮ) :
    ‖K.indicator f (z + (w : V) + t • u)‖ ≤
      (closedBall (0 : (ℝ ∙ u)ᗮ) (2 * R)).indicator (fun _ => B) w := by
  classical
  by_cases hx : z + (w : V) + t • u ∈ K
  · rw [Set.indicator_of_mem hx,
      Set.indicator_of_mem (tangent_mem_closedBall_of_mem hK hz w hx)]
    exact hf _ hx
  · rw [Set.indicator_of_notMem hx, norm_zero]
    exact Set.indicator_nonneg (fun _ _ => hB) w

/-- Polynomially growing speeds times a compact tangent cutoff are integrable.
This supplies the domination required by moving-boundary differentiation. -/
theorem integrable_tangent_polynomial_envelope [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (u : V)
    (μ : Measure ((ℝ ∙ u)ᗮ)) [μ.IsAddHaarMeasure]
    (R A B : ℝ) (n : ℕ) :
    Integrable ((closedBall (0 : (ℝ ∙ u)ᗮ) R).indicator
      (fun w => (A + B * ‖w‖) ^ n)) μ := by
  have hcont : Continuous (fun w : (ℝ ∙ u)ᗮ => (A + B * ‖w‖) ^ n) := by fun_prop
  exact (hcont.continuousOn.integrableOn_compact (μ := μ) (isCompact_closedBall _ _)).integrable_indicator
    measurableSet_closedBall

end Problem358.TangentEnvelope

end

noncomputable section

open Set MeasureTheory

namespace Problem358.MovingPlaneEnvelope

open MovingHyperplaneChart

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The fixed reference plane, with its induced topology and measurable structure. -/
abbrev Plane (n₀ : V) (c₀ : ℝ) := {z : V // inner ℝ z n₀ + c₀ = 0}

/-- Projection back to the fixed reference plane along the common transverse direction. -/
def projection (v n₀ : V) (c₀ : ℝ) (h₀ : inner ℝ v n₀ ≠ 0) (z : V) : Plane n₀ c₀ :=
  ⟨chart v n₀ c₀ z, chart_mem v n₀ c₀ z h₀⟩

theorem continuous_projection (v n₀ : V) (c₀ : ℝ) (h₀ : inner ℝ v n₀ ≠ 0) :
    Continuous (projection v n₀ c₀ h₀) :=
  (continuous_chart v n₀ c₀).subtype_mk _

/-- A compact set produces one compact envelope on the reference plane. -/
def envelope (v n₀ : V) (c₀ : ℝ) (h₀ : inner ℝ v n₀ ≠ 0) (K : Set V) :
    Set (Plane n₀ c₀) := projection v n₀ c₀ h₀ '' K

theorem isCompact_envelope (v n₀ : V) (c₀ : ℝ) (h₀ : inner ℝ v n₀ ≠ 0)
    {K : Set V} (hK : IsCompact K) : IsCompact (envelope v n₀ c₀ h₀ K) :=
  hK.image (continuous_projection v n₀ c₀ h₀)

/-- Every moving-plane pullback of K is contained in the same compact envelope.
No bound on the moving normal or intercept, nor moving transversality, is needed. -/
theorem chart_preimage_subset_envelope {v n₀ : V} {c₀ : ℝ}
    (h₀ : inner ℝ v n₀ ≠ 0) (K : Set V) (n : V) (c : ℝ) :
    {z : Plane n₀ c₀ | chart v n c z.val ∈ K} ⊆ envelope v n₀ c₀ h₀ K := by
  intro z hz
  refine ⟨chart v n c z.val, hz, ?_⟩
  apply Subtype.ext
  exact inverse_chart h₀ z.property

/-- A bounded integrand cut off on K has a parameter-independent indicator bound
when pulled back by any moving-plane chart. -/
theorem norm_indicator_chart_le {W : Type*} [NormedAddCommGroup W]
    {v n₀ : V} {c₀ : ℝ} (h₀ : inner ℝ v n₀ ≠ 0)
    {K : Set V} {g : V → W} {C : ℝ} (hC : 0 ≤ C)
    (hg : ∀ x ∈ K, ‖g x‖ ≤ C) (n : V) (c : ℝ) (z : Plane n₀ c₀) :
    ‖K.indicator g (chart v n c z.val)‖ ≤
      (envelope v n₀ c₀ h₀ K).indicator (fun _ => C) z := by
  by_cases hz : chart v n c z.val ∈ K
  · have he := chart_preimage_subset_envelope h₀ K n c hz
    simpa only [Set.indicator_of_mem hz, Set.indicator_of_mem he] using
      hg (chart v n c z.val) hz
  · rw [Set.indicator_of_notMem hz, norm_zero]
    exact Set.indicator_nonneg (fun _ _ => hC) z

/-- Extra cell-cut factors bounded by one do not change the common envelope. -/
theorem norm_smul_indicator_chart_le {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] {v n₀ : V} {c₀ : ℝ} (h₀ : inner ℝ v n₀ ≠ 0)
    {K : Set V} {g : V → W} {C : ℝ} (hC : 0 ≤ C)
    (hg : ∀ x ∈ K, ‖g x‖ ≤ C) (n : V) (c : ℝ) (z : Plane n₀ c₀)
    (a : ℝ) (ha : |a| ≤ 1) :
    ‖a • K.indicator g (chart v n c z.val)‖ ≤
      (envelope v n₀ c₀ h₀ K).indicator (fun _ => C) z := by
  rw [norm_smul, Real.norm_eq_abs]
  exact (mul_le_of_le_one_left (norm_nonneg _) ha).trans
    (norm_indicator_chart_le h₀ hC hg n c z)

variable [MeasurableSpace V] [BorelSpace V]
  {v n₀ : V} {c₀ : ℝ} (h₀ : inner ℝ v n₀ ≠ 0)
  (μ : Measure (Plane n₀ c₀)) [IsLocallyFiniteMeasure μ]

/-- Local finiteness on the reference plane makes the fixed compact envelope integrable. -/
theorem integrable_envelope_bound {K : Set V} (hK : IsCompact K) (C : ℝ) :
    Integrable ((envelope v n₀ c₀ h₀ K).indicator (fun _ => C)) μ := by
  have hcompact := isCompact_envelope v n₀ c₀ h₀ hK
  exact (integrableOn_const hcompact.measure_ne_top).integrable_indicator hcompact.measurableSet

include h₀ in
/-- Continuous tests on a compact body admit one integrable majorant for every
moving chart and every additional scalar cut factor of absolute value at most one. -/
theorem exists_integrable_chart_majorant {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] {K : Set V} (hK : IsCompact K) {g : V → W}
    (hg : ContinuousOn g K) :
    ∃ B : Plane n₀ c₀ → ℝ, Integrable B μ ∧ (∀ z, 0 ≤ B z) ∧
      ∀ (n : V) (c : ℝ) (z : Plane n₀ c₀) (a : ℝ), |a| ≤ 1 →
        ‖a • K.indicator g (chart v n c z.val)‖ ≤ B z := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg
  refine ⟨(envelope v n₀ c₀ h₀ K).indicator (fun _ => max C 0),
    integrable_envelope_bound h₀ μ hK (max C 0), ?_, ?_⟩
  · exact fun z => Set.indicator_nonneg (fun _ _ => le_max_right C 0) z
  · intro n c z a ha
    exact norm_smul_indicator_chart_le h₀ (le_max_right C 0)
      (fun x hx => (hC x hx).trans (le_max_left C 0)) n c z a ha

end Problem358.MovingPlaneEnvelope

end

end OAI

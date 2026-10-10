import OAI.Geometry.Perimeter.Regularity.SurfaceGradientConstSub
import OAI.Geometry.Perimeter.Regularity.AnnularCutoffTestAdmissible

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack

theorem tendsto_weighted_halfspaceBlowup {n : ℕ} {E : Set (Euc n)}
    (hE : MeasurableSet E) {c v : Euc n} (hv : HasHalfspaceBlowup E c v) :
    Tendsto (fun r : ℝ ↦ ∫ z in Metric.ball (0 : Euc n) 1,
        E.indicator (fun _ ↦ (1 : ℝ)) (c + r • z) * divergence (radialNormalTest v) z)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ z, radialFlux v z)) := by
  let μ := (volume : Measure (Euc n)).restrict (Metric.ball 0 1)
  let χ : ℝ → Euc n → ℝ := fun r z ↦ E.indicator (fun _ ↦ (1 : ℝ)) (c + r • z)
  let H : Set (Euc n) := {z | inner ℝ z v < 0}
  let ψ : Euc n → ℝ := H.indicator (fun _ ↦ (1 : ℝ))
  let dV : Euc n → ℝ := divergence (radialNormalTest v)
  have hH : MeasurableSet H :=
    (isOpen_lt (continuous_id.inner continuous_const) continuous_const).measurableSet
  have hχ : ∀ r, Integrable (χ r) μ := integrable_rescaled_indicator hE c
  have hψ : Integrable ψ μ :=
    (integrableOn_const measure_ball_lt_top.ne (C := (1 : ℝ))).indicator hH
  have hdV : Continuous dV := continuous_divergence (radialNormalTest_contDiff v)
  have hcV : HasCompactSupport dV := (radialNormalTest_admissible hv.1).2.1.of_isClosed_subset
    (isClosed_tsupport _) (tsupport_divergence_subset _)
  obtain ⟨D, hD⟩ := hcV.exists_bound_of_continuous hdV
  have hχV : ∀ r, Integrable (fun z ↦ χ r z * dV z) μ := fun r ↦
    (hχ r).mul_bdd hdV.aestronglyMeasurable (Eventually.of_forall hD)
  have hψV : Integrable (fun z ↦ ψ z * dV z) μ :=
    hψ.mul_bdd hdV.aestronglyMeasurable (Eventually.of_forall hD)
  have hconv : Tendsto (fun r ↦ ∫ z, |χ r z - ψ z| ∂μ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    apply hv.2.congr'
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [normalized_ball_integral _ c hr]
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [χ, ψ, H, halfspace_indicator_rescale c v z hr]
  have hbound : ∀ r, ‖(∫ z, χ r z * dV z ∂μ) - ∫ z, ψ z * dV z ∂μ‖ ≤
      D * ∫ z, |χ r z - ψ z| ∂μ := by
    intro r
    calc
      _ = ‖∫ z, (χ r z - ψ z) * dV z ∂μ‖ := by
        simp_rw [sub_mul]
        rw [integral_sub (hχV r) hψV]
      _ ≤ ∫ z, D * |χ r z - ψ z| ∂μ := by
        apply norm_integral_le_of_norm_le ((hχ r |>.sub hψ).abs.const_mul D)
        filter_upwards [] with z
        rw [norm_mul, Real.norm_eq_abs]
        exact (mul_le_mul_of_nonneg_left (hD z) (abs_nonneg _)).trans_eq (mul_comm _ _)
      _ = _ := integral_const_mul _ _
  have hl : Tendsto (fun r ↦ ∫ z, χ r z * dV z ∂μ) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ z, ψ z * dV z ∂μ)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero (fun _ ↦ norm_nonneg _) hbound (by simpa using hconv.const_mul D)
  have heq : (∫ z, ψ z * dV z ∂μ) = ∫ z, radialFlux v z := by
    calc
      _ = ∫ z in Metric.ball (0 : Euc n) 1, radialFlux v z := by
        apply integral_congr_ae
        filter_upwards [] with z
        rw [radialFlux_eq_indicator]
        by_cases hz : z ∈ H <;> simp [ψ, H, dV, hz]
      _ = _ := setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz ↦
        image_eq_zero_of_notMem_tsupport (fun h ↦ hz
          ((radialFlux_support v).trans (Metric.closedBall_subset_ball (by norm_num)) h)))
  rw [heq] at hl
  exact hl

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack

theorem exists_halfspace_perimeter_lower_density_constant (n : ℕ) (hn : 0 < n) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ E : Set (Euc n), MeasurableSet E →
      ∀ x v, HasHalfspaceBlowup E x v →
        ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
          ENNReal.ofReal (c₀ * r ^ (n - 1)) ≤ perimeter E (Metric.ball x r) := by
  obtain ⟨c₁, hc₁, hflux⟩ := exists_uniform_radialFlux_lower n hn
  refine ⟨c₁ / 2, by positivity, ?_⟩
  intro E hE x v hv
  have hconv := tendsto_weighted_halfspaceBlowup hE hv
  have hlt : c₁ / 2 < ∫ z, radialFlux v z := by
    have hh := hflux v hv.1
    linarith
  have hevent := hconv.eventually (Ioi_mem_nhds hlt)
  filter_upwards [hevent, self_mem_nhdsWithin] with r hr0 hr
  change 0 < r at hr
  change c₁ / 2 < _ at hr0
  calc
    _ ≤ ENNReal.ofReal (∫ y in E, divergence (ballNormalTest x r v) y) := by
      apply ENNReal.ofReal_le_ofReal
      rw [ballNormalTest_integral hn E hE x hr v]
      exact (mul_le_mul_of_nonneg_right hr0.le (pow_nonneg hr.le _)).trans_eq (mul_comm _ _)
    _ ≤ perimeter E (Metric.ball x r) := by
      rw [perimeter_eq_iSup_tests]
      exact le_iSup_of_le (ballNormalTest x r v)
        (le_iSup_of_le (ballNormalTest_admissible x hr hv.1) le_rfl)

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack

theorem perimeter_finset_disjoint_superadditive {n : ℕ} (E : Set (Euc n))
    {ι : Type*} (s : Finset ι) (U : ι → Set (Euc n))
    (hU : (s : Set ι).PairwiseDisjoint U) :
    ∑ i ∈ s, perimeter E (U i) ≤ perimeter E (⋃ i ∈ s, U i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact bot_le
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have hs : (s : Set ι).PairwiseDisjoint U := (fun i hi j hj h ↦ hU (by simp [hi]) (by simp [hj]) h)
    have hd : Disjoint (U a) (⋃ i ∈ s, U i) := by
      rw [Set.disjoint_iUnion_right]
      intro i
      rw [Set.disjoint_iUnion_right]
      intro hi
      exact hU (by simp) (by simp [hi]) (by intro h; subst i; exact ha hi)
    calc
      _ ≤ perimeter E (U a) + perimeter E (⋃ i ∈ s, U i) := add_le_add le_rfl (ih hs)
      _ ≤ perimeter E (⋃ i ∈ insert a s, U i) :=
        perimeter_disjoint_superadditive E
          (by intro x hx; exact mem_iUnion.mpr ⟨a, mem_iUnion.mpr ⟨by simp, hx⟩⟩)
          (by intro x hx; simpa only [Finset.mem_insert, iUnion_iUnion_eq_or_left] using
            (show x ∈ U a ∪ ⋃ i ∈ s, U i from Or.inr hx)) hd

theorem perimeter_tsum_disjoint_le {n : ℕ} (E : Set (Euc n))
    {ι : Type*} (U : ι → Set (Euc n)) (Z : Set (Euc n))
    (hU : Pairwise (fun i j ↦ Disjoint (U i) (U j))) (hUZ : ∀ i, U i ⊆ Z) :
    ∑' i, perimeter E (U i) ≤ perimeter E Z := by
  apply ENNReal.summable.tsum_le_of_sum_le
  intro s
  exact (perimeter_finset_disjoint_superadditive E s U
    (fun _ _ _ _ h ↦ hU h)).trans
    (raw_perimeter_mono_region E (by simp only [iUnion_subset_iff]; intro i hi; exact hUZ i))

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack

theorem exists_perimeter_vitali_cover {n : ℕ} (E S : Set (Euc n))
    {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hdensity : ∀ x ∈ S, ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal (c₀ * r ^ (n - 1)) ≤ perimeter E (Metric.ball x r))
    (c : Euc n) {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) :
    ∃ (u : Set (Euc n)) (r : Euc n → ℝ), u.Countable ∧
      (∀ x ∈ u, 0 < r x ∧ r x ≤ δ) ∧
      (S ∩ Metric.ball c R ⊆ ⋃ x ∈ u, Metric.ball x (4 * r x)) ∧
      (∑' x : u, (ENNReal.ofReal (r x)) ^ (n - 1)) ≤
        (ENNReal.ofReal c₀)⁻¹ * perimeter E (Metric.ball c (2 * R)) := by
  classical
  let t := S ∩ Metric.ball c R
  have hchoose : ∀ x ∈ t, ∃ r : ℝ, 0 < r ∧ r ≤ min δ R ∧
      ENNReal.ofReal (c₀ * r ^ (n - 1)) ≤ perimeter E (Metric.ball x r) := by
    intro x hx
    have hev := hdensity x hx.1
    have hsmall : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), r < min δ R :=
      (eventually_lt_nhds (lt_min hδ hR)).filter_mono nhdsWithin_le_nhds
    obtain ⟨r, hr, hden, hsm⟩ :=
      ((show ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), 0 < r from self_mem_nhdsWithin).and (hev.and hsmall)).exists
    exact ⟨r, hr, hsm.le, hden⟩
  have htotal : ∀ x : Euc n, ∃ r : ℝ, 0 < r ∧ r ≤ min δ R ∧
      (x ∈ t → ENNReal.ofReal (c₀ * r ^ (n - 1)) ≤ perimeter E (Metric.ball x r)) := by
    intro x
    by_cases hx : x ∈ t
    · obtain ⟨r, hr, hrb, hd⟩ := hchoose x hx
      exact ⟨r, hr, hrb, fun _ ↦ hd⟩
    · exact ⟨min δ R / 2, by positivity, by linarith [lt_min hδ hR],
        (show x ∈ t → ENNReal.ofReal (c₀ * (min δ R / 2) ^ (n - 1)) ≤
          perimeter E (Metric.ball x (min δ R / 2)) from fun h ↦ False.elim (hx h))⟩
  choose r hr using htotal
  obtain ⟨u, hut, hud, hcover⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_ball t id r (min δ R)
      (fun x hx ↦ (hr x).2.1) 4 (by norm_num)
  have huc : u.Countable := hud.countable_of_isOpen (fun _ _ ↦ Metric.isOpen_ball)
    (fun x hx ↦ ⟨x, Metric.mem_ball_self (hr x).1⟩)
  refine ⟨u, r, huc, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨(hr x).1, (hr x).2.1.trans (min_le_left _ _)⟩
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := hcover x hx
    exact mem_iUnion.mpr ⟨y, mem_iUnion.mpr ⟨hy, hxy (Metric.mem_ball_self (hr x).1)⟩⟩
  · have hballs : ∀ x : u, Metric.ball (x : Euc n) (r x) ⊆ Metric.ball c (2 * R) := by
      intro x y hy
      have hx := (hut x.property).2
      simp only [Metric.mem_ball] at hx hy ⊢
      have hrR := (hr x).2.1.trans (min_le_right δ R)
      calc dist y c ≤ dist y x + dist (x : Euc n) c := dist_triangle _ _ _
        _ < 2 * R := by linarith
    have hsum := perimeter_tsum_disjoint_le E
      (fun x : u ↦ Metric.ball (x : Euc n) (r x)) (Metric.ball c (2 * R))
      (fun x y h ↦ hud x.property y.property (fun hxy ↦ h (Subtype.ext hxy))) hballs
    have hweigh : ENNReal.ofReal c₀ * ∑' x : u, ENNReal.ofReal (r x) ^ (n - 1) ≤
        perimeter E (Metric.ball c (2 * R)) := by
      rw [← ENNReal.tsum_mul_left]
      apply le_trans (ENNReal.tsum_le_tsum (fun x : u ↦ ?_)) hsum
      rw [← ENNReal.ofReal_pow (hr x).1.le, ← ENNReal.ofReal_mul hc₀.le]
      exact (hr x).2.2 (hut x.property)
    calc
      _ = (ENNReal.ofReal c₀)⁻¹ *
          (ENNReal.ofReal c₀ * ∑' x : u, ENNReal.ofReal (r x) ^ (n - 1)) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr hc₀)
          ENNReal.ofReal_ne_top, one_mul]
      _ ≤ _ := mul_le_mul le_rfl hweigh (by positivity) (by positivity)

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack

theorem hausdorffMeasure_le_perimeter_of_lower_density {n : ℕ} (E S : Set (Euc n))
    {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hdensity : ∀ x ∈ S, ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal (c₀ * r ^ (n - 1)) ≤ perimeter E (Metric.ball x r))
    (c : Euc n) {R : ℝ} (hR : 0 < R) :
    Measure.hausdorffMeasure (n - 1 : ℕ) (S ∩ Metric.ball c R) ≤
      (8 : ℝ≥0∞) ^ (n - 1) * (ENNReal.ofReal c₀)⁻¹ *
        perimeter E (Metric.ball c (2 * R)) := by
  classical
  let δ : ℕ → ℝ := fun j ↦ 1 / (j + 1)
  have hδ : ∀ j, 0 < δ j := fun j ↦ by dsimp [δ]; positivity
  choose u r hcount hr hcover hsum using fun j ↦
    exists_perimeter_vitali_cover E S hc₀ hdensity c hR (hδ j)
  let : ∀ j, Countable (u j) := fun j ↦ (hcount j).to_subtype
  have hediam : ∀ j (x : u j),
      Metric.ediam (Metric.ball (x : Euc n) (4 * r j x)) ≤
        ENNReal.ofReal (8 * r j x) := by
    intro j x
    apply Metric.ediam_le
    intro y hy z hz
    rw [edist_dist]
    apply ENNReal.ofReal_le_ofReal
    simp only [Metric.mem_ball] at hy hz
    calc dist y z ≤ dist y x + dist z x := dist_triangle_right _ _ _
      _ ≤ 8 * r j x := by linarith
  have hδlim : Tendsto (fun j ↦ ENNReal.ofReal (8 * δ j)) atTop (𝓝 0) := by
    have hh : Tendsto δ atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    simpa only [Function.comp_def, mul_zero, ENNReal.ofReal_zero] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hh.const_mul 8)
  have hh := Measure.hausdorffMeasure_le_liminf_tsum ((n - 1 : ℕ) : ℝ)
    (S ∩ Metric.ball c R) (fun j ↦ ENNReal.ofReal (8 * δ j)) hδlim
    (fun j (x : u j) ↦ Metric.ball (x : Euc n) (4 * r j x))
    (Filter.Eventually.of_forall (fun j x ↦
      (hediam j x).trans (ENNReal.ofReal_le_ofReal (by
        have h := (hr j x x.property).2; linarith))))
    (Filter.Eventually.of_forall (fun j ↦ by simpa only [iUnion_subtype] using hcover j))
  apply hh.trans
  refine Filter.liminf_le_of_frequently_le ?_ (by isBoundedDefault)
  apply Filter.Eventually.frequently
  apply Filter.Eventually.of_forall
  intro j
  calc
    _ ≤ ∑' x : u j, (8 : ℝ≥0∞) ^ (n - 1) *
        ENNReal.ofReal (r j x) ^ (n - 1) := by
      apply ENNReal.tsum_le_tsum
      intro x
      rw [ENNReal.rpow_natCast]
      calc
        _ ≤ (ENNReal.ofReal (8 * r j x)) ^ (n - 1) := pow_le_pow_left' (hediam j x) _
        _ = _ := by rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8), mul_pow]; norm_num
    _ = (8 : ℝ≥0∞) ^ (n - 1) * ∑' x : u j, ENNReal.ofReal (r j x) ^ (n - 1) :=
      ENNReal.tsum_mul_left
    _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul le_rfl (hsum j) (by positivity) (by positivity)

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack

theorem exists_minimizing_surfaceMeasure_growth_of_halfspace {n : ℕ} (hn : 8 ≤ n)
    {E Z : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    (hZd : dimH Z ≤ (n - 8 : ℕ))
    (hhalf : ∀ x ∈ perimeterSupport E \ Z, ∃ v, HasHalfspaceBlowup E x v) :
    ∃ A : ℝ, 0 < A ∧ ∀ (c : Euc n) (r : ℝ), 0 < r →
      RPI.Boundary.surfaceMeasure (perimeterSupport E) (Metric.ball c r) ≤
        ENNReal.ofReal (A * r ^ (n - 1)) := by
  obtain ⟨c₀, hc₀, hdensity₀⟩ := exists_halfspace_perimeter_lower_density_constant n (by omega)
  obtain ⟨C, hC, hperim⟩ := exists_locallyMinimizing_perimeter_growth_constant n (by omega)
  have hdensity : ∀ x ∈ perimeterSupport E \ Z, ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
      ENNReal.ofReal (c₀ * r ^ (n - 1)) ≤ perimeter E (Metric.ball x r) := by
    intro x hx
    obtain ⟨v, hv⟩ := hhalf x hx
    exact hdensity₀ E hmin.1 x v hv
  have hZnull : Measure.hausdorffMeasure (n - 1 : ℕ) Z = 0 := by
    apply hausdorffMeasure_of_dimH_lt (d := (n - 1 : ℕ))
    apply hZd.trans_lt
    exact_mod_cast (show n - 8 < n - 1 by omega)
  let K : ℝ≥0∞ := (8 : ℝ≥0∞) ^ (n - 1) * (ENNReal.ofReal c₀)⁻¹ *
    ENNReal.ofReal C * (2 : ℝ≥0∞) ^ (n - 1)
  have hK : K ≠ ⊤ := by
    unfold K
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by finiteness)
        (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr hc₀)))
      ENNReal.ofReal_ne_top) (by finiteness)
  have hraw : ∀ (c : Euc n) (r : ℝ), 0 < r →
      Measure.hausdorffMeasure (n - 1 : ℕ) (Metric.ball c r ∩ perimeterSupport E) ≤
        K * ENNReal.ofReal r ^ (n - 1) := by
    intro c r hr
    have heq : (Metric.ball c r ∩ perimeterSupport E) \ Z =
        (perimeterSupport E \ Z) ∩ Metric.ball c r := by ext x; simp only [Set.mem_sdiff, mem_inter_iff]; tauto
    rw [← measure_sdiff_null hZnull, heq]
    calc
      _ ≤ (8 : ℝ≥0∞) ^ (n - 1) * (ENNReal.ofReal c₀)⁻¹ *
          perimeter E (Metric.ball c (2 * r)) :=
        hausdorffMeasure_le_perimeter_of_lower_density E (perimeterSupport E \ Z) hc₀ hdensity c hr
      _ ≤ (8 : ℝ≥0∞) ^ (n - 1) * (ENNReal.ofReal c₀)⁻¹ *
          ENNReal.ofReal (C * (2 * r) ^ (n - 1)) := by
        exact mul_le_mul le_rfl (hperim E hmin c (2 * r) (by positivity)) (by positivity) (by positivity)
      _ = _ := by
        rw [ENNReal.ofReal_mul hC.le, ENNReal.ofReal_pow (by positivity),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num only [ENNReal.ofReal_ofNat]
        simp only [K, mul_pow, mul_assoc]
  let a : ℝ≥0∞ := (Measure.addHaarScalarFactor (volume : Measure (Euc (n - 1)))
    (Measure.hausdorffMeasure ((n - 1 : ℕ) : ℝ)) : ℝ≥0∞)
  let A : ℝ := (a * K).toReal + 1
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A, hA, ?_⟩
  intro c r hr
  have haK : a * K ≤ ENNReal.ofReal A := by
    rw [← ENNReal.ofReal_toReal (ENNReal.mul_ne_top ENNReal.coe_ne_top hK)]
    exact ENNReal.ofReal_le_ofReal (by dsimp [A]; linarith)
  rw [RPI.Boundary.surfaceMeasure, Measure.restrict_apply measurableSet_ball,
    Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, ENNReal.smul_def]
  change a * Measure.hausdorffMeasure (n - 1 : ℕ) (Metric.ball c r ∩ perimeterSupport E) ≤ _
  calc
    _ ≤ a * (K * ENNReal.ofReal r ^ (n - 1)) :=
      mul_le_mul le_rfl (hraw c r hr) (by positivity) (by positivity)
    _ ≤ ENNReal.ofReal A * ENNReal.ofReal r ^ (n - 1) := by
      rw [← mul_assoc]
      exact mul_le_mul haK le_rfl (by positivity) (by positivity)
    _ = _ := by rw [ENNReal.ofReal_mul hA.le, ENNReal.ofReal_pow hr.le]

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack
open RPI RPI.Boundary

theorem min_wholeBoundarySobolev_and_supersolution_of_minimizing_regular_geometry
    {n : ℕ} (hn : 8 ≤ n) {E Z : Set (Euc n)}
    (hmin : IsLocallyPerimeterMinimizing E)
    (hZ : IsClosed Z) (hZd : dimH Z ≤ (n - 8 : ℕ))
    (hreg : ∀ x ∈ perimeterSupport E \ Z, ∃ U : Set (Euc n), IsOpen U ∧ x ∈ U ∧
      ∃ f : Euc n → ℝ, ContDiffOn ℝ ∞ f U ∧
        (∀ y ∈ U, fderiv ℝ f y ≠ 0) ∧
        (∀ y ∈ U, y ∈ perimeterSupport E ↔ f y = 0) ∧
        (∀ y ∈ U, (f y < 0 → y ∈ E) ∧ (y ∈ E → f y ≤ 0)))
    {W : Euc n → ℝ} {D : Euc n → Euc n}
    (htrace : ∀ x ∈ perimeterSupport E \ Z, HasSmoothTraceJetAt (perimeterSupport E) W D x)
    (hW0 : ∀ x ∈ perimeterSupport E \ Z, 0 ≤ W x)
    (hsup : ∀ φ : Euc n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      Disjoint (tsupport φ) Z → (∀ x, 0 ≤ φ x) →
      0 ≤ ∫ x, inner ℝ (D x) (surfaceGradient (perimeterSupport E) φ x)
        ∂surfaceMeasure (perimeterSupport E)) :
    WholeBoundarySobolev E (fun x ↦ min (W x) 1) (truncatedGradient W D) ∧
      WholeBoundarySupersolution E (truncatedGradient W D) := by
  have hhalf : ∀ x ∈ perimeterSupport E \ Z, ∃ v, HasHalfspaceBlowup E x v := by
    intro x hx
    obtain ⟨U, hU, hxU, f, hf, hdf, hs, he⟩ := hreg x hx
    refine ⟨_, hasHalfspaceBlowup_gradient_filled hmin.1
      ((hf.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by norm_num))
      ((hs x hxU).mp hx.1) (hdf x hxU) ?_⟩
    filter_upwards [hU.mem_nhds hxU] with y hy using he y hy
  obtain ⟨A, hA, harea⟩ := exists_minimizing_surfaceMeasure_growth_of_halfspace hn hmin hZd hhalf
  apply min_wholeBoundarySobolev_and_supersolution_of_regular_geometry hn hmin.1 hZ hZd
    (fun R hR ↦ (harea 0 R hR).trans_lt ENNReal.ofReal_lt_top) _ hreg htrace hW0 hsup
  intro R hR
  refine ⟨A, 1, hA, by norm_num, ?_⟩
  intro c hc r hr hrr
  exact (Measure.restrict_apply_le (Metric.ball 0 R) (Metric.ball c r)).trans (harea c r hr)

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPI.Boundary
open scoped Convolution
open ContinuousLinearMap

noncomputable def c1Mollifier {n : ℕ} (j : ℕ) : ContDiffBump (0 : Space n) :=
  ⟨((j : ℝ) + 1)⁻¹ / 2, ((j : ℝ) + 1)⁻¹,
    half_pos (by positivity), half_lt_self (by positivity)⟩

noncomputable def c1Mollify {n : ℕ} (f : Space n → ℝ) (j : ℕ) : Space n → ℝ :=
  (c1Mollifier j).normed volume ⋆[lsmul ℝ ℝ, volume] f

lemma c1Mollifier_radius_tendsto {n : ℕ} :
    Tendsto (fun j ↦ (c1Mollifier (n := n) j).rOut) atTop (𝓝 0) := by
  simpa only [c1Mollifier, one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

lemma c1Mollify_contDiff {n : ℕ} {f : Space n → ℝ} (hf : Continuous f) (j : ℕ) :
    ContDiff ℝ ∞ (c1Mollify f j) :=
  (c1Mollifier j).hasCompactSupport_normed.contDiff_convolution_left _
    (c1Mollifier j).contDiff_normed hf.locallyIntegrable

lemma c1Mollify_hasCompactSupport {n : ℕ} {f : Space n → ℝ}
    (hc : HasCompactSupport f) (j : ℕ) : HasCompactSupport (c1Mollify f j) :=
  (c1Mollifier j).hasCompactSupport_normed.convolution _ hc

lemma c1Mollify_fderiv {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) (j : ℕ) (x : Space n) :
    fderiv ℝ (c1Mollify f j) x =
      ((c1Mollifier j).normed volume ⋆[lsmul ℝ ℝ, volume] fderiv ℝ f) x := by
  have he : (lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).precompR (Space n) =
      (lsmul ℝ ℝ : ℝ →L[ℝ] (Space n →L[ℝ] ℝ) →L[ℝ] (Space n →L[ℝ] ℝ)) := by
    ext scalar linearMap
    rfl
  simpa only [c1Mollify, he] using
    (hc.hasFDerivAt_convolution_right (lsmul ℝ ℝ)
      (c1Mollifier j).continuous_normed.locallyIntegrable hf x).fderiv

lemma c1Mollify_tendsto {n : ℕ} {f : Space n → ℝ} (hf : Continuous f) (x : Space n) :
    Tendsto (fun j ↦ c1Mollify f j x) atTop (𝓝 (f x)) :=
  ContDiffBump.convolution_tendsto_right_of_continuous c1Mollifier_radius_tendsto hf x

lemma c1Mollify_fderiv_tendsto {n : ℕ} {f : Space n → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) (x : Space n) :
    Tendsto (fun j ↦ fderiv ℝ (c1Mollify f j) x) atTop (𝓝 (fderiv ℝ f x)) := by
  simp_rw [c1Mollify_fderiv hf hc]
  exact ContDiffBump.convolution_tendsto_right_of_continuous
    c1Mollifier_radius_tendsto (hf.continuous_fderiv one_ne_zero) x

lemma c1Mollify_nonneg {n : ℕ} {f : Space n → ℝ} (hf : ∀ x, 0 ≤ f x)
    (j : ℕ) (x : Space n) : 0 ≤ c1Mollify f j x := by
  apply integral_nonneg
  intro t
  exact mul_nonneg ((c1Mollifier j).nonneg_normed t) (hf _)

lemma c1Mollify_uniform_bound {n : ℕ} {f : Space n → ℝ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    ∃ M : ℝ, 0 < M ∧ ∀ j x, ‖c1Mollify f j x‖ ≤ M ∧
      ‖fderiv ℝ (c1Mollify f j) x‖ ≤ M := by
  obtain ⟨A, hA⟩ := hf.continuous.bounded_above_of_compact_support hc
  obtain ⟨B, hB⟩ := (hf.continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    (hc.fderiv ℝ)
  let M := 3 * (|A| + |B| + 1)
  refine ⟨M, by dsimp [M]; positivity, ?_⟩
  intro j x
  have h1 : dist (c1Mollify f j x) (f x) ≤ 2 * |A| := by
    apply (c1Mollifier j).dist_normed_convolution_le hf.continuous.aestronglyMeasurable
    intro y hy
    calc
      dist (f y) (f x) ≤ ‖f y‖ + ‖f x‖ := dist_le_norm_add_norm _ _
      _ ≤ 2 * |A| := by have := hA y; have := hA x; have := le_abs_self A; linarith
  have h2 : dist (fderiv ℝ (c1Mollify f j) x) (fderiv ℝ f x) ≤ 2 * |B| := by
    rw [c1Mollify_fderiv hf hc]
    apply (c1Mollifier j).dist_normed_convolution_le
      (hf.continuous_fderiv one_ne_zero).aestronglyMeasurable
    intro y hy
    calc
      dist (fderiv ℝ f y) (fderiv ℝ f x) ≤ ‖fderiv ℝ f y‖ + ‖fderiv ℝ f x‖ :=
        dist_le_norm_add_norm _ _
      _ ≤ 2 * |B| := by have := hB y; have := hB x; have := le_abs_self B; linarith
  constructor
  · have := dist_triangle (c1Mollify f j x) (f x) 0
    simp only [dist_zero_right] at this
    have := hA x
    dsimp [M]
    have := le_abs_self A
    have := abs_nonneg B
    simp only [Real.norm_eq_abs] at *
    linarith
  · have := dist_triangle (fderiv ℝ (c1Mollify f j) x) (fderiv ℝ f x) 0
    simp only [dist_zero_right] at this
    have := hB x
    dsimp [M]
    have := le_abs_self B
    have := abs_nonneg A
    linarith

lemma c1Mollify_tsupport_subset {n : ℕ} (f : Space n → ℝ) (j : ℕ) :
    tsupport (c1Mollify f j) ⊆ Metric.cthickening (c1Mollifier (n := n) j).rOut (tsupport f) := by
  apply closure_minimal _ Metric.isClosed_cthickening
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := support_convolution_subset_swap (lsmul ℝ ℝ) hx
  rw [(c1Mollifier j).support_normed_eq] at hz
  apply Metric.mem_cthickening_of_dist_le _ y _ _ (subset_closure hy)
  simpa only [dist_eq_norm, add_sub_cancel_left, sub_zero] using (Metric.mem_ball.mp hz).le

lemma c1Mollify_eventually_tsupport_subset {n : ℕ} {f : Space n → ℝ}
    (hc : HasCompactSupport f) {U : Set (Space n)} (hU : IsOpen U) (hs : tsupport f ⊆ U) :
    ∀ᶠ j in atTop, tsupport (c1Mollify f j) ⊆ U := by
  obtain ⟨r, hr, hsub⟩ := hc.exists_cthickening_subset_open hU hs
  filter_upwards [c1Mollifier_radius_tendsto.eventually (gt_mem_nhds hr)] with j hj
  exact (c1Mollify_tsupport_subset f j).trans ((Metric.cthickening_mono hj.le _).trans hsub)

end RPI.Boundary

end

end OAI

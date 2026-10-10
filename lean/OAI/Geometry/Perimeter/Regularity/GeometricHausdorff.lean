import OAI.Geometry.Perimeter.Regularity.ContinuousWithinAtSurfaceGradientOfLocalLevel

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
namespace RPISingularHarnack

def geometricHausdorff {n : ℕ} (k : ℕ) : Measure (Euc n) :=
  ((volume (Metric.ball (0 : Euc k) 1)) / (2 : ℝ≥0∞) ^ k) •
    Measure.hausdorffMeasure (k : ℝ)

def hausdorffNormalizationRatio (k : ℕ) : ℝ≥0∞ :=
  ((volume (Metric.ball (0 : Euc k) 1)) / (2 : ℝ≥0∞) ^ k) /
    (Measure.addHaarScalarFactor (volume : Measure (Euc k))
      (Measure.hausdorffMeasure (k : ℝ)) : ℝ≥0∞)

theorem hausdorffNormalizationRatio_ne_zero (k : ℕ) :
    hausdorffNormalizationRatio k ≠ 0 := by
  apply ENNReal.div_ne_zero.mpr
  constructor
  · apply ENNReal.div_ne_zero.mpr
    constructor
    · exact (Metric.measure_ball_pos volume 0 (by norm_num : (0 : ℝ) < 1)).ne'
    · exact ENNReal.pow_ne_top (by norm_num)
  · exact ENNReal.coe_ne_top

theorem hausdorffNormalizationRatio_ne_top (k : ℕ) :
    hausdorffNormalizationRatio k ≠ ⊤ := by
  apply ENNReal.div_ne_top
  · apply ENNReal.div_ne_top
    · exact measure_ball_ne_top
    · exact pow_ne_zero _ (by norm_num)
  · exact_mod_cast Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero k

theorem geometricHausdorff_eq_smul_euclideanHausdorff {n : ℕ} (k : ℕ) :
    (geometricHausdorff k : Measure (Euc n)) =
      hausdorffNormalizationRatio k • Measure.euclideanHausdorffMeasure k := by
  rw [geometricHausdorff, Measure.euclideanHausdorffMeasure_def,
    ENNReal.smul_def, smul_smul, hausdorffNormalizationRatio]
  rw [ENNReal.div_mul_cancel (by exact_mod_cast
    Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero k) ENNReal.coe_ne_top]

def boundaryArea {n : ℕ} (E : Set (Euc n)) : Measure (Euc n) :=
  (geometricHausdorff (n - 1)).restrict (perimeterSupport E)

def WholeBoundarySobolev {n : ℕ} (E : Set (Euc n))
    (h : Euc n → ℝ) (G : Euc n → Euc n) : Prop :=
  ∀ R : ℝ, 0 < R →
    let μ := (boundaryArea E).restrict (Metric.ball 0 R)
    MemLp h 2 μ ∧ MemLp G 2 μ ∧
    ∃ φ : ℕ → Euc n → ℝ,
      (∀ j, ContDiff ℝ ∞ (φ j) ∧ HasCompactSupport (φ j)) ∧
      Tendsto (fun j => ∫⁻ x, ENNReal.ofReal (|φ j x - h x| ^ 2) ∂μ)
        atTop (𝓝 0) ∧
      Tendsto (fun j => ∫⁻ x,
        ENNReal.ofReal (‖tangentialGradient E (φ j) x - G x‖ ^ 2) ∂μ)
        atTop (𝓝 0)

def WholeBoundarySupersolution {n : ℕ} (E : Set (Euc n))
    (G : Euc n → Euc n) : Prop :=
  ∀ φ : Euc n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    (∀ x, 0 ≤ φ x) →
    0 ≤ ∫ x, inner ℝ (G x) (tangentialGradient E φ x) ∂boundaryArea E

def ZeroEssentialInfAtVertex {n : ℕ} (E : Set (Euc n)) (h : Euc n → ℝ) : Prop :=
  ∀ R : ℝ, 0 < R → ∀ ε : ℝ, 0 < ε →
    0 < boundaryArea E (Metric.ball 0 R ∩ {x | h x < ε})

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
namespace RPI.Boundary

theorem surfaceGradient_ae_eq_tangentialGradient {n : ℕ} (hn : 8 ≤ n)
    {E S Z : Set (Space n)} (hE : MeasurableSet E) (hS : MeasurableSet S)
    (hZd : dimH Z ≤ (n - 8 : ℕ))
    (hreg : ∀ x ∈ S \ Z, ∃ f : Space n → ℝ,
      ContDiffAt ℝ 1 f x ∧ f x = 0 ∧ fderiv ℝ f x ≠ 0 ∧
      (∀ᶠ y in 𝓝 x, y ∈ S ↔ f y = 0) ∧
      (∀ᶠ y in 𝓝 x, y ∈ E ↔ f y < 0)) (g : Space n → ℝ) :
    surfaceGradient S g =ᵐ[surfaceMeasure S]
      RPISingularHarnack.tangentialGradient E g := by
  have hz : ∀ᵐ x ∂surfaceMeasure S, x ∉ Z := by
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using
      surfaceMeasure_zero_of_singular_dim hn S Z hZd
  filter_upwards [ae_restrict_mem hS, hz] with x hx hzx
  obtain ⟨f, hf, hfx, hdf, hlevel, hfilled⟩ := hreg x ⟨hx, hzx⟩
  exact surfaceGradient_eq_tangentialGradient hE hf hfx hdf hlevel hfilled

end RPI.Boundary

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
namespace RPISingularHarnack

theorem boundaryArea_eq_smul_surfaceMeasure {n : ℕ} (E : Set (Euc n)) :
    boundaryArea E = hausdorffNormalizationRatio (n - 1) •
      RPI.Boundary.surfaceMeasure (perimeterSupport E) := by
  rw [boundaryArea, geometricHausdorff_eq_smul_euclideanHausdorff,
    Measure.restrict_smul]
  rfl

theorem wholeBoundarySobolev_of_local_sobolevGraph {n : ℕ} (hn : 8 ≤ n)
    {E Z : Set (Euc n)} (hE : MeasurableSet E)
    (hS : MeasurableSet (perimeterSupport E)) (hZd : dimH Z ≤ (n - 8 : ℕ))
    (hreg : ∀ x ∈ perimeterSupport E \ Z, ∃ f : Euc n → ℝ,
      ContDiffAt ℝ 1 f x ∧ f x = 0 ∧ fderiv ℝ f x ≠ 0 ∧
      (∀ᶠ y in 𝓝 x, y ∈ perimeterSupport E ↔ f y = 0) ∧
      (∀ᶠ y in 𝓝 x, y ∈ E ↔ f y < 0))
    {h : Euc n → ℝ} {G : Euc n → Euc n}
    (hgraph : ∀ R : ℝ, 0 < R →
      ∃ (hh : MemLp h 2 ((RPI.Boundary.surfaceMeasure (perimeterSupport E)).restrict
          (Metric.ball 0 R)))
        (hG : MemLp G 2 ((RPI.Boundary.surfaceMeasure (perimeterSupport E)).restrict
          (Metric.ball 0 R))),
        (hh.toLp h, hG.toLp G) ∈ closure
          (RPI.Boundary.smoothGradientGraph (perimeterSupport E) (Metric.ball 0 R))) :
    WholeBoundarySobolev E h G := by
  intro R hR
  obtain ⟨hh, hG, hpair⟩ := hgraph R hR
  obtain ⟨φ, hφ, hlim, hDlim⟩ :=
    RPI.Boundary.exists_compact_energy_approximants_of_mem_sobolevGraph
      (perimeterSupport E) (Metric.ball 0 R) Metric.isBounded_ball
      measurableSet_ball hh hG hpair
  dsimp only
  rw [boundaryArea_eq_smul_surfaceMeasure, Measure.restrict_smul]
  refine ⟨hh.smul_measure (hausdorffNormalizationRatio_ne_top _),
    hG.smul_measure (hausdorffNormalizationRatio_ne_top _), φ, hφ, ?_, ?_⟩
  · simp_rw [lintegral_smul_measure, smul_eq_mul]
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hlim
      (Or.inr (hausdorffNormalizationRatio_ne_top (n - 1)))
  · have heq : ∀ j, RPI.Boundary.surfaceGradient (perimeterSupport E) (φ j)
        =ᵐ[(RPI.Boundary.surfaceMeasure (perimeterSupport E)).restrict (Metric.ball 0 R)]
          tangentialGradient E (φ j) := fun j ↦
      (RPI.Boundary.surfaceGradient_ae_eq_tangentialGradient hn hE hS hZd hreg (φ j)).filter_mono
        (ae_mono Measure.restrict_le_self)
    have hl : Tendsto (fun j ↦ ∫⁻ x,
        ENNReal.ofReal (‖tangentialGradient E (φ j) x - G x‖ ^ 2)
        ∂(RPI.Boundary.surfaceMeasure (perimeterSupport E)).restrict (Metric.ball 0 R))
        atTop (𝓝 0) := by
      apply hDlim.congr
      intro j
      apply lintegral_congr_ae
      filter_upwards [heq j] with x hx
      rw [hx]
    simp_rw [lintegral_smul_measure, smul_eq_mul]
    simpa only [mul_zero] using ENNReal.Tendsto.const_mul hl
      (Or.inr (hausdorffNormalizationRatio_ne_top (n - 1)))

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
namespace RPISingularHarnack

theorem eventually_filled_membership {n : ℕ} {E : Set (Euc n)}
    {f : Euc n → ℝ} {x z : Euc n} {L : Euc n →L[ℝ] ℝ}
    (hd : HasFDerivAt f L x) (hx : f x = 0)
    (hlocal : ∀ᶠ y in 𝓝 x, (f y < 0 → y ∈ E) ∧ (y ∈ E → f y ≤ 0)) (hz : L z ≠ 0) :
    ∀ᶠ r : ℝ in 𝓝[>] 0, x + r • z ∈ E ↔ L z < 0 := by
  have hp : HasDerivAt (fun r : ℝ ↦ x + r • z) z 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const z).const_add x
  have hc : HasDerivAt (fun r : ℝ ↦ f (x + r • z)) (L z) 0 := by
    exact (show HasFDerivAt f L (x + (0 : ℝ) • z) from by simpa using hd).comp_hasDerivAt 0 hp
  have ht : Tendsto (fun r : ℝ ↦ r⁻¹ * f (x + r • z)) (𝓝[>] 0) (𝓝 (L z)) := by
    simpa [hx] using hc.tendsto_slope_zero_right
  have hm : ∀ᶠ r : ℝ in 𝓝[>] 0,
      (f (x + r • z) < 0 → x + r • z ∈ E) ∧
      (x + r • z ∈ E → f (x + r • z) ≤ 0) :=
    (show Tendsto (fun r : ℝ ↦ x + r • z) (𝓝[>] 0) (𝓝 x) from
      (show Tendsto (fun r : ℝ ↦ x + r • z) (𝓝 0) (𝓝 x) from by
        simpa [ContinuousAt] using hp.continuousAt).mono_left nhdsWithin_le_nhds).eventually hlocal
  rcases lt_or_gt_of_ne hz with hneg | hpos
  · filter_upwards [hm, ht.eventually (gt_mem_nhds hneg), self_mem_nhdsWithin] with r hm hr hpr
    have hfr : f (x + r • z) < 0 := by
      have hi : 0 < r⁻¹ := inv_pos.mpr hpr
      nlinarith
    exact iff_of_true (hm.1 hfr) hneg
  · filter_upwards [hm, ht.eventually (lt_mem_nhds hpos), self_mem_nhdsWithin] with r hm hr hpr
    have hfr : 0 < f (x + r • z) := by
      have hi : 0 < r⁻¹ := inv_pos.mpr hpr
      nlinarith
    exact iff_of_false (fun he ↦ (not_le.mpr hfr) (hm.2 he)) (not_lt.mpr hpos.le)

theorem hasHalfspaceBlowup_of_regular_filled_chart {n : ℕ} {E : Set (Euc n)}
    (hE : MeasurableSet E) {f : Euc n → ℝ} {x v : Euc n} {L : Euc n →L[ℝ] ℝ}
    (hd : HasFDerivAt f L x) (hx : f x = 0)
    (hlocal : ∀ᶠ y in 𝓝 x, (f y < 0 → y ∈ E) ∧ (y ∈ E → f y ≤ 0))
    (hv : ‖v‖ = 1) {a : ℝ} (ha : 0 < a)
    (hL : ∀ z, L z = a * inner ℝ z v) : HasHalfspaceBlowup E x v := by
  have hLn : L ≠ 0 := by
    intro he
    have hval := hL v
    simp only [he, zero_apply, real_inner_self_eq_norm_sq, hv,
      one_pow, mul_one] at hval
    linarith
  let H : Set (Euc n) := {z | inner ℝ z v < 0}
  have hH : MeasurableSet H :=
    (isOpen_lt (continuous_id.inner continuous_const) continuous_const).measurableSet
  let F : ℝ → Euc n → ℝ := fun r z ↦
    |E.indicator (fun _ ↦ (1 : ℝ)) (x + r • z) - H.indicator (fun _ ↦ (1 : ℝ)) z|
  have hsign : ∀ z, L z < 0 ↔ inner ℝ z v < 0 := by
    intro z
    rw [hL]
    constructor <;> intro h <;> nlinarith
  have hmeas : ∀ r, AEStronglyMeasurable (F r)
      (volume.restrict (Metric.ball (0 : Euc n) 1)) := by
    intro r
    have he : Measurable (E.indicator (fun _ : Euc n ↦ (1 : ℝ))) :=
      measurable_const.indicator hE
    have hh : Measurable (H.indicator (fun _ : Euc n ↦ (1 : ℝ))) :=
      measurable_const.indicator hH
    have hm : Measurable (fun z : Euc n ↦ x + r • z) :=
      measurable_const.add (measurable_id.const_smul r)
    exact ((he.comp hm).sub hh).abs.aestronglyMeasurable
  have hb : ∀ r, ∀ᵐ z ∂volume.restrict (Metric.ball (0 : Euc n) 1), ‖F r z‖ ≤ 1 := by
    intro r
    filter_upwards [] with z
    by_cases he : x + r • z ∈ E <;> by_cases hh : z ∈ H <;> simp [F, he, hh]
  have ht : ∀ᵐ z ∂volume.restrict (Metric.ball (0 : Euc n) 1),
      Tendsto (fun r ↦ F r z) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    filter_upwards [ae_restrict_of_ae (ae_linear_ne_zero hLn)] with z hz
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_filled_membership hd hx hlocal hz] with r hr
    have hmem : x + r • z ∈ E ↔ z ∈ H := hr.trans (hsign z)
    by_cases he : x + r • z ∈ E
    · simp [F, he, hmem.mp he]
    · have hhn : z ∉ H := fun hh ↦ he (hmem.mpr hh)
      simp only [F, Set.indicator_of_notMem he, Set.indicator_of_notMem hhn,
        sub_self, abs_zero]
  have hi : Integrable (fun _ : Euc n ↦ (1 : ℝ))
      (volume.restrict (Metric.ball 0 1)) := integrableOn_const measure_ball_lt_top.ne
  have hconv := tendsto_integral_filter_of_dominated_convergence
    (fun _ : Euc n ↦ (1 : ℝ)) (Eventually.of_forall hmeas) (Eventually.of_forall hb) hi ht
  refine ⟨hv, ?_⟩
  have heq : ∀ᶠ r : ℝ in 𝓝[>] 0,
      (r ^ n)⁻¹ * (∫ y in Metric.ball x r,
        |E.indicator (fun _ ↦ (1 : ℝ)) y -
          {z | inner ℝ (z - x) v < 0}.indicator (fun _ ↦ (1 : ℝ)) y|) =
        ∫ z in Metric.ball (0 : Euc n) 1, F r z := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [normalized_ball_integral _ x hr]
    apply integral_congr_ae
    filter_upwards [] with z
    simp only [halfspace_indicator_rescale x v z hr, F, H]
  exact (show Tendsto (fun r ↦ ∫ z in Metric.ball (0 : Euc n) 1, F r z)
    (𝓝[>] (0 : ℝ)) (𝓝 0) from by simpa only [integral_zero] using hconv).congr' (Filter.EventuallyEq.symm heq)

theorem hasHalfspaceBlowup_gradient_filled {n : ℕ} {E : Set (Euc n)}
    (hE : MeasurableSet E) {f : Euc n → ℝ} {x : Euc n}
    (hd : DifferentiableAt ℝ f x) (hx : f x = 0) (hdf : fderiv ℝ f x ≠ 0)
    (hlocal : ∀ᶠ y in 𝓝 x, (f y < 0 → y ∈ E) ∧ (y ∈ E → f y ≤ 0)) :
    HasHalfspaceBlowup E x (‖gradient f x‖⁻¹ • gradient f x) := by
  have hg : gradient f x ≠ 0 := by
    intro he
    apply hdf
    ext z
    rw [← inner_gradient_left, he, inner_zero_left]
    rfl
  have hng : 0 < ‖gradient f x‖ := norm_pos_iff.mpr hg
  apply hasHalfspaceBlowup_of_regular_filled_chart hE hd.hasFDerivAt hx hlocal
    (a := ‖gradient f x‖)
  · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hng.le), inv_mul_cancel₀ hng.ne']
  · exact hng
  · intro z
    rw [real_inner_smul_right, ← inner_gradient_left, real_inner_comm]
    field_simp

theorem approximateNormal_eq_gradient_filled {n : ℕ} {E : Set (Euc n)}
    (hE : MeasurableSet E) {f : Euc n → ℝ} {x : Euc n}
    (hd : DifferentiableAt ℝ f x) (hx : f x = 0) (hdf : fderiv ℝ f x ≠ 0)
    (hlocal : ∀ᶠ y in 𝓝 x, (f y < 0 → y ∈ E) ∧ (y ∈ E → f y ≤ 0)) :
    approximateNormal E x = ‖gradient f x‖⁻¹ • gradient f x :=
  approximateNormal_eq_of_blowup hE
    (hasHalfspaceBlowup_gradient_filled hE hd hx hdf hlocal)

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPI

def truncationSlope (ε t : ℝ) : ℝ := Real.smoothTransition ((1 - t) / ε)

def smoothTruncation (ε s : ℝ) : ℝ := ∫ t in (0 : ℝ)..s, truncationSlope ε t

theorem truncationSlope_contDiff (ε : ℝ) : ContDiff ℝ ∞ (truncationSlope ε) := by
  unfold truncationSlope
  fun_prop

theorem smoothTruncation_hasDerivAt (ε s : ℝ) :
    HasDerivAt (smoothTruncation ε) (truncationSlope ε s) s := by
  have hc := (truncationSlope_contDiff ε).continuous
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 s)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

@[simp] theorem smoothTruncation_deriv (ε s : ℝ) :
    deriv (smoothTruncation ε) s = truncationSlope ε s :=
  (smoothTruncation_hasDerivAt ε s).deriv

theorem smoothTruncation_contDiff (ε : ℝ) : ContDiff ℝ ∞ (smoothTruncation ε) := by
  rw [contDiff_infty_iff_deriv]
  exact ⟨fun s ↦ (smoothTruncation_hasDerivAt ε s).differentiableAt,
    by simpa only [funext (smoothTruncation_deriv ε)] using truncationSlope_contDiff ε⟩

theorem truncationSlope_mem_Icc (ε t : ℝ) : truncationSlope ε t ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem truncationSlope_antitone {ε : ℝ} (hε : 0 < ε) : Antitone (truncationSlope ε) := by
  intro s t hst
  apply Real.smoothTransition.monotone
  exact div_le_div_of_nonneg_right (sub_le_sub_left hst 1) hε.le

theorem smoothTruncation_second_deriv_nonpos {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    deriv (deriv (smoothTruncation ε)) s ≤ 0 := by
  rw [show deriv (smoothTruncation ε) = truncationSlope ε from funext (smoothTruncation_deriv ε)]
  exact (truncationSlope_antitone hε).deriv_nonpos

@[simp] theorem smoothTruncation_zero (ε : ℝ) : smoothTruncation ε 0 = 0 := by
  simp [smoothTruncation]

theorem smoothTruncation_monotone (ε : ℝ) : Monotone (smoothTruncation ε) := by
  apply monotone_of_deriv_nonneg
  · exact fun s ↦ (smoothTruncation_hasDerivAt ε s).differentiableAt
  · intro s
    rw [smoothTruncation_deriv]
    exact (truncationSlope_mem_Icc ε s).1

theorem smoothTruncation_nonneg (ε : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ smoothTruncation ε s := by
  simpa only [smoothTruncation_zero] using smoothTruncation_monotone ε hs

theorem smoothTruncation_le_self (ε : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    smoothTruncation ε s ≤ s := by
  have h := intervalIntegral.integral_mono hs
    ((truncationSlope_contDiff ε).continuous.intervalIntegrable 0 s)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ ↦ (1 : ℝ)) volume 0 s)
    (fun t ↦ (truncationSlope_mem_Icc ε t).2)
  simpa only [smoothTruncation, intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one] using h

theorem truncationSlope_eq_zero {ε : ℝ} (hε : 0 < ε) {t : ℝ} (ht : 1 ≤ t) :
    truncationSlope ε t = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) hε.le

theorem truncationSlope_eq_one {ε : ℝ} (hε : 0 < ε) {t : ℝ} (ht : t ≤ 1 - ε) :
    truncationSlope ε t = 1 := by
  apply Real.smoothTransition.one_of_one_le
  apply (le_div_iff₀ hε).mpr
  linarith

theorem smoothTruncation_eq_self {ε s : ℝ} (hε : 0 < ε) (hs : 0 ≤ s)
    (hsε : s ≤ 1 - ε) : smoothTruncation ε s = s := by
  unfold smoothTruncation
  calc
    _ = ∫ _ in (0 : ℝ)..s, (1 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact truncationSlope_eq_one hε ((uIcc_of_le hs ▸ ht).2.trans hsε)
    _ = s := by simp

theorem smoothTruncation_eq_at_one {ε s : ℝ} (hε : 0 < ε) (hs : 1 ≤ s) :
    smoothTruncation ε s = smoothTruncation ε 1 := by
  have hc := (truncationSlope_contDiff ε).continuous
  have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 1) (hc.intervalIntegrable 1 s)
  have hz : ∫ t in (1 : ℝ)..s, truncationSlope ε t = 0 := by
    calc
      _ = ∫ _ in (1 : ℝ)..s, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        exact truncationSlope_eq_zero hε ((uIcc_of_le hs ▸ ht).1)
      _ = 0 := by simp
  change _ = _
  change smoothTruncation ε 1 + (∫ t in (1 : ℝ)..s, truncationSlope ε t) =
    smoothTruncation ε s at he
  rw [hz, add_zero] at he
  exact he.symm

theorem smoothTruncation_le_min {ε s : ℝ} (hε : 0 < ε) (hs : 0 ≤ s) :
    smoothTruncation ε s ≤ min s 1 := by
  apply le_min (smoothTruncation_le_self ε hs)
  by_cases h : s ≤ 1
  · exact (smoothTruncation_le_self ε hs).trans h
  · rw [smoothTruncation_eq_at_one hε (le_of_not_ge h)]
    exact smoothTruncation_le_self ε zero_le_one

theorem min_sub_le_smoothTruncation {ε s : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hs : 0 ≤ s) : min s 1 - ε ≤ smoothTruncation ε s := by
  by_cases h : s ≤ 1 - ε
  · rw [smoothTruncation_eq_self hε hs h]
    exact (sub_le_self _ hε.le).trans (min_le_left _ _)
  · have h0 : 0 ≤ 1 - ε := sub_nonneg.mpr hε1
    have he : smoothTruncation ε (1 - ε) = 1 - ε :=
      smoothTruncation_eq_self hε h0 le_rfl
    have hm := smoothTruncation_monotone ε (le_of_not_ge h)
    rw [he] at hm
    exact (sub_le_sub_right (min_le_right s 1) ε).trans hm

def truncationParameter (j : ℕ) : ℝ := 1 / (j + 1 : ℝ)

theorem truncationParameter_pos (j : ℕ) : 0 < truncationParameter j := by
  unfold truncationParameter
  positivity

theorem truncationParameter_le_one (j : ℕ) : truncationParameter j ≤ 1 := by
  unfold truncationParameter
  apply (div_le_one (by positivity)).mpr
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  linarith

theorem truncationParameter_tendsto : Tendsto truncationParameter atTop (𝓝 (0 : ℝ)) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem smoothTruncation_tendsto {s : ℝ} (hs : 0 ≤ s) :
    Tendsto (fun j ↦ smoothTruncation (truncationParameter j) s) atTop (𝓝 (min s 1)) := by
  have hlow : Tendsto (fun j ↦ min s 1 - truncationParameter j) atTop (𝓝 (min s 1)) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub truncationParameter_tendsto
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
  · intro j
    exact min_sub_le_smoothTruncation (truncationParameter_pos j)
      (truncationParameter_le_one j) hs
  · intro j
    exact smoothTruncation_le_min (truncationParameter_pos j) hs

theorem truncationSlope_tendsto (s : ℝ) :
    Tendsto (fun j ↦ truncationSlope (truncationParameter j) s) atTop
      (𝓝 (if s < 1 then (1 : ℝ) else 0)) := by
  split_ifs with hs
  · apply tendsto_const_nhds.congr'
    filter_upwards [truncationParameter_tendsto.eventually (gt_mem_nhds (sub_pos.mpr hs))] with j hj
    symm
    exact truncationSlope_eq_one (truncationParameter_pos j) (by linarith)
  · apply tendsto_const_nhds.congr
    intro j
    symm
    exact truncationSlope_eq_zero (truncationParameter_pos j) (le_of_not_gt hs)

end RPI

end

end OAI

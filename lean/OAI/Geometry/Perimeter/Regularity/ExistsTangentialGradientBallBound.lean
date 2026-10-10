import OAI.Geometry.Perimeter.Regularity.RankOneNormalError

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
open scoped BoundedContinuousFunction
open scoped ENNReal Topology
namespace RPISingularHarnack
open RPI.Boundary

theorem exists_tangentialGradient_ball_bound {n : ℕ} (E : Set (Euc n))
    (c : Euc n) (R : ℝ) {f : Euc n → ℝ} (hf : ContDiff ℝ 1 f) :
    ∃ B : ℝ, ∀ x ∈ Metric.ball c R, ‖tangentialGradient E f x‖ ≤ B := by
  have hg : Continuous (gradient f) := continuous_iff_continuousAt.mpr (fun x ↦
    continuousAt_gradient_of_contDiffAt hf.contDiffAt)
  obtain ⟨M, hM⟩ := (isCompact_closedBall c R).exists_bound_of_continuousOn hg.continuousOn
  exact ⟨2 * M, fun x hx ↦ (tangentialGradient_norm_le_twice E f x).trans
    (by nlinarith [hM x (Metric.ball_subset_closedBall hx)])⟩

theorem tangentialDivergence_integrable_ball_perimeter {n : ℕ}
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    (c : Euc n) {R : ℝ} (hR : 0 < R) {V : Euc n → Euc n}
    (hV : ContDiff ℝ ∞ V) :
    Integrable (tangentialDivergence E V) ((perimeterMeasure E).restrict (Metric.ball c R)) := by
  change Integrable (fun x ↦ tangentialDivergence E V x) _
  simp_rw [tangentialDivergence_eq_sum E (hV.differentiable (by simp))]
  apply integrable_finsetSum
  intro i _
  exact (tangentialGradient_integrable_ball_perimeter hmin c hR
    ((contDiff_const.inner ℝ hV).of_le (by simp))).inner_const _

theorem minimizing_radial_integral_bound {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    (c a : Euc n) {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    {f : Euc n → ℝ} (hf : ContDiff ℝ ∞ f) (hcf : HasCompactSupport f)
    (hsf : tsupport f ⊆ Metric.ball c R) (hf0 : ∀ x, 0 ≤ f x) :
    (∫ x in Metric.ball c R, f x * (n - 1 : ℕ) *
      (‖x - a‖ ^ 2 + ε ^ 2) ^ (-((n - 1 : ℕ) : ℝ) / 2 - 1) * ε ^ 2 ∂perimeterMeasure E) ≤
    ∫ x in Metric.ball c R, ‖tangentialGradient E f x‖ *
      (radialKernel a ε (n - 1 : ℕ) x * ‖x - a‖) ∂perimeterMeasure E := by
  let μ := (perimeterMeasure E).restrict (Metric.ball c R)
  let W : Euc n → Euc n := fun x ↦ radialKernel a ε (n - 1 : ℕ) x • (x - a)
  have hW : ContDiff ℝ ∞ W := (radialKernel_contDiff a hε _).smul (contDiff_id.sub contDiff_const)
  have hV : ContDiff ℝ ∞ (fun x ↦ f x • W x) := hf.smul hW
  have hcV : HasCompactSupport (fun x ↦ f x • W x) := hcf.smul_right
  have hsV : tsupport (fun x ↦ f x • W x) ⊆ Metric.ball c R :=
    (tsupport_smul_subset_left _ _).trans hsf
  have hz := minimizing_tangentialDivergence_integral_eq_zero hn hmin c hR hV hcV hsV
  have := perimeterMeasure_finiteOnCompacts E hmin.2.1
  have : IsFiniteMeasure μ := ⟨by
    rw [Measure.restrict_apply_univ, perimeterMeasure_open E Metric.isOpen_ball]
    exact hmin.2.1 c R hR⟩
  have hiW : Integrable W μ := hW.continuous.continuousOn.integrableOn_of_subset_isCompact
    (isCompact_closedBall c R) measurableSet_ball Metric.ball_subset_closedBall
    (by rw [perimeterMeasure_open E Metric.isOpen_ball]; exact (hmin.2.1 c R hR).ne)
  have hmG := (measurable_tangentialGradient hmin.1 (hf.of_le (by simp))).aestronglyMeasurable (μ := μ)
  obtain ⟨B, hB⟩ := exists_tangentialGradient_ball_bound E c R (hf.of_le (by simp))
  have hGi : Integrable (fun x ↦ inner ℝ (tangentialGradient E f x) (W x)) μ := by
    apply Integrable.mono' (hiW.norm.const_mul B) (hmG.inner hW.continuous.aestronglyMeasurable)
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hB x hx) (norm_nonneg _))
  obtain ⟨D, hD⟩ := (isCompact_closedBall c R).exists_bound_of_continuousOn hf.continuous.continuousOn
  have hDi := tangentialDivergence_integrable_ball_perimeter hmin c hR hW
  have hfi : Integrable (fun x ↦ f x * tangentialDivergence E W x) μ :=
    hDi.bdd_mul hf.continuous.aestronglyMeasurable
      ((ae_restrict_mem measurableSet_ball).mono fun x hx ↦ hD x (Metric.ball_subset_closedBall hx))
  have heq : (∫ x, f x * tangentialDivergence E W x ∂μ) +
      (∫ x, inner ℝ (tangentialGradient E f x) (W x) ∂μ) = 0 := by
    rw [← integral_add hfi hGi]
    simpa only [μ, ← tangentialDivergence_smul E (hf.differentiable (by simp)) (hW.differentiable (by simp))] using hz
  have hlci : Integrable (fun x ↦ f x * (n - 1 : ℕ) *
      (‖x - a‖ ^ 2 + ε ^ 2) ^ (-((n - 1 : ℕ) : ℝ) / 2 - 1) * ε ^ 2) μ := by
    apply ContinuousOn.integrableOn_of_subset_isCompact (s := Metric.ball c R)
      (K := Metric.closedBall c R) _ (isCompact_closedBall c R) measurableSet_ball Metric.ball_subset_closedBall
      (by rw [perimeterMeasure_open E Metric.isOpen_ball]; exact (hmin.2.1 c R hR).ne)
    apply Continuous.continuousOn
    apply Continuous.mul _ continuous_const
    apply Continuous.mul (hf.continuous.mul continuous_const)
    exact (((continuous_id.sub continuous_const).norm.pow 2).add continuous_const).rpow_const
      (fun x ↦ Or.inl (by change ‖x - a‖ ^ 2 + ε ^ 2 ≠ 0; positivity))
  have hlow := integral_mono_ae hlci hfi
    ((ae_restrict_of_ae (minimizing_halfspaceBlowup_ae hn hmin)).mono fun x hx ↦ by
      dsimp [W]
      rw [tangentialDivergence_radial E (by omega) a x hε hx.1]
      have hpos : 0 ≤ (‖x - a‖ ^ 2 + ε ^ 2) ^ (-((n - 1 : ℕ) : ℝ) / 2 - 1) := by positivity
      nlinarith [mul_nonneg (mul_nonneg (hf0 x) (Nat.cast_nonneg (n - 1))) hpos,
        sq_nonneg (inner ℝ (x - a) (approximateNormal E x))])
  have hRhi : Integrable (fun x ↦ ‖tangentialGradient E f x‖ * ‖W x‖) μ :=
    hiW.norm.bdd_mul hmG.norm ((ae_restrict_mem measurableSet_ball).mono fun x hx ↦ by
      simpa only [norm_norm] using hB x hx)
  have hu := integral_mono hGi.neg hRhi (fun x ↦ (neg_le_abs _).trans (abs_real_inner_le_norm _ _))
  have hconcl : (∫ x, f x * (n - 1 : ℕ) *
      (‖x - a‖ ^ 2 + ε ^ 2) ^ (-((n - 1 : ℕ) : ℝ) / 2 - 1) * ε ^ 2 ∂μ) ≤
      ∫ x, ‖tangentialGradient E f x‖ * ‖W x‖ ∂μ := by
    simp only [Pi.neg_apply, integral_neg] at hu
    linarith
  simpa only [W, norm_smul, Real.norm_of_nonneg (radialKernel_pos a _ hε _).le] using hconcl

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
open scoped BoundedContinuousFunction
open scoped ENNReal Topology
namespace RPISingularHarnack

theorem radial_integral_lower_of_density {n : ℕ} (μ : Measure (Euc n)) [IsFiniteMeasure μ]
    (a : Euc n) {ε k c : ℝ} (hε : 0 < ε) (hk : 0 ≤ k) (hc : 0 ≤ c)
    (hdensity : c * ε ^ k ≤ μ.real (Metric.ball a ε))
    {f : Euc n → ℝ} (hf0 : ∀ x, 0 ≤ f x)
    (hflower : ∀ x ∈ Metric.ball a ε, f a / 2 ≤ f x)
    (hi : Integrable (fun x ↦ f x * k * (‖x - a‖ ^ 2 + ε ^ 2) ^ (-k / 2 - 1) * ε ^ 2) μ) :
    (c * k * (2 : ℝ) ^ (-k / 2 - 1) / 2) * f a ≤
      ∫ x, f x * k * (‖x - a‖ ^ 2 + ε ^ 2) ^ (-k / 2 - 1) * ε ^ 2 ∂μ := by
  let B : ℝ := f a / 2 * k * (2 * ε ^ 2) ^ (-k / 2 - 1) * ε ^ 2
  have hB : 0 ≤ B := by dsimp [B]; positivity [hf0 a]
  have hdist (x : Euc n) (hx : x ∈ Metric.ball a ε) : ‖x - a‖ ^ 2 + ε ^ 2 ≤ 2 * ε ^ 2 := by
    have hh : ‖x - a‖ < ε := by simpa only [Metric.mem_ball, dist_eq_norm] using hx
    nlinarith [norm_nonneg (x - a)]
  have hp (x : Euc n) (hx : x ∈ Metric.ball a ε) :
      (2 * ε ^ 2) ^ (-k / 2 - 1) ≤ (‖x - a‖ ^ 2 + ε ^ 2) ^ (-k / 2 - 1) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (hdist x hx) (by linarith)
  have hle (x : Euc n) : (Metric.ball a ε).indicator (fun _ ↦ B) x ≤
      f x * k * (‖x - a‖ ^ 2 + ε ^ 2) ^ (-k / 2 - 1) * ε ^ 2 := by
    by_cases hx : x ∈ Metric.ball a ε
    · rw [indicator_of_mem hx]
      dsimp [B]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul (mul_le_mul_of_nonneg_right (hflower x hx) hk) (hp x hx)
          (by positivity) (mul_nonneg (hf0 x) hk)) (sq_nonneg ε)
    · rw [indicator_of_notMem hx]
      positivity [hf0 x]
  have hileft : Integrable ((Metric.ball a ε).indicator (fun _ ↦ B)) μ :=
    (integrable_const B).indicator measurableSet_ball
  have hh := integral_mono hileft hi hle
  rw [integral_indicator measurableSet_ball, integral_const, smul_eq_mul,
    Measure.real, Measure.restrict_apply_univ] at hh
  have hlow := mul_le_mul hdensity (le_refl B) hB
    ((mul_nonneg hc (Real.rpow_nonneg hε.le k)).trans hdensity)
  have he : (c * ε ^ k) * B = (c * k * (2 : ℝ) ^ (-k / 2 - 1) / 2) * f a := by
    calc
      _ = (c * k * f a / 2) * (ε ^ k * ε ^ 2 * (2 * ε ^ 2) ^ (-k / 2 - 1)) := by dsimp [B]; ring
      _ = _ := by rw [radialKernel_mass_scaling hε]; ring
  exact he ▸ hlow.trans hh

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
open scoped BoundedContinuousFunction
open scoped ENNReal Topology
namespace RPISingularHarnack
open RPI.Boundary

theorem exists_minimizing_riesz_potential_constant (n : ℕ) (hn : 2 < n) :
    ∃ S : ℝ, 0 < S ∧ ∀ E : Set (Euc n), IsLocallyPerimeterMinimizing E →
      ∀ (c : Euc n) (R : ℝ), 0 < R → ∀ f : Euc n → ℝ,
        ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ Metric.ball c R →
        (∀ x, 0 ≤ f x) → ∀ a ∈ perimeterSupport E,
        S * f a ≤ ∫ x in Metric.ball c R,
          ‖tangentialGradient E f x‖ * ‖x - a‖ ^ (-(((n - 1 : ℕ) : ℝ) - 1)) ∂perimeterMeasure E := by
  have hn1 : 1 < n := by omega
  have hk : (1 : ℝ) < (n - 1 : ℕ) := by exact_mod_cast (show 1 < n - 1 by omega)
  obtain ⟨c₀, hc₀, hdensity⟩ := exists_minimizing_perimeter_lower_density n hn1
  obtain ⟨A, hA, hgrowth⟩ := exists_locallyMinimizing_perimeter_growth_constant n (by omega)
  let S : ℝ := c₀ * (n - 1 : ℕ) * (2 : ℝ) ^ (-((n - 1 : ℕ) : ℝ) / 2 - 1) / 2
  have hS : 0 < S := by dsimp [S]; positivity
  refine ⟨S, hS, ?_⟩
  intro E hmin c R hR f hf hcf hsf hf0 a ha
  let μ := (perimeterMeasure E).restrict (Metric.ball c R)
  have : IsFiniteMeasure μ := ⟨by
    rw [Measure.restrict_apply_univ, perimeterMeasure_open E Metric.isOpen_ball]
    exact hmin.2.1 c R hR⟩
  have hg (b : Euc n) (r : ℝ) (hr : 0 < r) : μ (Metric.ball b r) ≤
      ENNReal.ofReal (A * r ^ ((n - 1 : ℕ) : ℝ)) := by
    calc
      _ ≤ perimeterMeasure E (Metric.ball b r) := Measure.restrict_apply_le _ _
      _ = perimeter E (Metric.ball b r) := perimeterMeasure_open E Metric.isOpen_ball
      _ ≤ _ := by simpa only [Real.rpow_natCast] using hgrowth E hmin b r hr
  have hiK := RPIKernel.integrable_kernel_of_growth μ (by linarith : 0 < ((n - 1 : ℕ) : ℝ) - 1)
    (by linarith : ((n - 1 : ℕ) : ℝ) - 1 < ((n - 1 : ℕ) : ℝ)) hA.le hg a
  have hmG := (measurable_tangentialGradient hmin.1 (hf.of_le (by simp))).aestronglyMeasurable (μ := μ)
  obtain ⟨B, hB⟩ := exists_tangentialGradient_ball_bound E c R (hf.of_le (by simp))
  have hiGK : Integrable (fun x ↦ ‖tangentialGradient E f x‖ *
      ‖x - a‖ ^ (-(((n - 1 : ℕ) : ℝ) - 1))) μ := by
    simpa only [dist_eq_norm] using hiK.bdd_mul hmG.norm
      ((ae_restrict_mem measurableSet_ball).mono fun x hx ↦ by simpa only [norm_norm] using hB x hx)
  by_cases hfa : f a = 0
  · rw [hfa, mul_zero]
    exact integral_nonneg fun x ↦ by positivity
  have hfa0 : 0 < f a := lt_of_le_of_ne (hf0 a) (Ne.symm hfa)
  have haU : a ∈ Metric.ball c R := hsf (subset_tsupport f (by exact hfa))
  have hnhood : {x | f a / 2 < f x} ∈ 𝓝 a :=
    hf.continuous.continuousAt.preimage_mem_nhds (Ioi_mem_nhds (by linarith))
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp
    (inter_mem hnhood (Metric.isOpen_ball.mem_nhds haU))
  have hεU : Metric.ball a ε ⊆ Metric.ball c R := fun x hx ↦ (hεsub hx).2
  have hμball : μ (Metric.ball a ε) = perimeter E (Metric.ball a ε) := by
    rw [Measure.restrict_apply measurableSet_ball, inter_eq_left.mpr hεU,
      perimeterMeasure_open E Metric.isOpen_ball]
  have hdens : c₀ * ε ^ ((n - 1 : ℕ) : ℝ) ≤ μ.real (Metric.ball a ε) := by
    have ht := ENNReal.toReal_mono (hmin.2.1 a ε hε).ne (hdensity E hmin a ha ε hε)
    rw [ENNReal.toReal_ofReal (by positivity)] at ht
    simpa only [Measure.real, hμball, Real.rpow_natCast] using ht
  have hlci : Integrable (fun x ↦ f x * (n - 1 : ℕ) *
      (‖x - a‖ ^ 2 + ε ^ 2) ^ (-((n - 1 : ℕ) : ℝ) / 2 - 1) * ε ^ 2) μ := by
    apply ContinuousOn.integrableOn_of_subset_isCompact (s := Metric.ball c R)
      (K := Metric.closedBall c R) _ (isCompact_closedBall c R) measurableSet_ball Metric.ball_subset_closedBall
      (by rw [perimeterMeasure_open E Metric.isOpen_ball]; exact (hmin.2.1 c R hR).ne)
    apply Continuous.continuousOn
    apply Continuous.mul _ continuous_const
    apply Continuous.mul (hf.continuous.mul continuous_const)
    exact (((continuous_id.sub continuous_const).norm.pow 2).add continuous_const).rpow_const
      (fun x ↦ Or.inl (by change ‖x - a‖ ^ 2 + ε ^ 2 ≠ 0; positivity))
  have hlow := radial_integral_lower_of_density μ a hε (by linarith : 0 ≤ ((n - 1 : ℕ) : ℝ))
    hc₀.le hdens hf0 (fun x hx ↦ (hεsub hx).1.le) hlci
  have hmid := minimizing_radial_integral_bound hn1 hmin c a hR hε hf hcf hsf hf0
  have hmRG : AEStronglyMeasurable (fun x ↦ ‖tangentialGradient E f x‖ *
      (radialKernel a ε (n - 1 : ℕ) x * ‖x - a‖)) μ :=
    hmG.norm.mul (((radialKernel_contDiff a hε _).continuous.mul
      (continuous_id.sub continuous_const).norm).aestronglyMeasurable)
  have hpoint (x : Euc n) : ‖tangentialGradient E f x‖ *
      (radialKernel a ε (n - 1 : ℕ) x * ‖x - a‖) ≤
      ‖tangentialGradient E f x‖ * ‖x - a‖ ^ (-(((n - 1 : ℕ) : ℝ) - 1)) :=
    mul_le_mul_of_nonneg_left (radialKernel_mul_dist_le a x hε hk) (norm_nonneg _)
  have hiRG : Integrable (fun x ↦ ‖tangentialGradient E f x‖ *
      (radialKernel a ε (n - 1 : ℕ) x * ‖x - a‖)) μ :=
    hiGK.mono' hmRG (ae_of_all μ fun x ↦ by
      rw [Real.norm_of_nonneg (by positivity [(radialKernel_pos a x hε ((n - 1 : ℕ) : ℝ)).le])]
      exact hpoint x)
  exact hlow.trans (hmid.trans (integral_mono hiRG hiGK hpoint))

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
open scoped BoundedContinuousFunction
open scoped ENNReal Topology
namespace RPIKernel

theorem lp_average_bound {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {p : ℝ} (hp : 1 < p) {f : X → ℝ≥0∞} (hf : AEMeasurable f μ) :
    (∫⁻ x, f x ∂μ) ^ p ≤ (∫⁻ x, f x ^ p ∂μ) * (μ univ) ^ (p - 1) := by
  have hc := Real.HolderConjugate.conjExponent hp
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hc hf
    (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, one_mul] at hh
  have h := ENNReal.rpow_le_rpow hh (by linarith : 0 ≤ p)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by linarith : 0 ≤ p), ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul, div_mul_cancel₀ _ (ne_of_gt (lt_trans zero_lt_one hp)), ENNReal.rpow_one] at h
  have he : 1 / p.conjExponent * p = p - 1 := by
    calc
      _ = p / p.conjExponent := by ring
      _ = p - 1 := (div_eq_iff (ne_of_gt hc.symm.pos)).mpr hc.sub_one_mul_conj.symm
  rwa [he] at h

theorem kernel_lp_bound {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    {p : ℝ} (hp : 1 < p) (K : Y → X → ℝ≥0∞)
    (hK : Measurable (Function.uncurry K)) (g : X → ℝ≥0∞) (hg : Measurable g)
    {C : ℝ≥0∞} (hcol : ∀ x, ∫⁻ y, K y x ^ p ∂ν ≤ C) :
    ∫⁻ y, (∫⁻ x, K y x * g x ∂μ) ^ p ∂ν ≤
      C * (∫⁻ x, g x ∂μ) ^ p := by
  have hrow (y : Y) : Measurable (K y) := hK.comp ((measurable_const (a := y)).prodMk measurable_id)
  have hcolumn (x : X) : Measurable (fun y ↦ K y x) := hK.comp (measurable_id.prodMk (measurable_const (a := x)))
  have hm : Measurable (Function.uncurry (fun y x ↦ K y x ^ p * g x)) := (hK.pow_const p).mul (hg.comp measurable_snd)
  have hmain (y : Y) := lp_average_bound (μ.withDensity g) hp ((hrow y).aemeasurable)
  have hw : (μ.withDensity g) univ = ∫⁻ x, g x ∂μ := by simp
  have hpt (y : Y) : (∫⁻ x, K y x * g x ∂μ) ^ p ≤
      (∫⁻ x, K y x ^ p * g x ∂μ) * (∫⁻ x, g x ∂μ) ^ (p - 1) := by
    have ht := hmain y
    rw [hw, lintegral_withDensity_eq_lintegral_mul μ hg (hrow y),
      lintegral_withDensity_eq_lintegral_mul μ hg ((hrow y).pow_const p)] at ht
    simpa only [Pi.mul_apply, mul_comm (g _)] using ht
  calc
    _ ≤ ∫⁻ y, (∫⁻ x, K y x ^ p * g x ∂μ) * (∫⁻ x, g x ∂μ) ^ (p - 1) ∂ν :=
      lintegral_mono hpt
    _ = (∫⁻ x, (∫⁻ y, K y x ^ p ∂ν) * g x ∂μ) * (∫⁻ x, g x ∂μ) ^ (p - 1) := by
      rw [lintegral_mul_const _ hm.lintegral_prod_right]
      congr 1
      rw [lintegral_lintegral_swap hm.aemeasurable]
      apply lintegral_congr
      intro x
      rw [lintegral_mul_const _ ((hcolumn x).pow_const p)]
    _ ≤ (∫⁻ x, C * g x ∂μ) * (∫⁻ x, g x ∂μ) ^ (p - 1) := by
      gcongr with x
      exact hcol x
    _ = _ := by
      rw [lintegral_const_mul _ hg]
      rw [mul_assoc]
      congr 1
      calc
        _ = (∫⁻ x, g x ∂μ) ^ (1 : ℝ) * (∫⁻ x, g x ∂μ) ^ (p - 1) := by rw [ENNReal.rpow_one]
        _ = (∫⁻ x, g x ∂μ) ^ (1 + (p - 1)) := (ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by linarith)).symm
        _ = _ := by congr 1; ring

end RPIKernel

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
open scoped BoundedContinuousFunction
open scoped ENNReal Topology
namespace RPIKernel
open Set Filter MeasureTheory
open scoped ENNReal Topology
variable {X : Type*}

lemma ofReal_integral_le_lintegral [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {f : X → ℝ} {μ : Measure X}
    (hf : ∀ᵐ x ∂μ, 0 ≤ f x) :
    ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  by_cases hi : Integrable f μ
  · exact (ofReal_integral_eq_lintegral_ofReal hi hf).le
  · simp [integral_undef hi]

variable [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

theorem exists_potential_lp_bound [SecondCountableTopology X] (μ : Measure X) [IsFiniteMeasure μ]
    {d s p A S : ℝ} (hs : 0 < s) (hp : 1 < p) (hsp : s * p < d)
    (hA : 0 ≤ A) (hS : 0 < S)
    (hgrowth : ∀ a r, 0 < r → μ (Metric.ball a r) ≤ ENNReal.ofReal (A * r ^ d)) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ f g : X → ℝ,
      Measurable g → (∀ x, 0 ≤ g x) →
      (∀ᵐ a ∂μ, S * f a ≤ ∫ x, g x * dist x a ^ (-s) ∂μ) →
      (∫⁻ a, ENNReal.ofReal (f a) ^ p ∂μ) ≤ C * (∫⁻ x, ENNReal.ofReal (g x) ∂μ) ^ p := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  obtain ⟨B, hB, hcol⟩ := exists_kernel_integral_bound μ (mul_pos hs hp0) hsp hA hgrowth
  let K : X → X → ℝ≥0∞ := fun a x ↦ ENNReal.ofReal (dist x a ^ (-s))
  have hmK : Measurable (Function.uncurry K) :=
    ENNReal.measurable_ofReal.comp ((continuous_snd.dist continuous_fst).measurable.pow_const _)
  have hcol' (x : X) : ∫⁻ a, K a x ^ p ∂μ ≤ B := by
    calc
      _ = ∫⁻ a, ENNReal.ofReal (dist a x ^ (-(s * p))) ∂μ := by
        apply lintegral_congr
        intro a
        dsimp [K]
        rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg dist_nonneg _) hp0.le,
          ← Real.rpow_mul dist_nonneg, dist_comm]
        congr 2
        ring
      _ ≤ B := hcol x
  let T : ℝ≥0∞ := (ENNReal.ofReal S)⁻¹ ^ p
  refine ⟨T * B, ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg hp0.le (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr hS))) hB, ?_⟩
  intro f g hg hg0 hpot
  have hrow (a : X) : Measurable (K a) := hmK.comp (measurable_const.prodMk measurable_id)
  have hpot' : ∀ᵐ a ∂μ, ENNReal.ofReal (f a) ≤ (ENNReal.ofReal S)⁻¹ *
      ∫⁻ x, K a x * ENNReal.ofReal (g x) ∂μ := by
    filter_upwards [hpot] with a ha
    apply (ENNReal.mul_le_iff_le_inv (ENNReal.ofReal_ne_zero_iff.mpr hS) ENNReal.ofReal_ne_top).mp
    calc
      _ = ENNReal.ofReal (S * f a) := (ENNReal.ofReal_mul hS.le).symm
      _ ≤ ENNReal.ofReal (∫ x, g x * dist x a ^ (-s) ∂μ) := ENNReal.ofReal_le_ofReal ha
      _ ≤ ∫⁻ x, ENNReal.ofReal (g x * dist x a ^ (-s)) ∂μ :=
        ofReal_integral_le_lintegral (ae_of_all _ fun x ↦ mul_nonneg (hg0 x) (Real.rpow_nonneg dist_nonneg _))
      _ = _ := by
        apply lintegral_congr
        intro x
        rw [ENNReal.ofReal_mul (hg0 x), mul_comm]
  have hi := kernel_lp_bound μ μ hp K hmK (fun x ↦ ENNReal.ofReal (g x)) hg.ennreal_ofReal hcol'
  calc
    _ ≤ ∫⁻ a, T * (∫⁻ x, K a x * ENNReal.ofReal (g x) ∂μ) ^ p ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hpot'] with a ha
      exact (ENNReal.rpow_le_rpow ha hp0.le).trans_eq
        (ENNReal.mul_rpow_of_nonneg _ _ hp0.le)
    _ = T * ∫⁻ a, (∫⁻ x, K a x * ENNReal.ofReal (g x) ∂μ) ^ p ∂μ := by
      rw [lintegral_const_mul _ (((hmK.mul (hg.ennreal_ofReal.comp measurable_snd)).lintegral_prod_right).pow_const p)]
    _ ≤ T * (B * (∫⁻ x, ENNReal.ofReal (g x) ∂μ) ^ p) := by gcongr
    _ = _ := by rw [mul_assoc]

end RPIKernel

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
open scoped BoundedContinuousFunction
open scoped ENNReal Topology
namespace RPISingularHarnack

theorem minimizing_perimeter_sobolev {n : ℕ} (hn : 2 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    (c : Euc n) {R p : ℝ} (hR : 0 < R) (hp : 1 < p)
    (hpk : (((n - 1 : ℕ) : ℝ) - 1) * p < (n - 1 : ℕ)) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ f : Euc n → ℝ,
      ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ Metric.ball c R →
      (∀ x, 0 ≤ f x) →
      (∫⁻ x in Metric.ball c R, ENNReal.ofReal (f x) ^ p ∂perimeterMeasure E) ≤
        C * (∫⁻ x in Metric.ball c R, ENNReal.ofReal ‖tangentialGradient E f x‖ ∂perimeterMeasure E) ^ p := by
  obtain ⟨S, hS, hpot⟩ := exists_minimizing_riesz_potential_constant n hn
  obtain ⟨A, hA, hg⟩ := exists_locallyMinimizing_perimeter_growth_constant n (by omega)
  let μ := (perimeterMeasure E).restrict (Metric.ball c R)
  let : IsFiniteMeasure μ := ⟨by
    rw [Measure.restrict_apply_univ, perimeterMeasure_open E Metric.isOpen_ball]
    exact hmin.2.1 c R hR⟩
  have hgrowth (a : Euc n) (r : ℝ) (hr : 0 < r) : μ (Metric.ball a r) ≤
      ENNReal.ofReal (A * r ^ ((n - 1 : ℕ) : ℝ)) := by
    calc
      _ ≤ perimeterMeasure E (Metric.ball a r) := Measure.restrict_apply_le _ _
      _ = perimeter E (Metric.ball a r) := perimeterMeasure_open E Metric.isOpen_ball
      _ ≤ _ := by simpa only [Real.rpow_natCast] using hg E hmin a r hr
  have hk : (1 : ℝ) < (n - 1 : ℕ) := by exact_mod_cast (show 1 < n - 1 by omega)
  obtain ⟨C, hC, hbound⟩ := RPIKernel.exists_potential_lp_bound μ
    (by linarith : 0 < ((n - 1 : ℕ) : ℝ) - 1) hp hpk hA.le hS hgrowth
  refine ⟨C, hC, ?_⟩
  intro f hf hcf hsf hf0
  apply hbound f (fun x ↦ ‖tangentialGradient E f x‖)
    (measurable_tangentialGradient hmin.1 (hf.of_le (by simp))).norm (fun _ ↦ norm_nonneg _)
  have hs : ∀ᵐ x ∂perimeterMeasure E, x ∈ perimeterSupport E := by
    rw [← perimeterMeasure_support]; exact (perimeterMeasure E).support_mem_ae
  filter_upwards [ae_restrict_of_ae hs] with a ha
  simpa only [dist_eq_norm] using hpot E hmin c R hR f hf hcf hsf hf0 a ha

theorem minimizing_perimeter_boundaryArea_comparison {n : ℕ} (hn : 1 < n) :
    ∃ C D : ℝ≥0∞, C ≠ 0 ∧ C ≠ ⊤ ∧ D ≠ 0 ∧ D ≠ ⊤ ∧
      ∀ E : Set (Euc n), IsLocallyPerimeterMinimizing E →
        perimeterMeasure E ≤ C • boundaryArea E ∧ boundaryArea E ≤ D • perimeterMeasure E := by
  obtain ⟨C, D, hC0, hCt, hD0, hDt, hb⟩ := minimizing_perimeter_hausdorff_comparison hn
  let b : ℝ≥0∞ := volume (Metric.ball (0 : Euc (n - 1)) 1) / 2 ^ (n - 1)
  have hb0 : b ≠ 0 := ENNReal.div_ne_zero.mpr ⟨
    (Metric.measure_ball_pos volume 0 (by norm_num : (0 : ℝ) < 1)).ne', ENNReal.pow_ne_top (by norm_num)⟩
  have hbt : b ≠ ⊤ := ENNReal.div_ne_top measure_ball_ne_top (pow_ne_zero _ (by norm_num))
  refine ⟨C * b⁻¹, b * D, mul_ne_zero hC0 (ENNReal.inv_ne_zero.mpr hbt),
    ENNReal.mul_ne_top hCt (ENNReal.inv_ne_top.mpr hb0), mul_ne_zero hb0 hD0,
    ENNReal.mul_ne_top hbt hDt, ?_⟩
  intro E hmin
  have he : boundaryArea E = b • ((Measure.hausdorffMeasure (n - 1 : ℕ)).restrict (perimeterSupport E)) := by
    rw [boundaryArea, geometricHausdorff, Measure.restrict_smul]
  constructor
  · rw [he, smul_smul, mul_assoc, ENNReal.inv_mul_cancel hb0 hbt, mul_one]
    exact (hb E hmin).1
  · rw [he]
    apply Measure.le_iff.mpr
    intro s hs
    simp only [Measure.smul_apply, smul_eq_mul]
    calc
      _ ≤ b * (D * perimeterMeasure E s) := by
        gcongr
        exact Measure.le_iff.mp (hb E hmin).2 s hs
      _ = _ := by rw [mul_assoc]

theorem minimizing_boundaryArea_sobolev {n : ℕ} (hn : 2 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    (c : Euc n) {R p : ℝ} (hR : 0 < R) (hp : 1 < p)
    (hpk : (((n - 1 : ℕ) : ℝ) - 1) * p < (n - 1 : ℕ)) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ f : Euc n → ℝ,
      ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ Metric.ball c R →
      (∀ x, 0 ≤ f x) →
      (∫⁻ x in Metric.ball c R, ENNReal.ofReal (f x) ^ p ∂boundaryArea E) ≤
        C * (∫⁻ x in Metric.ball c R, ENNReal.ofReal ‖tangentialGradient E f x‖ ∂boundaryArea E) ^ p := by
  obtain ⟨B, hB, hb⟩ := minimizing_perimeter_sobolev hn hmin c hR hp hpk
  obtain ⟨D₁, D₂, _, hD₁, _, hD₂, hd⟩ := minimizing_perimeter_boundaryArea_comparison (by omega : 1 < n)
  have hμ₁ := Measure.restrict_mono_measure (hd E hmin).1 (Metric.ball c R)
  have hμ₂ := Measure.restrict_mono_measure (hd E hmin).2 (Metric.ball c R)
  rw [Measure.restrict_smul] at hμ₁ hμ₂
  have hp0 : 0 ≤ p := (lt_trans zero_lt_one hp).le
  refine ⟨D₂ * B * D₁ ^ p,
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hD₂ hB) (ENNReal.rpow_ne_top_of_nonneg hp0 hD₁), ?_⟩
  intro f hf hcf hsf hf0
  have hgrad : (∫⁻ x in Metric.ball c R, ENNReal.ofReal ‖tangentialGradient E f x‖ ∂perimeterMeasure E) ≤
      D₁ * (∫⁻ x in Metric.ball c R, ENNReal.ofReal ‖tangentialGradient E f x‖ ∂boundaryArea E) := by
    simpa only [lintegral_smul_measure, smul_eq_mul] using lintegral_mono' hμ₁ (le_refl (fun x ↦ ENNReal.ofReal ‖tangentialGradient E f x‖))
  calc
    _ ≤ D₂ * (∫⁻ x in Metric.ball c R, ENNReal.ofReal (f x) ^ p ∂perimeterMeasure E) := by
      simpa only [lintegral_smul_measure, smul_eq_mul] using lintegral_mono' hμ₂ (le_refl (fun x ↦ ENNReal.ofReal (f x) ^ p))
    _ ≤ D₂ * (B * (∫⁻ x in Metric.ball c R, ENNReal.ofReal ‖tangentialGradient E f x‖ ∂perimeterMeasure E) ^ p) := by
      gcongr
      exact hb f hf hcf hsf hf0
    _ ≤ D₂ * (B * (D₁ * (∫⁻ x in Metric.ball c R, ENNReal.ofReal ‖tangentialGradient E f x‖ ∂boundaryArea E)) ^ p) := by
      gcongr
    _ = _ := by rw [ENNReal.mul_rpow_of_nonneg _ _ hp0]; ac_rfl

end RPISingularHarnack

end

end OAI

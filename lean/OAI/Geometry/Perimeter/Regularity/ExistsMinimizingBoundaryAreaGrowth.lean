import OAI.Geometry.Perimeter.Regularity.IndicatorConvolutionVariationLocalLe

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack
open RPI

theorem exists_minimizing_boundaryArea_growth {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E) :
    ∃ A : ℝ, 0 < A ∧ ∀ (c : Euc n) (r : ℝ), 0 < r →
      boundaryArea E (Metric.ball c r) ≤ ENNReal.ofReal (A * r ^ (n - 1)) := by
  obtain ⟨A, hA, harea⟩ := exists_minimizing_surfaceMeasure_growth hn hmin
  let b := hausdorffNormalizationRatio (n - 1)
  let D := (b * ENNReal.ofReal A).toReal + 1
  have hD : 0 < D := by dsimp [D]; positivity
  have hb : b ≠ ⊤ := hausdorffNormalizationRatio_ne_top _
  have hbA : b * ENNReal.ofReal A ≤ ENNReal.ofReal D := by
    rw [← ENNReal.ofReal_toReal (ENNReal.mul_ne_top hb ENNReal.ofReal_ne_top)]
    apply ENNReal.ofReal_le_ofReal
    dsimp [D]
    linarith
  refine ⟨D, hD, ?_⟩
  intro c r hr
  rw [boundaryArea_eq_smul_surfaceMeasure]
  change b * _ ≤ _
  calc
    _ ≤ b * ENNReal.ofReal (A * r ^ (n - 1)) := mul_le_mul le_rfl (harea c r hr) (by positivity) (by positivity)
    _ = (b * ENNReal.ofReal A) * ENNReal.ofReal r ^ (n - 1) := by
      rw [ENNReal.ofReal_mul hA.le, ENNReal.ofReal_pow hr.le, mul_assoc]
    _ ≤ ENNReal.ofReal D * ENNReal.ofReal r ^ (n - 1) := mul_le_mul hbA le_rfl (by positivity) (by positivity)
    _ = _ := by rw [ENNReal.ofReal_mul hD.le, ENNReal.ofReal_pow hr.le]

theorem approximateNormal_norm_le_one {n : ℕ} (E : Set (Euc n)) (x : Euc n) :
    ‖approximateNormal E x‖ ≤ 1 := by
  classical
  unfold approximateNormal
  split_ifs with h
  · exact (Classical.choose_spec h).1.le
  · simp

theorem tangentialGradient_norm_le_twice {n : ℕ} (E : Set (Euc n))
    (φ : Euc n → ℝ) (x : Euc n) :
    ‖tangentialGradient E φ x‖ ≤ 2 * ‖gradient φ x‖ := by
  have hv := approximateNormal_norm_le_one E x
  have hinner : |inner ℝ (gradient φ x) (approximateNormal E x)| ≤ ‖gradient φ x‖ := by
    exact (abs_real_inner_le_norm _ _).trans (by nlinarith [norm_nonneg (gradient φ x)])
  calc
    _ ≤ ‖gradient φ x‖ + ‖(inner ℝ (gradient φ x) (approximateNormal E x)) •
        approximateNormal E x‖ := norm_sub_le _ _
    _ ≤ ‖gradient φ x‖ + ‖gradient φ x‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      gcongr
      exact le_trans (mul_le_mul_of_nonneg_left hv (abs_nonneg _)) (by simpa using hinner)
    _ = _ := by ring

theorem exists_raw_minimizing_frontier_capacity_sequence {n : ℕ} (hn : 8 ≤ n)
    {E Z : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    (hZc : IsCompact Z) (hZd : dimH Z ≤ (n - 8 : ℕ)) :
    ∃ χ : ℕ → Euc n → ℝ,
      (∀ i, ContDiff ℝ ∞ (χ i) ∧ (∀ x, χ i x ∈ Icc (0 : ℝ) 1) ∧
        ∃ U : Set (Euc n), IsOpen U ∧ Z ⊆ U ∧ ∀ x ∈ U, χ i x = 0) ∧
      (∀ x ∉ Z, ∀ᶠ i in atTop, χ i x = 1) ∧
      Tendsto (fun i ↦ smoothDirichletEnergy (boundaryArea E) (χ i)) atTop (𝓝 0) ∧
      Tendsto (fun i ↦ vectorEnergy (boundaryArea E) (tangentialGradient E (χ i)))
        atTop (𝓝 0) := by
  obtain ⟨A, hA, harea⟩ := exists_minimizing_boundaryArea_growth (by omega : 1 < n) hmin
  obtain ⟨hm, hnull⟩ := hausdorff_capacity_dimension hn Z hZd
  have heq : n - 3 + 2 = n - 1 := by omega
  obtain ⟨χ, hχ, hχone, hχenergy⟩ := exists_smooth_capacity_sequence (boundaryArea E)
    Z hZc (n - 3) hm hnull hA (by norm_num : (0 : ℝ) < 1)
    (fun c _ r hr _ ↦ by simpa only [heq] using harea c r hr)
  refine ⟨χ, hχ, hχone, hχenergy, ?_⟩
  have hb : ∀ i, vectorEnergy (boundaryArea E) (tangentialGradient E (χ i)) ≤
      (4 : ℝ≥0∞) * smoothDirichletEnergy (boundaryArea E) (χ i) := by
    intro i
    rw [vectorEnergy, smoothDirichletEnergy, ← lintegral_const_mul' _ _ ENNReal.ofNat_ne_top]
    apply lintegral_mono
    intro x
    have hnorm := tangentialGradient_norm_le_twice E (χ i) x
    calc
      _ ≤ ENNReal.ofReal (4 * ‖gradient (χ i) x‖ ^ 2) := by
        apply ENNReal.ofReal_le_ofReal
        nlinarith [norm_nonneg (tangentialGradient E (χ i) x), norm_nonneg (gradient (χ i) x)]
      _ = _ := by rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]; norm_num
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [mul_zero] using ENNReal.Tendsto.const_mul hχenergy (Or.inr (by norm_num : (4 : ℝ≥0∞) ≠ ⊤)))
    (fun _ ↦ zero_le) hb

end RPISingularHarnack

end

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
open scoped Topology ENNReal NNReal
open scoped ENNReal Topology ContDiff Pointwise
open scoped Topology ENNReal ContDiff
namespace RPISingularHarnack

theorem tendsto_normalized_monotone_of_dyadic {a : ℝ → ℝ} (n : ℕ)
    (ha : ∀ r, 0 < r → 0 ≤ a r)
    (ham : ∀ r s, 0 < r → r ≤ s → a r ≤ a s)
    (ht : Tendsto (fun j : ℕ ↦ a ((1 / 2 : ℝ) ^ j) / ((1 / 2 : ℝ) ^ j) ^ n)
      atTop (𝓝 0)) :
    Tendsto (fun r : ℝ ↦ a r / r ^ n) (𝓝[>] 0) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have htwo : (0 : ℝ) < 2 ^ n := by positivity
  have hev := (Metric.tendsto_nhds.mp ht) (ε / (2 : ℝ) ^ n) (div_pos hε htwo)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ N := by positivity
  have hsmall : ∀ᶠ r : ℝ in 𝓝[>] 0, r < (1 / 2 : ℝ) ^ N :=
    (gt_mem_nhds hpos).filter_mono nhdsWithin_le_nhds
  filter_upwards [hsmall, self_mem_nhdsWithin] with r hr hrp
  have hunit : r ≤ 1 := hr.le.trans (pow_le_one₀ (by norm_num) (by norm_num))
  obtain ⟨j, hjlo, hjhi⟩ := exists_nat_pow_near_of_lt_one hrp hunit
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  have hjN : N ≤ j := by
    by_contra h
    have hNj : j + 1 ≤ N := by omega
    have hpow : (1 / 2 : ℝ) ^ N ≤ (1 / 2 : ℝ) ^ (j + 1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hNj
    linarith
  have hspos : (0 : ℝ) < (1 / 2 : ℝ) ^ j := by positivity
  have hscale : (1 / 2 : ℝ) ^ j ≤ 2 * r := by
    rw [pow_succ] at hjlo
    linarith
  have hpower : ((1 / 2 : ℝ) ^ j) ^ n ≤ (2 : ℝ) ^ n * r ^ n := by
    simpa only [mul_pow] using pow_le_pow_left₀ hspos.le hscale n
  have hab := ham r ((1 / 2 : ℝ) ^ j) hrp hjhi
  have hbound : a r / r ^ n ≤ (2 : ℝ) ^ n *
      (a ((1 / 2 : ℝ) ^ j) / ((1 / 2 : ℝ) ^ j) ^ n) := by
    apply le_trans (div_le_div_of_nonneg_right hab (pow_nonneg hrp.le _))
    rw [← mul_div_assoc, div_le_div_iff₀ (pow_pos hrp _) (pow_pos hspos _)]
    nlinarith [mul_le_mul_of_nonneg_left hpower (ha _ hspos)]
  have hj := hN j hjN
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (ha _ hspos)
    (pow_nonneg hspos.le _))] at hj
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (ha _ hrp)
    (pow_nonneg hrp.le _))]
  exact hbound.trans_lt ((mul_lt_mul_of_pos_left hj htwo).trans_eq (by field_simp))

def rescaledHalfspaceError {n : ℕ} (E : Set (Euc n)) (r : ℝ)
    (p : Euc n × Euc n) : ℝ :=
  ∫ z in Metric.ball (0 : Euc n) 1,
    |E.indicator (fun _ ↦ (1 : ℝ)) (p.1 + r • z) -
      {y | inner ℝ y p.2 < 0}.indicator (fun _ ↦ (1 : ℝ)) z|

theorem rescaledHalfspaceError_eq {n : ℕ} (E : Set (Euc n))
    (x v : Euc n) {r : ℝ} (hr : 0 < r) :
    rescaledHalfspaceError E r (x, v) =
      (r ^ n)⁻¹ * ∫ y in Metric.ball x r,
        |E.indicator (fun _ ↦ (1 : ℝ)) y -
          {z | inner ℝ (z - x) v < 0}.indicator (fun _ ↦ (1 : ℝ)) y| := by
  rw [normalized_ball_integral _ x hr]
  unfold rescaledHalfspaceError
  apply integral_congr_ae
  exact ae_of_all _ (fun z ↦ by dsimp only; rw [halfspace_indicator_rescale x v z hr])

theorem hasHalfspaceBlowup_iff_dyadic {n : ℕ} {E : Set (Euc n)}
    (hE : MeasurableSet E) (x v : Euc n) :
    HasHalfspaceBlowup E x v ↔ ‖v‖ = 1 ∧
      Tendsto (fun j : ℕ ↦ rescaledHalfspaceError E ((1 / 2 : ℝ) ^ j) (x, v))
        atTop (𝓝 0) := by
  have hpow := tendsto_pow_atTop_nhdsWithin_zero_of_lt_one
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  constructor
  · rintro ⟨hv, ht⟩
    refine ⟨hv, ?_⟩
    convert ht.comp hpow using 1
    ext j
    exact rescaledHalfspaceError_eq E x v (by positivity)
  · rintro ⟨hv, ht⟩
    refine ⟨hv, ?_⟩
    let f : Euc n → ℝ := fun y ↦ |E.indicator (fun _ ↦ (1 : ℝ)) y -
      {z | inner ℝ (z - x) v < 0}.indicator (fun _ ↦ (1 : ℝ)) y|
    have hf : Measurable f := by
      apply Measurable.abs
      exact (measurable_const.indicator hE).sub
        (measurable_const.indicator (isOpen_lt
          ((continuous_id.sub continuous_const).inner continuous_const) continuous_const).measurableSet)
    have hfi : ∀ s : ℝ, IntegrableOn f (Metric.ball x s) volume := by
      intro s
      apply (integrableOn_const measure_ball_lt_top.ne (C := (1 : ℝ))).mono' hf.aestronglyMeasurable
      apply ae_of_all
      intro y
      dsimp [f]
      by_cases he : y ∈ E <;> by_cases hh : inner ℝ (y - x) v < 0 <;> simp [he, hh]
    have hnon : ∀ s, 0 < s → 0 ≤ ∫ y in Metric.ball x s, f y :=
      fun s _ ↦ integral_nonneg (fun y ↦ abs_nonneg _)
    have hmono : ∀ r s, 0 < r → r ≤ s →
        (∫ y in Metric.ball x r, f y) ≤ ∫ y in Metric.ball x s, f y := by
      intro r s _ hrs
      exact setIntegral_mono_set (hfi s) (ae_of_all _ (fun y ↦ abs_nonneg _))
        (Eventually.of_forall (Metric.ball_subset_ball hrs))
    have hdy : Tendsto (fun j : ℕ ↦
        (∫ y in Metric.ball x ((1 / 2 : ℝ) ^ j), f y) / ((1 / 2 : ℝ) ^ j) ^ n)
        atTop (𝓝 0) := by
      convert ht using 1
      ext j
      rw [rescaledHalfspaceError_eq E x v (by positivity)]
      simp only [div_eq_mul_inv, mul_comm, f]
    simpa only [div_eq_mul_inv, mul_comm, f] using
      tendsto_normalized_monotone_of_dyadic n hnon hmono hdy

theorem measurable_rescaledHalfspaceError {n : ℕ} {E : Set (Euc n)}
    (hE : MeasurableSet E) (r : ℝ) : Measurable (rescaledHalfspaceError E r) := by
  have hχ : Measurable (E.indicator (fun _ ↦ (1 : ℝ))) := measurable_const.indicator hE
  have hH : MeasurableSet {p : (Euc n × Euc n) × Euc n | inner ℝ p.2 p.1.2 < 0} :=
    (isOpen_lt (continuous_snd.inner (continuous_snd.comp continuous_fst)) continuous_const).measurableSet
  have hf : Measurable (fun p : (Euc n × Euc n) × Euc n ↦
      |E.indicator (fun _ ↦ (1 : ℝ)) (p.1.1 + r • p.2) -
        {y | inner ℝ y p.1.2 < 0}.indicator (fun _ ↦ (1 : ℝ)) p.2|) := by
    have he : Measurable (fun p : (Euc n × Euc n) × Euc n ↦
        E.indicator (fun _ ↦ (1 : ℝ)) (p.1.1 + r • p.2)) :=
      hχ.comp ((measurable_fst.comp measurable_fst).add (measurable_snd.const_smul r))
    have hh : Measurable (fun p : (Euc n × Euc n) × Euc n ↦
        {y | inner ℝ y p.1.2 < 0}.indicator (fun _ ↦ (1 : ℝ)) p.2) := by
      have heq : (fun p : (Euc n × Euc n) × Euc n ↦
          {y | inner ℝ y p.1.2 < 0}.indicator (fun _ ↦ (1 : ℝ)) p.2) =
          {p : (Euc n × Euc n) × Euc n | inner ℝ p.2 p.1.2 < 0}.indicator
            (fun _ ↦ (1 : ℝ)) := by funext p; rfl
      rw [heq]
      exact measurable_const.indicator hH
    exact (he.sub hh).abs
  exact (hf.stronglyMeasurable.integral_prod_right').measurable

theorem measurableSet_halfspaceBlowup {n : ℕ} {E : Set (Euc n)}
    (hE : MeasurableSet E) :
    MeasurableSet {p : Euc n × Euc n | HasHalfspaceBlowup E p.1 p.2} := by
  have hnorm : MeasurableSet {p : Euc n × Euc n | ‖p.2‖ = 1} :=
    measurableSet_eq_fun measurable_snd.norm measurable_const
  have ht := measurableSet_tendsto (l := (atTop : Filter ℕ)) (𝓝 (0 : ℝ))
    (fun j : ℕ ↦ measurable_rescaledHalfspaceError hE ((1 / 2 : ℝ) ^ j))
  simpa only [hasHalfspaceBlowup_iff_dyadic hE, Set.ofPred_and] using hnorm.inter ht

theorem measurable_approximateNormal {n : ℕ} {E : Set (Euc n)}
    (hE : MeasurableSet E) : Measurable (approximateNormal E) := by
  classical
  let Γ : Set (Euc n × Euc n) := {p | HasHalfspaceBlowup E p.1 p.2}
  have hΓ : MeasurableSet Γ := measurableSet_halfspaceBlowup hE
  have hinj : Set.InjOn Prod.fst Γ := by
    intro p hp q hq heq
    apply Prod.ext heq
    exact (show HasHalfspaceBlowup E p.1 p.2 from hp).unique hE
      (by simpa only [Γ, Set.mem_ofPred_eq, heq] using hq)
  let D : Set (Euc n) := Prod.fst '' Γ
  have hD : MeasurableSet D := hΓ.image_of_measurable_injOn measurable_fst hinj
  have hDm : ∀ x, x ∈ D ↔ ∃ v, HasHalfspaceBlowup E x v := by
    intro x
    constructor
    · rintro ⟨⟨y, v⟩, hv, hxy⟩
      change y = x at hxy
      subst y
      exact ⟨v, hv⟩
    · rintro ⟨v, hv⟩
      exact ⟨(x, v), hv, rfl⟩
  intro s hs
  let B : Set (Euc n) := Prod.fst '' (Γ ∩ Prod.snd ⁻¹' s)
  have hB : MeasurableSet B := (hΓ.inter (hs.preimage measurable_snd)).image_of_measurable_injOn
    measurable_fst (hinj.mono Set.inter_subset_left)
  have hBm : ∀ x, x ∈ B ↔ ∃ v, HasHalfspaceBlowup E x v ∧ v ∈ s := by
    intro x
    constructor
    · rintro ⟨⟨y, v⟩, ⟨hv, hvs⟩, hxy⟩
      change y = x at hxy
      subst y
      exact ⟨v, hv, hvs⟩
    · rintro ⟨v, hv, hvs⟩
      exact ⟨(x, v), ⟨hv, hvs⟩, rfl⟩
  have hm : ∀ x, x ∈ D → (approximateNormal E x ∈ s ↔ x ∈ B) := by
    intro x hx
    obtain ⟨v, hv⟩ := (hDm x).mp hx
    rw [approximateNormal_eq_of_blowup hE hv, hBm]
    constructor
    · exact fun hvs ↦ ⟨v, hv, hvs⟩
    · rintro ⟨w, hw, hws⟩
      rwa [hv.unique hE hw]
  have hz : ∀ x, x ∉ D → approximateNormal E x = 0 := by
    intro x hx
    have hno : ¬ ∃ v, HasHalfspaceBlowup E x v := by simpa only [hDm] using hx
    simp only [approximateNormal, dite_eq_right hno]
  have hBD : B ⊆ D := by
    intro x hx
    obtain ⟨v, hv, _⟩ := (hBm x).mp hx
    exact (hDm x).mpr ⟨v, hv⟩
  by_cases hzero : (0 : Euc n) ∈ s
  · have heq : approximateNormal E ⁻¹' s = B ∪ Dᶜ := by
      ext x
      by_cases hx : x ∈ D
      · simp only [Set.mem_preimage, Set.mem_union, Set.mem_compl_iff, hx, not_true_eq_false,
          or_false, hm x hx]
      · simp only [Set.mem_preimage, Set.mem_union, Set.mem_compl_iff, hx, not_false_eq_true,
          or_true, hz x hx, hzero]
    rw [heq]
    exact hB.union hD.compl
  · have heq : approximateNormal E ⁻¹' s = B := by
      ext x
      by_cases hx : x ∈ D
      · exact hm x hx
      · have hb : x ∉ B := fun hb ↦ hx (hBD hb)
        simp only [Set.mem_preimage, hz x hx, hzero, hb]
    rw [heq]
    exact hB

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

theorem measurable_tangentialGradient {n : ℕ} {E : Set (Euc n)}
    (hE : MeasurableSet E) {φ : Euc n → ℝ} (hφ : ContDiff ℝ 1 φ) :
    Measurable (tangentialGradient E φ) := by
  have hg : Continuous (gradient φ) := continuous_iff_continuousAt.mpr (fun x ↦
    continuousAt_gradient_of_contDiffAt hφ.contDiffAt)
  have hv := measurable_approximateNormal hE
  exact hg.measurable.sub ((hg.measurable.inner (𝕜 := ℝ) hv).smul hv)

theorem minimizing_boundaryArea_ball_lt_top {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    (c : Euc n) {R : ℝ} (hR : 0 < R) : boundaryArea E (Metric.ball c R) < ⊤ := by
  obtain ⟨A, _, hA⟩ := exists_minimizing_boundaryArea_growth hn hmin
  exact (hA c R hR).trans_lt ENNReal.ofReal_lt_top

theorem tangentialGradient_memLp_on_ball {n : ℕ} (hn : 1 < n)
    {E : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    {R : ℝ} (hR : 0 < R) {φ : Euc n → ℝ} (hφ : ContDiff ℝ 1 φ) :
    MemLp (tangentialGradient E φ) 2 ((boundaryArea E).restrict (Metric.ball 0 R)) := by
  let μ := (boundaryArea E).restrict (Metric.ball 0 R)
  have : IsFiniteMeasure μ := ⟨by
    simpa only [μ, Measure.restrict_apply_univ] using minimizing_boundaryArea_ball_lt_top hn hmin 0 hR⟩
  have hg : Continuous (gradient φ) := continuous_iff_continuousAt.mpr (fun x ↦
    continuousAt_gradient_of_contDiffAt hφ.contDiffAt)
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : Euc n) R).exists_bound_of_continuousOn hg.continuousOn
  apply MemLp.of_bound (measurable_tangentialGradient hmin.1 hφ).aestronglyMeasurable (2 * M)
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  exact (tangentialGradient_norm_le_twice E φ x).trans (by
    nlinarith [hM x (Metric.ball_subset_closedBall hx)])

theorem tangentialGradient_mul {n : ℕ} (E : Set (Euc n))
    {f g : Euc n → ℝ} {x : Euc n}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    tangentialGradient E (fun y ↦ f y * g y) x =
      f x • tangentialGradient E g x + g x • tangentialGradient E f x := by
  have hgrad : gradient (fun y ↦ f y * g y) x = f x • gradient g x + g x • gradient f x := by
    apply (InnerProductSpace.toDual ℝ (Euc n)).injective
    simp only [map_add, map_smul, toDual_gradient]
    exact fderiv_mul hf hg
  simp only [tangentialGradient, hgrad, inner_add_left, real_inner_smul_left]
  module

theorem tangentialGradient_eq_zero_of_notMem_tsupport {n : ℕ} (E : Set (Euc n))
    {φ : Euc n → ℝ} {x : Euc n} (hx : x ∉ tsupport φ) : tangentialGradient E φ x = 0 := by
  simp only [tangentialGradient, gradient, fderiv_of_notMem_tsupport ℝ hx, map_zero,
    inner_zero_left, zero_smul, sub_self]

theorem boundaryArea_zero_of_singular_dim {n : ℕ} (hn : 8 ≤ n)
    (E Z : Set (Euc n)) (hZd : dimH Z ≤ (n - 8 : ℕ)) : boundaryArea E Z = 0 := by
  rw [boundaryArea_eq_smul_surfaceMeasure, Measure.smul_apply,
    surfaceMeasure_zero_of_singular_dim hn _ _ hZd]
  exact mul_zero _

theorem wholeBoundarySupersolution_of_regular_tests {n : ℕ} (hn : 8 ≤ n)
    {E Z : Set (Euc n)} (hmin : IsLocallyPerimeterMinimizing E)
    (hZ : IsClosed Z) (hZd : dimH Z ≤ (n - 8 : ℕ)) {G : Euc n → Euc n}
    (hloc : ∀ R : ℝ, 0 < R → MemLp G 2 ((boundaryArea E).restrict (Metric.ball 0 R)))
    (hreg : ∀ ψ : Euc n → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      Disjoint (tsupport ψ) Z → (∀ x, 0 ≤ ψ x) →
      0 ≤ ∫ x, inner ℝ (G x) (tangentialGradient E ψ x) ∂boundaryArea E) :
    WholeBoundarySupersolution E G := by
  intro φ hφ hcφ hpφ
  obtain ⟨r, hr⟩ := Metric.isBounded_iff_subset_ball (0 : Euc n) |>.mp hcφ.isBounded
  let R := max r 1
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hsupp : tsupport φ ⊆ Metric.ball (0 : Euc n) R :=
    hr.trans (Metric.ball_subset_ball (le_max_left _ _))
  let μ := (boundaryArea E).restrict (Metric.ball 0 R)
  have hn1 : 1 < n := by omega
  have : IsFiniteMeasure μ := ⟨by
    simpa only [μ, Measure.restrict_apply_univ] using minimizing_boundaryArea_ball_lt_top hn1 hmin 0 hR⟩
  let K := Z ∩ tsupport φ
  have hKc : IsCompact K := hcφ.of_isClosed_subset
    (hZ.inter (isClosed_tsupport φ)) inter_subset_right
  have hKd : dimH K ≤ (n - 8 : ℕ) := (dimH_mono inter_subset_left).trans hZd
  obtain ⟨χ, hχ, hχlim, _, hχE⟩ := exists_raw_minimizing_frontier_capacity_sequence hn hmin hKc hKd
  have hzero : ∀ᵐ x ∂μ, x ∉ K := by
    have hKzero : μ K = 0 := le_antisymm
      (Measure.restrict_apply_le _ _ |>.trans_eq (boundaryArea_zero_of_singular_dim hn E K hKd)) zero_le
    simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hKzero
  have hχlim' : ∀ᵐ x ∂μ, Tendsto (fun i ↦ χ i x) atTop (𝓝 1) := by
    filter_upwards [hzero] with x hx
    apply tendsto_const_nhds.congr'
    filter_upwards [hχlim x hx] with i hi
    exact hi.symm
  have hχE' : Tendsto (fun i ↦ vectorEnergy μ (tangentialGradient E (χ i))) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hχE (fun _ ↦ zero_le)
    intro i
    exact lintegral_mono' Measure.restrict_le_self le_rfl
  have hB : MemLp (tangentialGradient E φ) 2 μ :=
    tangentialGradient_memLp_on_ball hn1 hmin hR (hφ.of_le (by simp))
  have hC : ∀ i, MemLp (tangentialGradient E (χ i)) 2 μ := fun i ↦
    tangentialGradient_memLp_on_ball hn1 hmin hR ((hχ i).1.of_le (by simp))
  have hC0 : Tendsto (fun i ↦ (eLpNorm (tangentialGradient E (χ i)) 2 μ).toReal)
      atTop (𝓝 0) := tendsto_eLpNorm_two_toReal_of_vectorEnergy_zero_of_aestronglyMeasurable
        (fun i ↦ (hC i).aestronglyMeasurable) hχE'
  have hχnorm : ∀ i, ∀ᵐ x ∂μ, ‖χ i x‖ ≤ 1 := fun i ↦ ae_of_all _ (fun x ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg ((hχ i).2.1 x).1]
    exact ((hχ i).2.1 x).2)
  obtain ⟨M, hM⟩ := hcφ.exists_bound_of_continuous hφ.continuous
  have hpair : 0 ≤ ∫ x, inner ℝ (G x) (tangentialGradient E φ x) ∂μ := by
    apply energy_inequality_of_capacity_cutoffs (hloc R hR) hB χ
      (fun i ↦ (hχ i).1.continuous.aestronglyMeasurable) hχnorm hχlim'
      (fun i ↦ tangentialGradient E (χ i)) hC hC0 φ hφ.continuous.aestronglyMeasurable
      (M := M) (ae_of_all _ hM)
    intro i
    have heq : (fun x ↦ χ i x • tangentialGradient E φ x + φ x • tangentialGradient E (χ i) x) =
        tangentialGradient E (fun x ↦ φ x * χ i x) := by
      funext x
      rw [tangentialGradient_mul E (hφ.differentiable (by simp)).differentiableAt
        ((hχ i).1.differentiable (by simp)).differentiableAt, add_comm]
    simp_rw [congrFun heq]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    · apply hreg _ (hφ.mul (hχ i).1) hcφ.mul_right
      · exact tsupport_mul_disjoint_Singular (hχ i).2.2
      · exact fun x ↦ mul_nonneg (hpφ x) ((hχ i).2.1 x).1
    · intro x hx
      rw [tangentialGradient_eq_zero_of_notMem_tsupport E
        (fun hx' ↦ hx (hsupp (tsupport_mul_subset_left hx'))), inner_zero_right]
  dsimp only [μ] at hpair
  rwa [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx ↦ by
    rw [tangentialGradient_eq_zero_of_notMem_tsupport E (fun hx' ↦ hx (hsupp hx')),
      inner_zero_right])] at hpair

end RPISingularHarnack

end

end OAI

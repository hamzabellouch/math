import OAI.Probability.SLE.Multipoint.MultipointPhysicalBudget

namespace OAI

/-! Deterministic transport of the two-ended regulator to physical time.
The single-point cost follows by change of variables along the actual
radius clock, and the pair cost follows from geometric interaction decay. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal

namespace SLEExactGauge.Multipoint

/-- Change of variables for a regulator on any subinterval of its clock.
Only ordinary calculus is used here; no stochastic estimate is assumed. -/
theorem regulator_clock_integral_le
    {β U s T : ℝ} (hβ : 0 < β) (hU : 0 ≤ U) (hsT : s ≤ T)
    (u speed : ℝ → ℝ) (hu : ContinuousOn u (Icc s T))
    (hspeed : ContinuousOn speed (Icc s T))
    (hdu : ∀ t ∈ Ioo s T, HasDerivWithinAt u (speed t) (Ioi t) t)
    (hu0 : 0 ≤ u s) (huT : u T ≤ U) (hmono : u s ≤ u T) :
    (∫ t in s..T, regulator β U (u t) * speed t) ≤ 2 / β := by
  have he : (∫ t in s..T, regulator β U (u t) * speed t) =
      ∫ v in u s..u T, regulator β U v := by
    simpa only [Function.comp_apply] using
      intervalIntegral.integral_comp_mul_deriv''
        (by simpa only [uIcc_of_le hsT] using hu)
        (by simpa only [min_eq_left hsT, max_eq_right hsT] using hdu)
        (by simpa only [uIcc_of_le hsT] using hspeed)
        (regulator_continuous β U).continuousOn
  rw [he]
  apply le_trans _ (integral_regulator_le hβ hU)
  exact intervalIntegral.integral_mono_interval hu0 hmono huT
    (ae_of_all _ fun v => (regulator_pos β U v).le)
    ((regulator_continuous β U).intervalIntegrable 0 U)

/-- The radius clock measured from activation, in capacity-two time.
The clock derivative is the square of the Poisson rate. -/
def activeRadiusClock (G : ℝ≥0 → ℂ → ℂ) (z : ℂ) (σ : ℝ≥0) (t : ℝ) : ℝ :=
  (Real.log ((2 * z.im) / fullRadius G t.toNNReal z) -
    Real.log ((2 * z.im) / fullRadius G σ z)) / 4

@[simp] lemma activeRadiusClock_start (G : ℝ≥0 → ℂ → ℂ) (z : ℂ) (σ : ℝ≥0) :
    activeRadiusClock G z σ σ = 0 := by
  simp [activeRadiusClock]

end SLEExactGauge.Multipoint

namespace SLEExactGauge

theorem IsCapacityTwoWitness.activeRadiusClock_hasDerivWithinAt
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    (σ T : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain γ T)
    (t : ℝ) (ht : t ∈ Icc 0 (T : ℝ)) :
    HasDerivWithinAt (Multipoint.activeRadiusClock G z σ)
      (chartPoissonRate U G t.toNNReal z ^ 2) (Icc 0 (T : ℝ)) t := by
  refine (((loewner_radius_clock_derivative hU hw T z hz t ht).sub_const
    (Real.log ((2 * z.im) / fullRadius G σ z))).div_const 4).congr_deriv ?_
  simp only [chartPoissonRate, Complex.normSq_eq_norm_sq]
  ring

theorem IsCapacityTwoWitness.activeRadiusClock_continuousOn
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    (σ T : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain γ T) :
    ContinuousOn (Multipoint.activeRadiusClock G z σ) (Icc 0 (T : ℝ)) := by
  intro t ht
  exact (hw.activeRadiusClock_hasDerivWithinAt hU σ T z hz t ht).continuousWithinAt

theorem IsCapacityTwoWitness.activeRadiusClock_nonneg
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    (σ T : ℝ≥0) (hσT : σ ≤ T) (z : ℂ) (hz : z ∈ survivingDomain γ T) :
    0 ≤ Multipoint.activeRadiusClock G z σ T := by
  have h := (hw.radius_clock_strictMonoOn hU z T hz).monotoneOn
    (show (σ : ℝ) ∈ Icc 0 (T : ℝ) from ⟨σ.coe_nonneg, hσT⟩)
    (show (T : ℝ) ∈ Icc 0 (T : ℝ) from ⟨T.coe_nonneg, le_rfl⟩) hσT
  simp only [Real.toNNReal_coe] at h
  change 0 ≤ (Real.log ((2 * z.im) / fullRadius G (T : ℝ).toNNReal z) -
    Real.log ((2 * z.im) / fullRadius G σ z)) / 4
  rw [Real.toNNReal_coe]
  exact div_nonneg (sub_nonneg.mpr h) (by norm_num)

/-- The physical conformal radius has the same ratio as the half-plane
radius. In particular, no derivative bound on `J` is needed. -/
theorem IsCapacityTwoWitness.physical_radius_active_clock
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    (J : ℂ → ℂ) (σ t : ℝ≥0) (z : ℂ)
    (hσ : z ∈ survivingDomain γ σ) (ht : z ∈ survivingDomain γ t) :
    physicalConformalRadius J G t z = physicalConformalRadius J G σ z *
      Real.exp (-4 * Multipoint.activeRadiusClock G z σ t) := by
  have hRσ := hw.fullRadius_positive hU σ z hσ
  have hRt := hw.fullRadius_positive hU t z ht
  have hz0 : 2 * z.im ≠ 0 := ne_of_gt (mul_pos (by norm_num) ht.1.1)
  have he : -4 * Multipoint.activeRadiusClock G z σ t =
      Real.log (fullRadius G t z / fullRadius G σ z) := by
    rw [Multipoint.activeRadiusClock, Real.toNNReal_coe,
      Real.log_div hz0 hRt.ne', Real.log_div hz0 hRσ.ne',
      Real.log_div hRt.ne' hRσ.ne']
    ring
  rw [he, Real.exp_log (div_pos hRt hRσ)]
  unfold physicalConformalRadius
  field_simp [hRσ.ne']

/-- One complete or partial active interval has regulator cost at most
`2 / β`, independently of its target-clock length. -/
theorem IsCapacityTwoWitness.active_regulator_integral_le
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    (σ T : ℝ≥0) (hσT : σ ≤ T) (z : ℂ) (hz : z ∈ survivingDomain γ T)
    {β target : ℝ} (hβ : 0 < β) (htarget : 0 ≤ target)
    (hclock : Multipoint.activeRadiusClock G z σ T ≤ target) :
    (∫ t in (σ : ℝ)..(T : ℝ),
      Multipoint.regulator β target (Multipoint.activeRadiusClock G z σ t) *
        chartPoissonRate U G t.toNNReal z ^ 2) ≤ 2 / β := by
  have hsub : Icc (σ : ℝ) (T : ℝ) ⊆ Icc (0 : ℝ) (T : ℝ) :=
    Icc_subset_Icc σ.coe_nonneg le_rfl
  have hclockcont : ContinuousOn (Multipoint.activeRadiusClock G z σ)
      (Icc (σ : ℝ) (T : ℝ)) := by
    intro t ht
    exact ((hw.activeRadiusClock_hasDerivWithinAt hU σ T z hz t (hsub ht)).mono
      hsub).continuousWithinAt
  apply Multipoint.regulator_clock_integral_le hβ htarget hσT
    (Multipoint.activeRadiusClock G z σ) (fun t => chartPoissonRate U G t.toNNReal z ^ 2)
    hclockcont ((hw.poissonRate_continuousOn hU T z hz).pow 2 |>.mono hsub)
  · intro t ht
    exact (hw.activeRadiusClock_hasDerivWithinAt hU σ T z hz t
      ⟨σ.coe_nonneg.trans ht.1.le, ht.2.le⟩).hasDerivAt
        (Icc_mem_nhds (σ.coe_nonneg.trans_lt ht.1) ht.2) |>.hasDerivWithinAt
  · simp
  · exact hclock
  · simpa [Multipoint.activeRadiusClock] using
      hw.activeRadiusClock_nonneg hU σ T hσT z hz

/-- The inverse pair regulator is paid by the actual physical-domain
interaction budget. The terminal clock levels can be arbitrary. -/
theorem IsCapacityTwoWitness.physical_pair_regulator_integral_le
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    (hgrowth : PublishedDiskUnivalentGrowth)
    (J : ℂ → ℂ) (hJ : DifferentiableOn ℂ J upperHalfPlane)
    (hJinj : InjOn J upperHalfPlane)
    (s T : ℝ≥0) (hsT : s ≤ T) (z w : ℂ)
    (hz : z ∈ survivingDomain γ T) (hw' : w ∈ survivingDomain γ T) (hne : z ≠ w)
    (bz bw : ℝ) (hbz : bz ≤ dist (J z) (J w)) (hbw : bw ≤ dist (J z) (J w))
    {β M : ℝ} (hβ : 0 ≤ β) (hM : 0 ≤ M) (hdecay : 2 * (M * β) < 2)
    (Uz Uw : ℝ) (u v : ℝ → ℝ)
    (hu : ContinuousOn u (Icc (s : ℝ) (T : ℝ)))
    (hv : ContinuousOn v (Icc (s : ℝ) (T : ℝ)))
    (hu0 : ∀ t ∈ Icc (s : ℝ) (T : ℝ), 0 ≤ u t)
    (hv0 : ∀ t ∈ Icc (s : ℝ) (T : ℝ), 0 ≤ v t)
    (hRu : ∀ t ∈ Icc (s : ℝ) (T : ℝ),
      physicalConformalRadius J G t.toNNReal z ≤ bz * Real.exp (-4 * u t))
    (hRv : ∀ t ∈ Icc (s : ℝ) (T : ℝ),
      physicalConformalRadius J G t.toNNReal w ≤ bw * Real.exp (-4 * v t)) :
    (∫ t in (s : ℝ)..(T : ℝ),
      (Multipoint.regulator β Uz (u t) * Multipoint.regulator β Uw (v t)) ^ (-M) *
        (chartPoissonRate U G t.toNNReal z * chartPoissonRate U G t.toNNReal w)) ≤
      Multipoint.interactionBudget 2 (M * β) := by
  have hsub : Icc (s : ℝ) (T : ℝ) ⊆ Icc (0 : ℝ) (T : ℝ) :=
    Icc_subset_Icc s.coe_nonneg le_rfl
  have hR := ((hw.poissonRate_continuousOn hU T z hz).mul
    (hw.poissonRate_continuousOn hU T w hw')).mono hsub
  have hreg := ((Multipoint.regulator_continuous β Uz).comp_continuousOn hu).mul
    ((Multipoint.regulator_continuous β Uw).comp_continuousOn hv)
  have hpw := hreg.rpow_const (p := -M) fun t _ => Or.inl
    (mul_pos (Multipoint.regulator_pos _ _ _) (Multipoint.regulator_pos _ _ _)).ne'
  apply le_trans (intervalIntegral.integral_mono_on hsT
    ((hpw.mul hR).intervalIntegrable_of_Icc hsT)
    (((Real.continuous_exp.comp_continuousOn
      (continuousOn_const.mul (hu.add hv))).mul hR).intervalIntegrable_of_Icc hsT) ?_)
    (hw.physical_pair_interaction_budget hU hgrowth J hJ hJinj s T hsT z w hz hw' hne
      bz bw hbz hbw (mul_nonneg hM hβ) hdecay u v hu hv hu0 hv0 hRu hRv)
  intro t ht
  apply mul_le_mul_of_nonneg_right (Multipoint.pair_regulator_inv_power_le hβ hM)
  have htT : t.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.mpr ht.2
  exact mul_nonneg
    (hw.poissonRate_nonneg _ z (survivingDomain_antitone γ htT hz))
    (hw.poissonRate_nonneg _ w (survivingDomain_antitone γ htT hw'))

/-- The pair discount on a joint active interval, expressed entirely in
the actual radius clocks measured from the individual activation times. -/
theorem IsCapacityTwoWitness.actual_pair_regulator_integral_le
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    (hgrowth : PublishedDiskUnivalentGrowth)
    (J : ℂ → ℂ) (hJ : DifferentiableOn ℂ J upperHalfPlane)
    (hJinj : InjOn J upperHalfPlane)
    (σz σw s T : ℝ≥0) (hσz : σz ≤ s) (hσw : σw ≤ s) (hsT : s ≤ T)
    (z w : ℂ) (hz : z ∈ survivingDomain γ T) (hw' : w ∈ survivingDomain γ T)
    (hne : z ≠ w)
    (hbz : physicalConformalRadius J G σz z ≤ dist (J z) (J w))
    (hbw : physicalConformalRadius J G σw w ≤ dist (J z) (J w))
    {β M : ℝ} (hβ : 0 ≤ β) (hM : 0 ≤ M) (hdecay : 2 * (M * β) < 2)
    (Uz Uw : ℝ) :
    (∫ t in (s : ℝ)..(T : ℝ),
      (Multipoint.regulator β Uz (Multipoint.activeRadiusClock G z σz t) *
        Multipoint.regulator β Uw (Multipoint.activeRadiusClock G w σw t)) ^ (-M) *
        (chartPoissonRate U G t.toNNReal z * chartPoissonRate U G t.toNNReal w)) ≤
      Multipoint.interactionBudget 2 (M * β) := by
  have hsub : Icc (s : ℝ) (T : ℝ) ⊆ Icc (0 : ℝ) (T : ℝ) :=
    Icc_subset_Icc s.coe_nonneg le_rfl
  have hzσ := survivingDomain_antitone γ (hσz.trans hsT) hz
  have hwσ := survivingDomain_antitone γ (hσw.trans hsT) hw'
  apply hw.physical_pair_regulator_integral_le hU hgrowth J hJ hJinj s T hsT z w hz hw'
    hne (physicalConformalRadius J G σz z) (physicalConformalRadius J G σw w)
    hbz hbw hβ hM hdecay Uz Uw
    (Multipoint.activeRadiusClock G z σz) (Multipoint.activeRadiusClock G w σw)
    ((hw.activeRadiusClock_continuousOn hU σz T z hz).mono hsub)
    ((hw.activeRadiusClock_continuousOn hU σw T w hw').mono hsub)
  · intro t ht
    have htT : t.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.mpr ht.2
    have hσzt : σz ≤ t.toNNReal := by
      simpa only [Real.toNNReal_coe] using
        Real.toNNReal_le_toNNReal ((show (σz : ℝ) ≤ s from hσz).trans ht.1)
    simpa only [Real.coe_toNNReal _ (s.coe_nonneg.trans ht.1)] using
      hw.activeRadiusClock_nonneg hU σz t.toNNReal hσzt z
        (survivingDomain_antitone γ htT hz)
  · intro t ht
    have htT : t.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.mpr ht.2
    have hσwt : σw ≤ t.toNNReal := by
      simpa only [Real.toNNReal_coe] using
        Real.toNNReal_le_toNNReal ((show (σw : ℝ) ≤ s from hσw).trans ht.1)
    simpa only [Real.coe_toNNReal _ (s.coe_nonneg.trans ht.1)] using
      hw.activeRadiusClock_nonneg hU σw t.toNNReal hσwt w
        (survivingDomain_antitone γ htT hw')
  · intro t ht
    have htT : t.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.mpr ht.2
    simpa only [Real.coe_toNNReal _ (s.coe_nonneg.trans ht.1)] using
      (hw.physical_radius_active_clock hU J σz t.toNNReal z hzσ
        (survivingDomain_antitone γ htT hz)).le
  · intro t ht
    have htT : t.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.mpr ht.2
    simpa only [Real.coe_toNNReal _ (s.coe_nonneg.trans ht.1)] using
      (hw.physical_radius_active_clock hU J σw t.toNNReal w hwσ
        (survivingDomain_antitone γ htT hw')).le

end SLEExactGauge

namespace SLEExactGauge.Multipoint

/-- The regulator is unchanged when moving from the capacity-two clock
`u` to the manuscript clock `κ * u`, provided its decay rate is scaled
by the inverse factor. -/
lemma regulator_scale_clock {κ : ℝ} (hκ : 0 ≤ κ) (β U u : ℝ) :
    regulator (κ * β) U u = regulator β (κ * U) (κ * u) := by
  unfold regulator
  rw [← mul_sub, ← mul_min_of_nonneg u (U-u) hκ]
  congr 1
  ring

lemma source_radius_clock_scale {κ : ℝ} (hκ : 0 < κ) (b u : ℝ) :
    b * Real.exp (-2 * (2 / κ) * (κ * u)) = b * Real.exp (-4 * u) := by
  congr 2
  field_simp [hκ.ne']
  ring

lemma source_pair_exponent_scale (κ c u v : ℝ) :
    Real.exp (c * (κ * u + κ * v)) = Real.exp ((κ * c) * (u + v)) := by
  congr 1
  ring

lemma source_pair_exponent_admissible {κ c : ℝ} (hκ : 0 < κ) :
    2 * (κ * c) < 2 ↔ 2 * c < 2 / κ := by
  rw [lt_div_iff₀ hκ]
  constructor <;> intro h <;> nlinarith

lemma source_terminal_factor_scale (κ p u : ℝ) :
    Real.exp ((κ * p) / 2 * u) = Real.exp (p / 2 * (κ * u)) := by
  congr 1
  ring

end SLEExactGauge.Multipoint

end

end OAI

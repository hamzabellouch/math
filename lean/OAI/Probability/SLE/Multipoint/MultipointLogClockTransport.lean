import OAI.Probability.SLE.Multipoint.MultipointFactorBranches
import OAI.Probability.SLE.Multipoint.MultipointRegulatorTransport
import OAI.Probability.SLE.DiskHalfPlane

namespace OAI

/-! The smooth logarithmic-coordinate factors use precisely the source
radius clock. These identities transport the proved one-point and pair
costs to the normalized branches, in capacity-two physical time. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal

namespace SLEExactGauge.Multipoint

lemma logFactorClock_eq_logRadiusClock (κ η : ℝ) (z : ℂ × ℝ) :
    logFactorClock κ z = κ/4*(logRadiusClock η z-η) := by
  unfold logFactorClock logRadiusClock
  ring

lemma regulator_scaled_argument {κ : ℝ} (hκ : 0 < κ) (β U u : ℝ) :
    regulator β U (κ*u) = regulator (κ*β) (U/κ) u := by
  rw [regulator_scale_clock hκ.le]
  have he : κ*(U/κ) = U := by field_simp [hκ.ne']
  rw [he]

lemma logVelocity_logCoordinates (κ : ℝ) (B : ℝ≥0 → ℝ)
    (G : ℝ≥0 → ℂ → ℂ) (z : ℂ) (t : ℝ)
    (hy : 0 < (G t.toNNReal z).im) :
    logVelocity κ (logLoewnerCoordinates G z t) (B t.toNNReal) =
      chartPoissonRate (fun u => Real.sqrt κ*B u) G t.toNNReal z := by
  have he : logLoewnerCoordinates G z t = logLoewnerCoordinates G z (t.toNNReal : ℝ) := by
    simp only [logLoewnerCoordinates, Real.toNNReal_coe]
  rw [he, logVelocity, logCoordinates_im, Real.exp_log hy,
    greenLogNormSq_logCoordinates κ (B t.toNNReal) G z t.toNNReal hy,
    Complex.normSq_eq_norm_sq]
  rfl

lemma logFactor_single_integrand_nonneg (κ β target : ℝ) (B : ℝ≥0 → ℝ)
    (G : ℝ≥0 → ℂ → ℂ) (z : ℂ) (σ : ℝ≥0) (t : ℝ) :
    0 ≤ regulator β target
      (logFactorClock κ (logLoewnerCoordinates G z t) -
        logFactorClock κ (logLoewnerCoordinates G z σ)) *
      logVelocity κ (logLoewnerCoordinates G z t) (B t.toNNReal)^2 :=
  mul_nonneg (regulator_pos _ _ _).le (sq_nonneg _)

lemma logFactor_pair_integrand_nonneg (κ β M Uz Uw : ℝ) (B : ℝ≥0 → ℝ)
    (G : ℝ≥0 → ℂ → ℂ) (z w : ℂ) (σz σw : ℝ≥0) (t : ℝ) :
    0 ≤ (regulator β Uz
      (logFactorClock κ (logLoewnerCoordinates G z t) -
        logFactorClock κ (logLoewnerCoordinates G z σz)) *
      regulator β Uw
      (logFactorClock κ (logLoewnerCoordinates G w t) -
        logFactorClock κ (logLoewnerCoordinates G w σw)))^(-M) *
      (logVelocity κ (logLoewnerCoordinates G z t) (B t.toNNReal) *
        logVelocity κ (logLoewnerCoordinates G w t) (B t.toNNReal)) :=
  mul_nonneg (Real.rpow_nonneg (mul_nonneg (regulator_pos _ _ _).le
    (regulator_pos _ _ _).le) _) (mul_pos (logVelocity_pos _ _ _) (logVelocity_pos _ _ _)).le

end SLEExactGauge.Multipoint

namespace SLEExactGauge

lemma IsCapacityTwoWitness.logFactorClock_sub
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    (κ : ℝ) (z : ℂ) (σ : ℝ≥0) (t : ℝ)
    (hσ : z ∈ survivingDomain γ σ) (ht : z ∈ survivingDomain γ t.toNNReal) :
    Multipoint.logFactorClock κ (logLoewnerCoordinates G z t) -
      Multipoint.logFactorClock κ (logLoewnerCoordinates G z σ) =
        κ*Multipoint.activeRadiusClock G z σ t := by
  have hLt : logRadiusClock (Real.log z.im) (logLoewnerCoordinates G z t) =
      Real.log ((2*z.im)/fullRadius G t.toNNReal z) := by
    simpa only [logLoewnerCoordinates, Real.toNNReal_coe] using
      logRadiusClock_logCoordinates hU hw z t.toNNReal ht
  have hLs := logRadiusClock_logCoordinates hU hw z σ hσ
  rw [Multipoint.logFactorClock_eq_logRadiusClock κ (Real.log z.im),
    Multipoint.logFactorClock_eq_logRadiusClock κ (Real.log z.im), hLt, hLs]
  unfold Multipoint.activeRadiusClock
  ring

/-- The one-point regulator cost in the smooth factor's clock units. -/
theorem IsCapacityTwoWitness.logFactor_single_regulator_integral_le
    {κ : ℝ} (hκ : 0 < κ) {B : ℝ≥0 → ℝ} (hB : Continuous B)
    {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ*B t) γ G F)
    (σ T : ℝ≥0) (hσT : σ ≤ T) (z : ℂ) (hz : z ∈ survivingDomain γ T)
    {β target : ℝ} (hβ : 0 < β) (htarget : 0 ≤ target)
    (hclock : Multipoint.logFactorClock κ (logLoewnerCoordinates G z T) -
      Multipoint.logFactorClock κ (logLoewnerCoordinates G z σ) ≤ target) :
    (∫ t in (σ : ℝ)..(T : ℝ),
      Multipoint.regulator β target
        (Multipoint.logFactorClock κ (logLoewnerCoordinates G z t) -
          Multipoint.logFactorClock κ (logLoewnerCoordinates G z σ)) *
        Multipoint.logVelocity κ (logLoewnerCoordinates G z t) (B t.toNNReal)^2) ≤
          2/(κ*β) := by
  have hU : Continuous (fun t => Real.sqrt κ*B t) := continuous_const.mul hB
  have hzσ := survivingDomain_antitone γ hσT hz
  have hclock' : Multipoint.activeRadiusClock G z σ T ≤ target/κ := by
    apply (le_div_iff₀ hκ).mpr
    have hc := hw.logFactorClock_sub hU κ z σ T hzσ (by simpa using hz)
    rw [hc] at hclock
    nlinarith only [hclock]
  have hb := hw.active_regulator_integral_le hU σ T hσT z hz
    (mul_pos hκ hβ) (div_nonneg htarget hκ.le) hclock'
  convert hb using 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le (show (σ : ℝ) ≤ T by exact_mod_cast hσT)] at ht
  have htT : t.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.mpr ht.2
  have hzt := survivingDomain_antitone γ htT hz
  dsimp only
  rw [hw.logFactorClock_sub hU κ z σ t hzσ hzt,
    Multipoint.regulator_scaled_argument hκ,
    Multipoint.logVelocity_logCoordinates κ B G z t (hw.imag_positive _ z hzt)]

/-- Including the generator's factor `κ` gives exactly the source bound. -/
theorem IsCapacityTwoWitness.logFactor_single_discount_le
    {κ : ℝ} (hκ : 0 < κ) {B : ℝ≥0 → ℝ} (hB : Continuous B)
    {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ*B t) γ G F)
    (σ T : ℝ≥0) (hσT : σ ≤ T) (z : ℂ) (hz : z ∈ survivingDomain γ T)
    {β target : ℝ} (hβ : 0 < β) (htarget : 0 ≤ target)
    (hclock : Multipoint.logFactorClock κ (logLoewnerCoordinates G z T) -
      Multipoint.logFactorClock κ (logLoewnerCoordinates G z σ) ≤ target) :
    κ*(∫ t in (σ : ℝ)..(T : ℝ),
      Multipoint.regulator β target
        (Multipoint.logFactorClock κ (logLoewnerCoordinates G z t) -
          Multipoint.logFactorClock κ (logLoewnerCoordinates G z σ)) *
        Multipoint.logVelocity κ (logLoewnerCoordinates G z t) (B t.toNNReal)^2) ≤
          2/β := by
  have hb := mul_le_mul_of_nonneg_left
    (hw.logFactor_single_regulator_integral_le hκ hB σ T hσT z hz hβ htarget hclock) hκ.le
  have he : κ*(2/(κ*β)) = 2/β := by field_simp [hκ.ne', hβ.ne']
  rwa [he] at hb

/-- Pair interaction cost for the source-normalized regulator branches.
The physical-time interaction budget remains in capacity-two units. -/
theorem IsCapacityTwoWitness.logFactor_pair_regulator_integral_le
    {κ : ℝ} (hκ : 0 < κ) {B : ℝ≥0 → ℝ} (hB : Continuous B)
    {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ*B t) γ G F)
    (hgrowth : PublishedDiskUnivalentGrowth)
    (J : ℂ → ℂ) (hJ : DifferentiableOn ℂ J upperHalfPlane)
    (hJinj : InjOn J upperHalfPlane)
    (σz σw s T : ℝ≥0) (hσz : σz ≤ s) (hσw : σw ≤ s) (hsT : s ≤ T)
    (z w : ℂ) (hz : z ∈ survivingDomain γ T) (hw' : w ∈ survivingDomain γ T)
    (hne : z ≠ w)
    (hbz : physicalConformalRadius J G σz z ≤ dist (J z) (J w))
    (hbw : physicalConformalRadius J G σw w ≤ dist (J z) (J w))
    {β M : ℝ} (hβ : 0 ≤ β) (hM : 0 ≤ M) (hdecay : 2*(M*β) < 2/κ)
    (Uz Uw : ℝ) :
    (∫ t in (s : ℝ)..(T : ℝ),
      (Multipoint.regulator β Uz
        (Multipoint.logFactorClock κ (logLoewnerCoordinates G z t) -
          Multipoint.logFactorClock κ (logLoewnerCoordinates G z σz)) *
       Multipoint.regulator β Uw
        (Multipoint.logFactorClock κ (logLoewnerCoordinates G w t) -
          Multipoint.logFactorClock κ (logLoewnerCoordinates G w σw)))^(-M) *
      (Multipoint.logVelocity κ (logLoewnerCoordinates G z t) (B t.toNNReal) *
        Multipoint.logVelocity κ (logLoewnerCoordinates G w t) (B t.toNNReal))) ≤
      Multipoint.interactionBudget 2 (M*(κ*β)) := by
  have hU : Continuous (fun t => Real.sqrt κ*B t) := continuous_const.mul hB
  have hzσ := survivingDomain_antitone γ (hσz.trans hsT) hz
  have hwσ := survivingDomain_antitone γ (hσw.trans hsT) hw'
  have hadm : 2*(M*(κ*β)) < 2 := by
    have hh := (Multipoint.source_pair_exponent_admissible (c := M*β) hκ).mpr hdecay
    convert hh using 1
    ring
  have hb := hw.actual_pair_regulator_integral_le hU hgrowth J hJ hJinj
    σz σw s T hσz hσw hsT z w hz hw' hne hbz hbw (mul_nonneg hκ.le hβ) hM hadm
    (Uz/κ) (Uw/κ)
  convert hb using 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le (show (s : ℝ) ≤ T by exact_mod_cast hsT)] at ht
  have htT : t.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.mpr ht.2
  have hzt := survivingDomain_antitone γ htT hz
  have hwt := survivingDomain_antitone γ htT hw'
  dsimp only
  rw [hw.logFactorClock_sub hU κ z σz t hzσ hzt,
    hw.logFactorClock_sub hU κ w σw t hwσ hwt,
    Multipoint.regulator_scaled_argument hκ, Multipoint.regulator_scaled_argument hκ,
    Multipoint.logVelocity_logCoordinates κ B G z t (hw.imag_positive _ z hzt),
    Multipoint.logVelocity_logCoordinates κ B G w t (hw.imag_positive _ w hwt)]

lemma IsCapacityTwoWitness.logFactorClock_sub_continuousOn
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness U γ G F) (hU : Continuous U)
    (κ : ℝ) (σ T : ℝ≥0) (z : ℂ)
    (hσ : z ∈ survivingDomain γ σ) (hz : z ∈ survivingDomain γ T) :
    ContinuousOn (fun t : ℝ =>
      Multipoint.logFactorClock κ (logLoewnerCoordinates G z t) -
        Multipoint.logFactorClock κ (logLoewnerCoordinates G z σ)) (Icc 0 (T : ℝ)) := by
  apply (continuousOn_const.mul (hw.activeRadiusClock_continuousOn hU σ T z hz)).congr
  intro t ht
  exact hw.logFactorClock_sub hU κ z σ t hσ
    (hw.live_at_real_time T z hz t ht.2)

lemma IsCapacityTwoWitness.logVelocity_continuousOn
    {κ : ℝ} {B : ℝ≥0 → ℝ} (hB : Continuous B)
    {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ*B t) γ G F)
    (T : ℝ≥0) (z : ℂ) (hz : z ∈ survivingDomain γ T) :
    ContinuousOn (fun t : ℝ =>
      Multipoint.logVelocity κ (logLoewnerCoordinates G z t) (B t.toNNReal))
      (Icc 0 (T : ℝ)) := by
  apply (hw.poissonRate_continuousOn (continuous_const.mul hB) T z hz).congr
  intro t ht
  exact Multipoint.logVelocity_logCoordinates κ B G z t
    (hw.imag_positive _ z (hw.live_at_real_time T z hz t ht.2))

/-- Integrability for the exact source-clock single-point cost on its own
active interval. The endpoint may be specific to this marked point. -/
theorem IsCapacityTwoWitness.logFactor_single_intervalIntegrable
    {κ : ℝ} {B : ℝ≥0 → ℝ} (hB : Continuous B)
    {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ*B t) γ G F)
    (σ T : ℝ≥0) (hσT : σ ≤ T) (z : ℂ) (hz : z ∈ survivingDomain γ T)
    (β target : ℝ) :
    IntervalIntegrable (fun t : ℝ =>
      Multipoint.regulator β target
        (Multipoint.logFactorClock κ (logLoewnerCoordinates G z t) -
          Multipoint.logFactorClock κ (logLoewnerCoordinates G z σ)) *
        Multipoint.logVelocity κ (logLoewnerCoordinates G z t) (B t.toNNReal)^2)
      volume (σ : ℝ) (T : ℝ) := by
  have hU : Continuous (fun t => Real.sqrt κ*B t) := continuous_const.mul hB
  have hσ := survivingDomain_antitone γ hσT hz
  have hc := (Multipoint.regulator_continuous β target).comp_continuousOn
    (hw.logFactorClock_sub_continuousOn hU κ σ T z hσ hz)
  have hv := (hw.logVelocity_continuousOn hB T z hz).pow 2
  have hsub : Icc (σ : ℝ) (T : ℝ) ⊆ Icc 0 (T : ℝ) :=
    Icc_subset_Icc σ.coe_nonneg le_rfl
  exact ((hc.mul hv).mono hsub).intervalIntegrable_of_Icc
    (show (σ : ℝ) ≤ T by exact_mod_cast hσT)

/-- Integrability for the exact source-clock pair cost on the overlap of
the two active intervals; the common endpoint may be their minimum. -/
theorem IsCapacityTwoWitness.logFactor_pair_intervalIntegrable
    {κ : ℝ} {B : ℝ≥0 → ℝ} (hB : Continuous B)
    {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ*B t) γ G F)
    (σz σw s T : ℝ≥0) (hσz : σz ≤ s) (hσw : σw ≤ s) (hsT : s ≤ T)
    (z w : ℂ) (hz : z ∈ survivingDomain γ T) (hw' : w ∈ survivingDomain γ T)
    (β M Uz Uw : ℝ) :
    IntervalIntegrable (fun t : ℝ =>
      (Multipoint.regulator β Uz
        (Multipoint.logFactorClock κ (logLoewnerCoordinates G z t) -
          Multipoint.logFactorClock κ (logLoewnerCoordinates G z σz)) *
       Multipoint.regulator β Uw
        (Multipoint.logFactorClock κ (logLoewnerCoordinates G w t) -
          Multipoint.logFactorClock κ (logLoewnerCoordinates G w σw)))^(-M) *
      (Multipoint.logVelocity κ (logLoewnerCoordinates G z t) (B t.toNNReal) *
        Multipoint.logVelocity κ (logLoewnerCoordinates G w t) (B t.toNNReal)))
      volume (s : ℝ) (T : ℝ) := by
  have hU : Continuous (fun t => Real.sqrt κ*B t) := continuous_const.mul hB
  have hzσ := survivingDomain_antitone γ (hσz.trans hsT) hz
  have hwσ := survivingDomain_antitone γ (hσw.trans hsT) hw'
  have hzclock := hw.logFactorClock_sub_continuousOn hU κ σz T z hzσ hz
  have hwclock := hw.logFactorClock_sub_continuousOn hU κ σw T w hwσ hw'
  have hreg := ((Multipoint.regulator_continuous β Uz).comp_continuousOn hzclock).mul
    ((Multipoint.regulator_continuous β Uw).comp_continuousOn hwclock)
  have hpw := hreg.rpow_const (p := -M) fun t _ => Or.inl
    (mul_pos (Multipoint.regulator_pos _ _ _) (Multipoint.regulator_pos _ _ _)).ne'
  have hv := (hw.logVelocity_continuousOn hB T z hz).mul
    (hw.logVelocity_continuousOn hB T w hw')
  have hsub : Icc (s : ℝ) (T : ℝ) ⊆ Icc 0 (T : ℝ) :=
    Icc_subset_Icc s.coe_nonneg le_rfl
  exact ((hpw.mul hv).mono hsub).intervalIntegrable_of_Icc
    (show (s : ℝ) ≤ T by exact_mod_cast hsT)

end SLEExactGauge

end

end OAI

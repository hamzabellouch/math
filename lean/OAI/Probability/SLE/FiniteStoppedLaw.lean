import Mathlib
import OAI.Probability.SLE.KernelExpectation

namespace OAI

/-! Finite Stopped Law for chordal SLE. -/

section
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 

theorem finite_stopped_green_regular
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (u : ℝ) (hu : 0 ≤ u) :
    Integrable (fun ω => stoppedGreen κ (fun t => Real.sqrt κ * B t ω)
      (γ ω) (G ω) z u) P ∧
    (∫ ω, stoppedGreen κ (fun t => Real.sqrt κ * B t ω)
      (γ ω) (G ω) z u ∂P) = initialGreen κ z := by
  let A := logAngleSq κ (initialLogCoordinates z) 0
  have hA : 0 < A := logAngleSq_pos _ _ _
  let ε (n : ℕ) := A / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hεA (n : ℕ) : ε n ≤ A := div_le_self hA.le (by have h := Nat.cast_nonneg (α := ℝ) n; linarith)
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    have hh := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul A
    simpa only [mul_one_div, mul_zero] using hh
  choose f hfi hfm hfb hfw using fun n => exists_finite_angular_kernel
    hB hBm hBc hB0 κ hκ hκ8 z hz u hu (ε n) (hε n) (hεA n)
  let K := Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im))
  let g (ω : Ω) := stoppedGreen κ (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) z u
  have hp : 0 < greenExponent κ / 2 := div_pos (greenExponent_pos κ hκ hκ8) (by norm_num)
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (g ω)) := by
    filter_upwards [hw] with ω hω
    have hU : Continuous (fun t => Real.sqrt κ * B t ω) := (hBc ω).const_mul _
    by_cases hlevel : ∃ T : ℝ≥0, z ∈ survivingDomain (γ ω) T ∧
        fullRadius (G ω) T z = (2 * z.im) * Real.exp (-u)
    · obtain ⟨T, hT, hTR⟩ := hlevel
      obtain ⟨δ, hδ, hδb⟩ := live_angleSq_lower_bound hU hω z T hT
      have hev : ∀ᶠ n in atTop, ε n < δ := (tendsto_order.mp hεlim).2 δ hδ
      apply tendsto_const_nhds.congr'
      filter_upwards [hev] with n hn
      obtain ⟨t, ht, htu, hb, he, _⟩ := hfw n ω (γ ω) (G ω) (F ω) hω
      have hTc : Real.log ((2 * z.im) / fullRadius (G ω) T z) = u := by
        rw [← logRadiusClock_logCoordinates hU hω z T hT]
        exact (fullRadius_level_iff_logClock hU hω z T hT u).mp hTR
      have htT : t ≤ T := live_clock_le_time hU hω z t T ht hT (by simpa only [hTc] using htu)
      have htb : δ ≤ (Real.sin (Complex.arg (G ω t z - ((Real.sqrt κ * B t ω : ℝ) : ℂ)))) ^ 2 :=
        hδb t htT
      have htc : Real.log ((2 * z.im) / fullRadius (G ω) t z) = u := hb.resolve_right (by linarith)
      have htR : fullRadius (G ω) t z = (2 * z.im) * Real.exp (-u) := by
        apply (fullRadius_level_iff_logClock hU hω z t ht u).mpr
        rwa [logRadiusClock_logCoordinates hU hω z t ht]
      exact (stoppedGreen_eq_of_live_level hU hω κ z u t ht htR).trans he.symm
    · have hg : g ω = 0 := stoppedGreen_eq_zero_of_no_level κ _ _ _ z u hlevel
      rw [hg]
      have hb (n : ℕ) : f n ω ≤ K * (ε n) ^ (greenExponent κ / 2) := by
        obtain ⟨t, ht, _, htb, _, hbe⟩ := hfw n ω (γ ω) (G ω) (F ω) hω
        apply hbe
        apply htb.resolve_left
        intro he
        apply hlevel
        refine ⟨t, ht, (fullRadius_level_iff_logClock hU hω z t ht u).mpr ?_⟩
        rwa [logRadiusClock_logCoordinates hU hω z t ht]
      have hupp : Tendsto (fun n => K * (ε n) ^ (greenExponent κ / 2)) atTop (𝓝 0) := by
        have hh := ((Real.continuousAt_rpow_const 0 (greenExponent κ / 2) (Or.inr hp.le)).tendsto.comp hεlim).const_mul K
        simpa only [Function.comp_apply, Real.zero_rpow hp.ne', mul_zero] using hh
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupp
        (fun n => (hfb n ω).1) hb
  have hbound (n : ℕ) : ∀ᵐ ω ∂P, ‖f n ω‖ ≤ K := by
    apply Eventually.of_forall
    intro ω
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hfb n ω).1] using (hfb n ω).2
  have hgm : AEStronglyMeasurable g P :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hfi n).aestronglyMeasurable) hlim
  have hgi : Integrable g P := ⟨hgm,
    hasFiniteIntegral_of_dominated_convergence (integrable_const K).hasFiniteIntegral hbound hlim⟩
  have hc := tendsto_integral_of_dominated_convergence (fun _ : Ω => K)
    (fun n => (hfi n).aestronglyMeasurable) (integrable_const K) hbound hlim
  refine ⟨hgi, ?_⟩
  apply tendsto_nhds_unique hc
  simpa only [hfm] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => initialGreen κ z) atTop (𝓝 (initialGreen κ z)))

 

theorem finite_stopped_green_of_witness
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (u : ℝ) (hu : 0 ≤ u) :
    Integrable (fun ω => stoppedGreen κ (fun t => Real.sqrt κ * B t ω)
      (γ ω) (G ω) z u) P ∧
    (∫ ω, stoppedGreen κ (fun t => Real.sqrt κ * B t ω)
      (γ ω) (G ω) z u ∂P) = initialGreen κ z := by
  obtain ⟨C, hCm, hCc, hC0, hC, hCB⟩ := exists_regular_brownian_version hB
  have hwC : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * C t ω) (γ ω) (G ω) (F ω) := by
    filter_upwards [hw, hCB] with ω hω hω'
    simpa only [hω'] using hω
  have heq : (fun ω => stoppedGreen κ (fun t => Real.sqrt κ * C t ω)
      (γ ω) (G ω) z u) =ᵐ[P] (fun ω => stoppedGreen κ (fun t => Real.sqrt κ * B t ω)
      (γ ω) (G ω) z u) := by
    filter_upwards [hCB] with ω hω
    simp only [hω]
  obtain ⟨hfi, hfm⟩ := finite_stopped_green_regular hC hCm hCc hC0 κ hκ hκ8 γ G F hwC z hz u hu
  exact ⟨hfi.congr heq, (integral_congr_ae heq).symm.trans hfm⟩

universe uLevel
def FiniteStoppedGreenTarget : Prop :=
  ∀ (Ω : Type uLevel) (_ : MeasurableSpace Ω) (P : Measure Ω), IsProbabilityMeasure P →
    ∀ (κ : ℝ), 0 < κ → κ < 8 →
    ∀ (B : ℝ≥0 → Ω → ℝ), ProbabilityTheory.IsBrownianReal B P →
    ∀ (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ),
      (∀ t, Measurable (fun ω => γ ω t)) →
      (∀ᵐ ω ∂P, IsCapacityTwoWitness
        (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω)) →
      ∀ (z : ℂ), z ∈ upperHalfPlane → ∀ (u : ℝ), 0 ≤ u →
        Integrable (fun ω => stoppedGreen κ (fun t => Real.sqrt κ * B t ω)
          (γ ω) (G ω) z u) P ∧
        (∫ ω, stoppedGreen κ (fun t => Real.sqrt κ * B t ω)
          (γ ω) (G ω) z u ∂P) = initialGreen κ z

 

theorem finite_stopped_green : FiniteStoppedGreenTarget := by
  intro Ω mΩ P hP κ hκ hκ8 B hB γ G F _hγ hw z hz u hu
  let := hP
  exact finite_stopped_green_of_witness hB κ hκ hκ8 γ G F hw z hz u hu

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

lemma initialGreen_pos (κ : ℝ) (z : ℂ) (hz : z ∈ upperHalfPlane) :
    0 < initialGreen κ z := by
  have hz0 : z ≠ 0 := by intro he; simp only [he, upperHalfPlane, Set.mem_ofPred_eq, Complex.zero_im, lt_self_iff_false] at hz
  have hsin : 0 < Real.sin (Complex.arg z) := by
    rw [Complex.sin_arg]
    exact div_pos hz (norm_pos_iff.mpr hz0)
  exact mul_pos (Real.rpow_pos_of_pos (mul_pos (by norm_num) hz) _) (Real.rpow_pos_of_pos hsin _)

lemma greenDensity_nonneg
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (κ : ℝ) (t : ℝ≥0) (z : ℂ) :
    0 ≤ greenDensity κ U γ G t z := by
  classical
  by_cases hz : z ∈ survivingDomain γ t
  · rw [greenDensity, ite_eq_left hz]
    have hy := h.imag_positive t z hz
    apply mul_nonneg
    · exact Real.rpow_nonneg (div_nonneg (mul_nonneg (by norm_num) hy.le) (norm_nonneg _)) _
    · apply Real.rpow_nonneg
      rw [Complex.sin_arg, Complex.sub_im, Complex.ofReal_im, sub_zero]
      exact div_nonneg hy.le (norm_nonneg _)
  · simp only [greenDensity, ite_eq_right hz, le_refl]

lemma stoppedGreen_nonneg
    {U : ℝ≥0 → ℝ} {γ : ℝ≥0 → ℂ} {G F : ℝ≥0 → ℂ → ℂ}
    (h : IsCapacityTwoWitness U γ G F) (κ : ℝ) (z : ℂ) (u : ℝ) :
    0 ≤ stoppedGreen κ U γ G z u := by
  unfold stoppedGreen
  split_ifs
  · exact greenDensity_nonneg h κ _ z
  · exact le_rfl

 

noncomputable def finiteCenteredLaw
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (κ : ℝ)
    (B : ℝ≥0 → Ω → ℝ) (γ : Ω → ℝ≥0 → ℂ) (G : Ω → ℝ≥0 → ℂ → ℂ)
    (z : ℂ) (u : ℝ) : Measure Ω :=
  P.withDensity (fun ω => ENNReal.ofReal
    (stoppedGreen κ (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) z u / initialGreen κ z))

theorem finiteCenteredLaw_probability
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (u : ℝ) (hu : 0 ≤ u) :
    IsProbabilityMeasure (finiteCenteredLaw P κ B γ G z u) := by
  obtain ⟨hi, he⟩ := finite_stopped_green_of_witness hB κ hκ hκ8 γ G F hw z hz u hu
  have hp := initialGreen_pos κ z hz
  apply isProbabilityMeasure_iff.mpr
  rw [finiteCenteredLaw, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hi.div_const _) ?_, integral_div, he, div_self hp.ne', ENNReal.ofReal_one]
  filter_upwards [hw] with ω hω
  exact div_nonneg (stoppedGreen_nonneg hω κ z u) hp.le

 

theorem finiteCenteredLaw_live_compact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (u : ℝ) (hu : 0 ≤ u) :
    ∀ᵐ ω ∂finiteCenteredLaw P κ B γ G z u,
      ∃ T : ℝ≥0, z ∈ survivingDomain (γ ω) T ∧
        fullRadius (G ω) T z = (2 * z.im) * Real.exp (-u) ∧
        radiusLevelTime (γ ω) (G ω) z u = (T : ℝ≥0∞) ∧
        ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ≥0, t ≤ T →
          δ ≤ (Real.sin (Complex.arg (G ω t z - ((Real.sqrt κ * B t ω : ℝ) : ℂ)))) ^ 2 := by
  obtain ⟨hi, _⟩ := finite_stopped_green_of_witness hB κ hκ hκ8 γ G F hw z hz u hu
  apply (ae_withDensity_iff' ((hi.div_const _).aestronglyMeasurable.aemeasurable.ennreal_ofReal)).mpr
  filter_upwards [hw, hB.cont] with ω hω hcont
  intro hweight
  have hex : ∃ T : ℝ≥0, z ∈ survivingDomain (γ ω) T ∧
      fullRadius (G ω) T z = (2 * z.im) * Real.exp (-u) := by
    by_contra hn
    apply hweight
    rw [stoppedGreen_eq_zero_of_no_level κ _ _ _ z u hn, zero_div, ENNReal.ofReal_zero]
  obtain ⟨T, hT, hTR⟩ := hex
  have hU : Continuous (fun t => Real.sqrt κ * B t ω) := hcont.const_mul _
  exact ⟨T, hT, hTR, radiusLevelTime_eq_of_live_level hU hω z u T hT hTR,
    live_angleSq_lower_bound hU hω z T hT⟩

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory
open scoped Topology
namespace SLEExactGauge

lemma continuousOn_of_integral_balance {F H : ℝ → ℝ} {v A C L : ℝ}
    (hv : 0 ≤ v) (hFi : IntervalIntegrable F volume 0 v) (hHi : IntervalIntegrable H volume 0 v)
    (hbal : ∀ u ∈ Icc 0 v, F u + C * (∫ s in (0 : ℝ)..u, H s) =
      L + A * (∫ s in (0 : ℝ)..u, F s)) : ContinuousOn F (Icc 0 v) := by
  have hcF : ContinuousOn (fun u => ∫ s in (0 : ℝ)..u, F s) (Icc 0 v) := by
    simpa only [uIcc_of_le hv] using intervalIntegral.continuousOn_primitive_interval (f := F) (a := 0) (b := v) (μ := volume)
      (by simpa only [uIcc_of_le hv] using (intervalIntegrable_iff_integrableOn_Icc_of_le hv).mp hFi)
  have hcH : ContinuousOn (fun u => ∫ s in (0 : ℝ)..u, H s) (Icc 0 v) := by
    simpa only [uIcc_of_le hv] using intervalIntegral.continuousOn_primitive_interval (f := H) (a := 0) (b := v) (μ := volume)
      (by simpa only [uIcc_of_le hv] using (intervalIntegrable_iff_integrableOn_Icc_of_le hv).mp hHi)
  have hc : ContinuousOn (fun u => L + A * (∫ s in (0 : ℝ)..u, F s) - C * (∫ s in (0 : ℝ)..u, H s)) (Icc 0 v) :=
    (continuousOn_const.add (continuousOn_const.mul hcF)).sub (continuousOn_const.mul hcH)
  apply hc.congr
  intro u hu
  dsimp only
  linarith [hbal u hu]

lemma integral_drift_of_balance {F H : ℝ → ℝ} {v A C L q : ℝ}
    (hv : 0 ≤ v) (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hFi : IntervalIntegrable F volume 0 v) (hHi : IntervalIntegrable H volume 0 v)
    (hbal : ∀ u ∈ Icc 0 v, F u + C * (∫ s in (0 : ℝ)..u, H s) =
      L + A * (∫ s in (0 : ℝ)..u, F s))
    (hpow : ∀ᵐ s ∂volume.restrict (Ioc 0 v), (F s) ^ q ≤ H s) :
    ContinuousOn F (Icc 0 v) ∧
      ∀ s ∈ Icc 0 v, ∀ t ∈ Icc 0 v, s ≤ t →
        F t - F s ≤ ∫ u in s..t, A * F u - C * (F u) ^ q := by
  have hc := continuousOn_of_integral_balance hv hFi hHi hbal
  refine ⟨hc, ?_⟩
  intro s hs t ht hst
  have hsub : uIcc s t ⊆ uIcc 0 v := by
    simp only [uIcc_of_le hst, uIcc_of_le hv]
    exact Icc_subset_Icc hs.1 ht.2
  have hsub0 (x : ℝ) (hx : x ∈ Icc 0 v) : uIcc 0 x ⊆ uIcc 0 v := by
    simp only [uIcc_of_le hx.1, uIcc_of_le hv]
    exact Icc_subset_Icc le_rfl hx.2
  have hFi' := hFi.mono_set hsub
  have hHi' := hHi.mono_set hsub
  have hpI : IntervalIntegrable (fun u => F u ^ q) volume s t := by
    apply ContinuousOn.intervalIntegrable
    apply (Real.continuous_rpow_const hq).comp_continuousOn
    exact hc.mono (by simpa only [uIcc_of_le hst] using Icc_subset_Icc hs.1 ht.2)
  have hpw : (∫ u in s..t, (F u) ^ q) ≤ ∫ u in s..t, H u := by
    apply intervalIntegral.integral_mono_ae_restrict hst hpI hHi'
    rw [restrict_Ioc_eq_restrict_Icc] at hpow
    exact ae_restrict_of_ae_restrict_of_subset (Icc_subset_Icc hs.1 ht.2) hpow
  have hdiff : F t - F s = A * (∫ u in s..t, F u) - C * (∫ u in s..t, H u) := by
    rw [← intervalIntegral.integral_interval_sub_left (hFi.mono_set (hsub0 t ht)) (hFi.mono_set (hsub0 s hs)),
      ← intervalIntegral.integral_interval_sub_left (hHi.mono_set (hsub0 t ht)) (hHi.mono_set (hsub0 s hs))]
    linarith [hbal s hs, hbal t ht]
  rw [intervalIntegral.integral_sub (hFi'.const_mul A) (hpI.const_mul C),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hdiff]
  exact sub_le_sub_left (mul_le_mul_of_nonneg_left hpw hC) _

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {v : ℝ≥0} {ε : ℕ → ℝ}

noncomputable def radiusMoment (P : Measure Ω)
    (c : ∀ n, AngularLocalization B hm κ z v (ε n)) (b s : ℝ) : ℝ :=
  (∫ ω, limitRadiusKernel c (codimension κ) (greenExponent κ - b) s ω ∂P) / initialGreen κ z

lemma radiusMoment_nonneg {P : Measure Ω}
    (c : ∀ n, AngularLocalization B hm κ z v (ε n)) (hI : 0 ≤ initialGreen κ z) (b s : ℝ) :
    0 ≤ radiusMoment P c b s :=
  div_nonneg (integral_nonneg fun ω => limitRadiusKernel_nonneg c _ _ s ω) hI

lemma radiusMoment_intervalIntegrable {P : Measure Ω} [IsFiniteMeasure P]
    (c : ∀ n, AngularLocalization B hm κ z v (ε n)) {b u : ℝ} (hu : 0 ≤ u)
    (hi : Integrable (Function.uncurry (limitRadiusKernel c (codimension κ) (greenExponent κ - b)))
      ((volume.restrict (Ioc 0 u)).prod P)) : IntervalIntegrable (radiusMoment P c b) volume 0 u := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hu]
  exact hi.integral_prod_left.div_const _

lemma radiusMoment_intervalIntegral {P : Measure Ω} [IsFiniteMeasure P]
    (c : ∀ n, AngularLocalization B hm κ z v (ε n)) {b u : ℝ} (hu : 0 ≤ u)
    (hi : Integrable (Function.uncurry (limitRadiusKernel c (codimension κ) (greenExponent κ - b)))
      ((volume.restrict (Ioc 0 u)).prod P)) :
    (∫ s in (0 : ℝ)..u, radiusMoment P c b s) =
      (∫ q : ℝ × Ω, limitRadiusKernel c (codimension κ) (greenExponent κ - b) q.1 q.2
        ∂((volume.restrict (Ioc 0 u)).prod P)) / initialGreen κ z := by
  simp only [intervalIntegral.integral_of_le hu, radiusMoment, integral_div]
  congr 1
  exact (integral_prod _ hi).symm

lemma balance_divide {X H Y F A C : ℝ} (he : X + C * H = Y + A * F) (I : ℝ) :
    X / I + C * (H / I) = Y / I + A * (F / I) := by
  linear_combination (1 / I) * he

lemma radiusMoment_balance
    (a : ∀ u : ℝ≥0, ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0)) (hε0 : ∀ n, 0 < ε n)
    {P : Measure Ω} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (hκ : 0 < κ) (hκ8 : κ < 8) (b : ℝ) (hb0 : 0 < b) (hb : b < greenExponent κ)
    (u : ℝ) (hu : u ∈ Icc 0 (v : ℝ)) :
    radiusMoment P (a v) b u + (κ * b / 8) * (greenExponent κ - b) *
      (∫ s in (0 : ℝ)..u, radiusMoment P (a v) (b + 2) s) =
    powerLogDensity κ (codimension κ) (greenExponent κ - b) (initialLogCoordinates z) 0 / initialGreen κ z +
      (κ * b / 8) * (1 + (greenExponent κ - b)) *
        (∫ s in (0 : ℝ)..u, radiusMoment P (a v) b s) := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  obtain ⟨hi, he⟩ := limit_power_balance (a ⟨u, hu.1⟩) (a v) hε hεlim hε0 hB hBm hBc hB0
    hκ hκ8 b hb0 hb hu.1 hu.2
  dsimp only [NNReal.toReal] at hi he
  have hi' : Integrable (Function.uncurry (limitRadiusKernel (a v) (codimension κ) (greenExponent κ - (b + 2))))
      ((volume.restrict (Ioc 0 u)).prod P) := by
    rw [show greenExponent κ - (b + 2) = greenExponent κ - b - 2 by ring]
    convert hi using 1; rfl
  have hl := limitRadiusKernel_region_integrable (P := P) (a v) hε hBm (codimension κ)
    (greenExponent κ - b) (codimension_pos κ hκ8).le (sub_pos.mpr hb).le u
  rw [radiusMoment_intervalIntegral _ hu.1 hi', radiusMoment_intervalIntegral _ hu.1 hl]
  dsimp only [radiusMoment]
  rw [sub_add_eq_sub_sub]
  convert balance_divide he (initialGreen κ z) using 1 <;> rfl

 

theorem radiusMoment_drift
    (a : ∀ u : ℝ≥0, ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0)) (hε0 : ∀ n, 0 < ε n)
    {P : Measure Ω} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (hκ : 0 < κ) (hκ8 : κ < 8) (hz : z ∈ upperHalfPlane)
    (b : ℝ) (hb0 : 0 < b) (hb : b < greenExponent κ) :
    ContinuousOn (radiusMoment P (a v) b) (Icc 0 v) ∧
      ∀ s ∈ Icc 0 (v : ℝ), ∀ t ∈ Icc 0 (v : ℝ), s ≤ t →
        radiusMoment P (a v) b t - radiusMoment P (a v) b s ≤
          ∫ u in s..t, (κ * b / 8) * (1 + (greenExponent κ - b)) * radiusMoment P (a v) b u -
            (κ * b / 8) * (greenExponent κ - b) * (radiusMoment P (a v) b u) ^ (1 + 2 / b) := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  have hI : 0 < initialGreen κ z := initialGreen_pos κ z hz
  have hh := (limit_power_balance (a v) (a v) hε hεlim hε0 hB hBm hBc hB0 hκ hκ8 b hb0 hb v.coe_nonneg le_rfl).1
  have hhigh : IntervalIntegrable (radiusMoment P (a v) (b + 2)) volume 0 v := by
    apply radiusMoment_intervalIntegrable _ v.coe_nonneg
    simpa only [sub_add_eq_sub_sub] using hh
  have hlow := radiusMoment_intervalIntegrable (P := P) (a v) v.coe_nonneg
    (limitRadiusKernel_region_integrable (a v) hε hBm (codimension κ) (greenExponent κ - b)
      (codimension_pos κ hκ8).le (sub_pos.mpr hb).le v)
  apply integral_drift_of_balance v.coe_nonneg (by positivity) (by positivity) hlow hhigh
    (radiusMoment_balance a hε hεlim hε0 hB hBm hBc hB0 hκ hκ8 b hb0 hb)
  filter_upwards [hh.prod_right_ae, ae_restrict_mem measurableSet_Ioc] with s hsi hs
  have hm := limitRadiusKernel_green_mean (a ⟨s, hs.1.le⟩) (a v) hε hεlim (fun n => (hε0 n).le)
    hB hBm hBc hB0 hκ hκ8 hz hs.1.le hs.2
  have hj := limitRadiusKernel_inverse_moment_jensen (a v) hε hBm (codimension κ)
    (greenExponent κ) b s (initialGreen κ z) (codimension_pos κ hκ8).le
    (greenExponent_pos κ hκ hκ8).le hb0 hb.le hI hm hsi
  simpa only [radiusMoment, sub_add_eq_sub_sub] using hj

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

 
noncomputable def stoppedInverseAngle (κ : ℝ) (B : ℝ≥0 → ℝ) (γ : ℝ≥0 → ℂ)
    (G : ℝ≥0 → ℂ → ℂ) (z : ℂ) (u b : ℝ) : ℝ :=
  (stoppedAngleSq κ B γ G z u) ^ (-b / 2)

lemma finiteCenteredLaw_inverseAngle_moment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
    (hB : IsBrownianReal B P)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω))
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness
      (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω))
    (z : ℂ) (hz : z ∈ upperHalfPlane) (u : ℝ≥0) (hu : 0 ≤ (u : ℝ))
    {ε : ℕ → ℝ} (a : ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0))
    (b : ℝ) (hb : b ≤ greenExponent κ) :
    Integrable (fun ω => stoppedInverseAngle κ (fun t => B t ω) (γ ω) (G ω) z u b)
      (finiteCenteredLaw P κ B γ G z u) ∧
    (∫ ω, stoppedInverseAngle κ (fun t => B t ω) (γ ω) (G ω) z u b
      ∂finiteCenteredLaw P κ B γ G z u) = radiusMoment P a b u := by
  let w (ω : Ω) := stoppedGreen κ (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) z u
  let f (ω : Ω) := stoppedInverseAngle κ (fun t => B t ω) (γ ω) (G ω) z u b
  let d (ω : Ω) := ENNReal.ofReal (w ω / initialGreen κ z)
  have hwi := (finite_stopped_green_of_witness hB κ hκ hκ8 γ G F hw z hz u hu).1
  have hd : AEMeasurable d P := (hwi.div_const _).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hid : Integrable (limitRadiusKernel a (codimension κ) (greenExponent κ - b) u) P :=
    limitRadiusKernel_integrable a hε hBm _ _ (codimension_pos κ hκ8).le (sub_nonneg.mpr hb) u
  have he : (fun ω => (d ω).toReal • f ω) =ᵐ[P]
      (fun ω => limitRadiusKernel a (codimension κ) (greenExponent κ - b) u ω / initialGreen κ z) := by
    filter_upwards [hw] with ω hω
    have hw0 := stoppedGreen_nonneg hω κ z u
    rw [show (d ω).toReal = w ω / initialGreen κ z from
      ENNReal.toReal_ofReal (div_nonneg hw0 (initialGreen_pos κ z hz).le), smul_eq_mul]
    rw [limitRadiusKernel_inverse_factor,
      limitRadiusKernel_eq_stoppedGreen a hε hεlim hBc hz hu ω (γ ω) (G ω) (F ω) hω,
      limitRadiusKernel_eq_stoppedAngleSq a hε hεlim hBc hz hu ω (γ ω) (G ω) (F ω) hω]
    · change w ω / initialGreen κ z * f ω = w ω * f ω / initialGreen κ z
      ring
    · exact hε
  constructor
  · apply (integrable_withDensity_iff_integrable_smul₀' hd
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mpr
    exact (hid.div_const _).congr he.symm
  · change (∫ ω, f ω ∂P.withDensity d) = _
    rw [integral_withDensity_eq_integral_toReal_smul₀ hd
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), integral_congr_ae he, integral_div]
    rfl

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {u : ℝ} {ε : ℕ → ℝ}

lemma limitRadiusKernel_zero_eq_indicator_level
    (a : ∀ n, AngularLocalization B hm κ z u (ε n)) (hε : Antitone ε)
    (hεlim : Tendsto ε atTop (𝓝 0))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hz : z ∈ upperHalfPlane)
    (hu : 0 ≤ u) (ω : Ω) (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) γ G F) (p : ℝ) :
    limitRadiusKernel a p 0 u ω =
      if radiusLevelTime γ G z u < ∞ then Real.exp (p * (u - Real.log 2 - Real.log z.im)) else 0 := by
  by_cases hh : ∃ T : ℝ≥0, z ∈ survivingDomain γ T ∧ fullRadius G T z = (2 * z.im) * Real.exp (-u)
  · obtain ⟨T, hT, hR⟩ := hh
    rw [limitRadiusKernel_eq_stopped_of_live_level a hε hεlim hBc hz hu ω γ G F hw T hT hR,
      radiusLevelTime_eq_of_live_level ((hBc ω).const_mul _) hw z u T hT hR, ite_eq_left ENNReal.coe_lt_top,
      powerLogDensity_radius_angle κ p 0 (Real.log z.im), zero_div, Real.rpow_zero, mul_one,
      (fullRadius_level_iff_logClock ((hBc ω).const_mul _) hw z T hT u).mp hR]
  · rw [limitRadiusKernel_eq_zero_of_no_level a hBc hz ω γ G F hw _ _ hh,
      radiusLevelTime_eq_top_of_no_level γ G z u hh, ite_eq_right (lt_irrefl _)]

lemma integral_limitRadiusKernel_zero_eq_probability
    (a : ∀ n, AngularLocalization B hm κ z u (ε n)) (hε : Antitone ε)
    (hεlim : Tendsto ε atTop (𝓝 0))
    {P : Measure Ω} [IsFiniteMeasure P]
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hz : z ∈ upperHalfPlane)
    (hu : 0 ≤ u) (γ : Ω → ℝ≥0 → ℂ) (G F : Ω → ℝ≥0 → ℂ → ℂ)
    (hw : ∀ᵐ ω ∂P, IsCapacityTwoWitness (fun t => Real.sqrt κ * B t ω) (γ ω) (G ω) (F ω)) (p : ℝ) :
    (∫ ω, limitRadiusKernel a p 0 u ω ∂P) =
      Real.exp (p * (u - Real.log 2 - Real.log z.im)) *
        (P {ω | radiusLevelTime (γ ω) (G ω) z u < ∞}).toReal := by
  let K := Real.exp (p * (u - Real.log 2 - Real.log z.im))
  let A := {ω | limitRadiusKernel a p 0 u ω ≠ 0}
  have hAm : MeasurableSet A := (measurableSet_eq_fun
    ((limitRadiusKernel_measurable a hε hBm p 0).comp (measurable_const.prodMk measurable_id)) measurable_const).compl
  have hA : A =ᵐ[P] {ω | radiusLevelTime (γ ω) (G ω) z u < ∞} := by
    filter_upwards [hw] with ω hω
    change (limitRadiusKernel a p 0 u ω ≠ 0) = (radiusLevelTime (γ ω) (G ω) z u < ∞)
    rw [limitRadiusKernel_zero_eq_indicator_level a hε hεlim hBc hz hu ω (γ ω) (G ω) (F ω) hω p]
    split_ifs with h <;> simp [h, Real.exp_ne_zero]
  have he : limitRadiusKernel a p 0 u = A.indicator (fun _ => K) := by
    funext ω
    rw [Set.indicator_apply]
    change limitRadiusKernel a p 0 u ω = if limitRadiusKernel a p 0 u ω ≠ 0 then K else 0
    simp only [limitRadiusKernel_zero, max_eq_left hu]
    split_ifs <;> simp_all [Real.exp_ne_zero, K]
  rw [he, integral_indicator hAm, setIntegral_const, smul_eq_mul, mul_comm]
  change K * (P A).toReal = _
  rw [measure_congr hA]

lemma initialGreen_div_zeroKernel (κ u : ℝ) (z : ℂ) (hz : z ∈ upperHalfPlane) :
    initialGreen κ z / Real.exp (codimension κ * (u - Real.log 2 - Real.log z.im)) =
      Real.exp (-codimension κ * u) * (Real.sin (Complex.arg z)) ^ greenExponent κ := by
  have hr : 0 < 2 * z.im := mul_pos (by norm_num) hz
  rw [initialGreen, Real.rpow_def_of_pos hr, Real.log_mul (by norm_num) (ne_of_gt hz)]
  rw [mul_comm (Real.exp _) ((Real.sin (Complex.arg z)) ^ greenExponent κ),
    mul_div_assoc, ← Real.exp_sub]
  rw [show (Real.log 2 + Real.log z.im) * -codimension κ -
    codimension κ * (u - Real.log 2 - Real.log z.im) = -codimension κ * u by ring]
  ring

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory
open scoped Topology
namespace SLEExactGauge

 

lemma liminf_slope_of_integral_bound {F G : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hG : ContinuousOn G (Icc a b))
    (hinc : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t →
      F t - F s ≤ ∫ u in s..t, G u) :
    ∀ x ∈ Ico a b, ∀ r, G x < r → ∃ᶠ z in 𝓝[>] x, slope F x z < r := by
  let g (t : ℝ) := G (projIcc a b hab t)
  have hgc : Continuous g := hG.comp_continuous
    (continuous_subtype_val.comp continuous_projIcc) (fun t => (projIcc a b hab t).property)
  have he (t : ℝ) (ht : t ∈ Icc a b) : g t = G t := by
    simp only [g, projIcc_of_mem hab ht]
  intro x hx r hr
  have hd : HasDerivAt (fun z => ∫ u in a..z, g u) (g x) x :=
    intervalIntegral.integral_hasDerivAt_right (hgc.intervalIntegrable _ _)
      hgc.stronglyMeasurable.stronglyMeasurableAtFilter hgc.continuousAt
  have hs := (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl x)).1
    (hd.hasDerivWithinAt : HasDerivWithinAt (fun z => ∫ u in a..z, g u) (g x) (Ioi x) x)
  have hsl : ∀ᶠ z in 𝓝[>] x, slope (fun y => ∫ u in a..y, g u) x z < r :=
    hs (Iio_mem_nhds (by rw [he x ⟨hx.1, hx.2.le⟩]; exact hr))
  apply Filter.Eventually.frequently
  filter_upwards [hsl, Ioc_mem_nhdsGT hx.2] with z hz hzI
  apply lt_of_le_of_lt _ hz
  rw [slope_def_field, slope_def_field,
    intervalIntegral.integral_interval_sub_left (hgc.intervalIntegrable a z) (hgc.intervalIntegrable a x)]
  apply div_le_div_of_nonneg_right _ (sub_pos.mpr hzI.1).le
  rw [intervalIntegral.integral_congr (fun t ht => he t (by
    have ht' : t ∈ Icc x z := by simpa only [uIcc_of_le hzI.1.le] using ht
    exact ⟨hx.1.trans ht'.1, ht'.2.trans hzI.2⟩))]
  exact hinc x ⟨hx.1, hx.2.le⟩ z ⟨hx.1.trans hzI.1.le, hzI.2⟩ hzI.1.le

lemma image_le_of_integral_drift {F G H H' : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hF : ContinuousOn F (Icc a b)) (hG : ContinuousOn G (Icc a b))
    (hinc : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t → F t - F s ≤ ∫ u in s..t, G u)
    (ha : F a ≤ H a) (hH : ContinuousOn H (Icc a b))
    (hH' : ∀ x ∈ Ico a b, HasDerivWithinAt H (H' x) (Ici x) x)
    (hbound : ∀ x ∈ Ico a b, F x = H x → G x < H' x) :
    ∀ x ∈ Icc a b, F x ≤ H x := by
  exact fun x hx => image_le_of_liminf_slope_right_lt_deriv_boundary' hF
    (liminf_slope_of_integral_bound hab hG hinc) ha hH hH' hbound hx

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory
open scoped Topology
namespace SLEExactGauge

noncomputable def lyapunovBarrier (r K δ t : ℝ) : ℝ := K ^ r * (t + δ) ^ (-r)

lemma lyapunovBarrier_pos {r K δ t : ℝ} (hK : 0 < K) (ht : 0 < t + δ) :
    0 < lyapunovBarrier r K δ t := mul_pos (Real.rpow_pos_of_pos hK _) (Real.rpow_pos_of_pos ht _)

lemma lyapunovBarrier_deriv {r K δ t : ℝ} (ht : 0 < t + δ) :
    HasDerivAt (lyapunovBarrier r K δ) (-r * lyapunovBarrier r K δ t / (t + δ)) t := by
  have hd := (((hasDerivAt_id t).add_const δ).rpow_const (p := -r) (Or.inl ht.ne')).const_mul (K ^ r)
  convert hd using 1 <;> try rfl
  dsimp only [lyapunovBarrier, id_eq]
  rw [Real.rpow_sub ht, Real.rpow_one]
  ring

lemma lyapunovBarrier_power {r K δ t : ℝ} (hr : 0 < r) (hK : 0 < K) (ht : 0 < t + δ) :
    (lyapunovBarrier r K δ t) ^ (1 + 1 / r) =
      lyapunovBarrier r K δ t * K / (t + δ) := by
  have he : lyapunovBarrier r K δ t = (K / (t + δ)) ^ r := by
    rw [Real.div_rpow hK.le ht.le, lyapunovBarrier, Real.rpow_neg ht.le]
    rfl
  rw [he, ← Real.rpow_mul (div_pos hK ht).le]
  have hf : r * (1 + 1 / r) = r + 1 := by field_simp
  rw [hf, Real.rpow_add (div_pos hK ht), Real.rpow_one]
  ring

lemma exists_small_barrier {r K C : ℝ} (hr : 0 < r) (hK : 0 < K) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ C ≤ lyapunovBarrier r K δ 0 := by
  have ht : Tendsto (fun δ : ℝ => K ^ r * δ ^ (-r)) (𝓝[>] (0 : ℝ)) atTop :=
    (tendsto_rpow_neg_nhdsGT_zero (neg_neg_of_pos hr)).const_mul_atTop (Real.rpow_pos_of_pos hK r)
  have he := (ht.eventually_ge_atTop C).and (Ioc_mem_nhdsGT (by norm_num : (0 : ℝ) < 1))
  obtain ⟨δ, hd, hδ⟩ := he.exists
  exact ⟨δ, hδ.1, hδ.2, by simpa only [lyapunovBarrier, zero_add] using hd⟩

 

theorem comingDown_one_window {F : ℝ → ℝ} {v A C r : ℝ}
    (hv : 0 ≤ v) (hv1 : v ≤ 1) (hA : 0 ≤ A) (hC : 0 < C) (hr : 0 < r)
    (hF : ContinuousOn F (Icc 0 v))
    (hinc : ∀ s ∈ Icc 0 v, ∀ t ∈ Icc 0 v, s ≤ t →
      F t - F s ≤ ∫ u in s..t, A * F u - C * (F u) ^ (1 + 1 / r)) :
    ∀ t ∈ Ioc 0 v, F t ≤ ((2 * A + r + 1) / C / t) ^ r := by
  let K := (2 * A + r + 1) / C
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨δ, hδ, hδ1, hinit⟩ := exists_small_barrier (C := F 0) hr hK
  have hcont : ContinuousOn (lyapunovBarrier r K δ) (Icc 0 v) := by
    intro t ht
    exact (lyapunovBarrier_deriv (r := r) (K := K) (by linarith [ht.1] : 0 < t + δ)).continuousAt.continuousWithinAt
  have hq : 0 ≤ 1 + 1 / r := by positivity
  have hgc : ContinuousOn (fun u => A * F u - C * (F u) ^ (1 + 1 / r)) (Icc 0 v) :=
    (continuousOn_const.mul hF).sub (continuousOn_const.mul ((Real.continuous_rpow_const hq).comp_continuousOn hF))
  have hfence : ∀ t ∈ Icc 0 v, F t ≤ lyapunovBarrier r K δ t := by
    apply image_le_of_integral_drift hv hF hgc hinc hinit hcont
      (fun t ht => (lyapunovBarrier_deriv (r := r) (K := K) (by linarith [ht.1] : 0 < t + δ)).hasDerivWithinAt)
    intro t ht he
    have htδ : 0 < t + δ := by linarith [ht.1]
    have hH : 0 < lyapunovBarrier r K δ t := lyapunovBarrier_pos hK htδ
    rw [he, lyapunovBarrier_power hr hK htδ]
    apply (lt_div_iff₀ htδ).mpr
    have ht2 : t + δ ≤ 2 := by linarith [ht.2]
    have hk : C * K = 2 * A + r + 1 := by dsimp [K]; field_simp
    have htA : A * (t + δ) ≤ 2 * A := by nlinarith
    have hx : A * (t + δ) - C * K < -r := by linarith
    have hm := mul_lt_mul_of_pos_left hx hH
    field_simp at *
    nlinarith
  intro t ht
  apply (hfence t ⟨ht.1.le, ht.2⟩).trans
  have htδ : 0 < t + δ := by linarith [ht.1]
  have he : lyapunovBarrier r K δ t = (K / (t + δ)) ^ r := by
    rw [Real.div_rpow hK.le htδ.le, lyapunovBarrier, Real.rpow_neg htδ.le]
    rfl
  rw [he]
  exact Real.rpow_le_rpow (div_nonneg hK.le htδ.le)
    (div_le_div_of_nonneg_left hK.le ht.1 (by linarith)) hr.le

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory
open scoped Topology
namespace SLEExactGauge

lemma comingDown_shifted {F : ℝ → ℝ} {v A C r : ℝ}
    (_hv : 0 ≤ v) (hA : 0 ≤ A) (hC : 0 < C) (hr : 0 < r)
    (hF : ContinuousOn F (Icc 0 v))
    (hinc : ∀ s ∈ Icc 0 v, ∀ t ∈ Icc 0 v, s ≤ t →
      F t - F s ≤ ∫ u in s..t, A * F u - C * (F u) ^ (1 + 1 / r))
    {x ℓ : ℝ} (hx : 0 ≤ x) (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (hxℓ : x + ℓ ≤ v) :
    F (x + ℓ) ≤ ((2 * A + r + 1) / C / ℓ) ^ r := by
  have hmap : MapsTo (fun s : ℝ => x + s) (Icc 0 ℓ) (Icc 0 v) := by
    intro s hs
    constructor <;> linarith [hs.1, hs.2]
  have hcont : ContinuousOn (fun s => F (x + s)) (Icc 0 ℓ) :=
    hF.comp (continuous_const.add continuous_id).continuousOn hmap
  apply comingDown_one_window hℓ.le hℓ1 hA hC hr hcont ?_ ℓ ⟨hℓ, le_rfl⟩
  intro s hs t ht hst
  rw [intervalIntegral.integral_comp_add_left (fun u => A * F u - C * F u ^ (1 + 1 / r)) x]
  exact hinc _ (hmap hs) _ (hmap ht) (by linarith)

 

theorem comingDown_uniform {F : ℝ → ℝ} {v A C r η : ℝ}
    (hv : 0 ≤ v) (hA : 0 ≤ A) (hC : 0 < C) (hr : 0 < r)
    (hF : ContinuousOn F (Icc 0 v))
    (hinc : ∀ s ∈ Icc 0 v, ∀ t ∈ Icc 0 v, s ≤ t →
      F t - F s ≤ ∫ u in s..t, A * F u - C * (F u) ^ (1 + 1 / r))
    (hη : 0 < η) (hη1 : η ≤ 1) :
    ∀ t ∈ Icc η v, F t ≤ ((2 * A + r + 1) / C / η) ^ r := by
  intro t ht
  have hh := comingDown_shifted hv hA hC hr hF hinc (x := t - η) (sub_nonneg.mpr ht.1) hη hη1
    (by linarith [ht.2] : t - η + η ≤ v)
  simpa only [sub_add_cancel] using hh

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

noncomputable def lyapunovA (κ b : ℝ) : ℝ := (κ * b / 8) * (1 + (greenExponent κ - b))
noncomputable def lyapunovC (κ b : ℝ) : ℝ := (κ * b / 8) * (greenExponent κ - b)
noncomputable def angularMomentBound (κ b η : ℝ) : ℝ :=
  ((2 * lyapunovA κ b + b / 2 + 1) / lyapunovC κ b / η) ^ (b / 2)

lemma lyapunovA_nonneg {κ b : ℝ} (hκ : 0 < κ) (hb0 : 0 < b) (hb : b < greenExponent κ) :
    0 ≤ lyapunovA κ b := by dsimp [lyapunovA]; positivity
lemma lyapunovC_pos {κ b : ℝ} (hκ : 0 < κ) (hb0 : 0 < b) (hb : b < greenExponent κ) :
    0 < lyapunovC κ b := by dsimp [lyapunovC]; positivity
lemma angularMomentBound_pos {κ b η : ℝ} (hκ : 0 < κ) (hb0 : 0 < b)
    (hb : b < greenExponent κ) (hη : 0 < η) : 0 < angularMomentBound κ b η := by
  have hA := lyapunovA_nonneg hκ hb0 hb
  have hC := lyapunovC_pos hκ hb0 hb
  dsimp only [angularMomentBound]
  apply Real.rpow_pos_of_pos
  positivity

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {v : ℝ≥0} {ε : ℕ → ℝ}

 

theorem radiusMoment_bound
    (a : ∀ u : ℝ≥0, ∀ n, AngularLocalization B hm κ z u (ε n))
    (hε : Antitone ε) (hεlim : Tendsto ε atTop (𝓝 0)) (hε0 : ∀ n, 0 < ε n)
    {P : Measure Ω} (hB : IsBrownianReal B P)
    (hBm : Measurable (fun q : ℝ≥0 × Ω => B q.1 q.2))
    (hBc : ∀ ω, Continuous (fun t => B t ω)) (hB0 : ∀ ω, B 0 ω = 0)
    (hκ : 0 < κ) (hκ8 : κ < 8) (hz : z ∈ upperHalfPlane)
    (b : ℝ) (hb0 : 0 < b) (hb : b < greenExponent κ)
    (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) :
    ∀ t ∈ Icc η (v : ℝ), radiusMoment P (a v) b t ≤ angularMomentBound κ b η := by
  obtain ⟨hc, hd⟩ := radiusMoment_drift a hε hεlim hε0 hB hBm hBc hB0 hκ hκ8 hz b hb0 hb (v := v)
  have he : 1 + 1 / (b / 2) = 1 + 2 / b := by field_simp
  apply comingDown_uniform v.coe_nonneg (lyapunovA_nonneg hκ hb0 hb) (lyapunovC_pos hκ hb0 hb)
    (by positivity : 0 < b / 2) hc ?_ hη hη1
  simpa only [he, lyapunovA, lyapunovC] using hd

end SLEExactGauge
end

 
section

open Set Filter MeasureTheory ProbabilityTheory Classical
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
  {B : ℝ≥0 → Ω → ℝ} {hm : ∀ t, Measurable (B t)}
  {κ : ℝ} {z : ℂ} {v : ℝ} {ε : ℕ → ℝ}

lemma limitRadiusKernel_antitone_power
    (c : ∀ n, AngularLocalization B hm κ z v (ε n)) (hε : Antitone ε)
    (p α β s : ℝ) (hαβ : α ≤ β) (ω : Ω) :
    limitRadiusKernel c p β s ω ≤ limitRadiusKernel c p α s ω := by
  have he := limitRadiusKernel_power_factor c hε p α (β - α) s ω
  rw [show α + (β - α) = β by ring] at he
  rw [he]
  apply mul_le_of_le_one_right (limitRadiusKernel_nonneg c p α s ω)
  exact Real.rpow_le_one (limitRadiusKernel_nonneg c 0 2 s ω)
    (limitRadiusKernel_angle_le_one c s ω) (by linarith)

lemma integral_limitRadiusKernel_antitone_power
    (c : ∀ n, AngularLocalization B hm κ z v (ε n)) (hε : Antitone ε)
    {P : Measure Ω} (p α β s : ℝ) (hαβ : α ≤ β)
    (hiα : Integrable (limitRadiusKernel c p α s) P)
    (hiβ : Integrable (limitRadiusKernel c p β s) P) :
    (∫ ω, limitRadiusKernel c p β s ω ∂P) ≤ ∫ ω, limitRadiusKernel c p α s ω ∂P :=
  integral_mono hiβ hiα (limitRadiusKernel_antitone_power c hε p α β s hαβ)

end SLEExactGauge
end

 
end

end OAI

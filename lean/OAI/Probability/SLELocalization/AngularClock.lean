import Mathlib
import OAI.Probability.SLELocalization.AngularMoments
import OAI.Probability.SLE.ClippedCoordinates
import OAI.Probability.SLE.IntegralLimits
import OAI.Probability.SLE.ItoIsometry
import OAI.Probability.SLE.StochasticIntegrals

namespace OAI


/-! Conformal localization and Gamma Field estimates. -/

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.GammaField
open LoewnerCutoff LoewnerField LoewnerExit AngularBarrier
variable {ε T : ℝ} (hε : 0 < ε) (hT : 0 ≤ T)

lemma field_nonneg {l b η : ℝ} (hl : 0 < l) (hb : 0 < b) (hη : 0 < η)
    (ρ sdev : ℝ) (U : C(I, ℝ)) (z : ℂ) (t x : ℝ) :
    0 ≤ field hε hT l b η ρ sdev U z t x :=
  AngularBarrier.value_nonneg hl hb (remaining_pos hε hT hη ρ U z t)
    (squaredSine_pos _).le

lemma field_initial {z : ℂ} (hy : ε ≤ z.im) {u : ℝ} (hu : 0 ≤ u)
    (l b η sdev : ℝ) (U : C(I, ℝ)) :
    field hε hT l b η ((2*z.im)*Real.exp (-u)) sdev U z 0 0 = profile l b (η+u) (z.re/z.im) := by
  have hz : 0 < z.im := hε.trans_le hy
  simp only [field, remaining, rawRemaining, angleRatio, height, position_initial,
    logDerivative_initial, mul_zero, sub_zero, max_eq_right hy]
  rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]
  have he : η + Real.log (2*z.im) - (Real.log (2*z.im) + -u) = η+u := by ring
  rw [he, max_eq_right (by linarith)]

lemma measurable_stop (hTp : 0 < T) (z : ℂ) (ρ δ : ℝ) :
    @Measurable C(I, ℝ) ℝ (borel _) _ (fun U => stop hε hT U z ρ δ) := by
  let : MeasurableSpace C(I, ℝ) := borel _
  let : BorelSpace C(I, ℝ) := ⟨rfl⟩
  apply measurable_of_Ioi
  intro a
  by_cases ha : a < 0
  · have he : (fun U => stop hε hT U z ρ δ) ⁻¹' Ioi a = univ := by
      ext U; simp only [mem_preimage, mem_Ioi, mem_univ, iff_true]
      exact ha.trans_le (stop_bounds hε hT U z ρ δ).1
    rw [he]; exact MeasurableSet.univ
  · by_cases hat : a < T
    · have he : (fun U => stop hε hT U z ρ δ) ⁻¹' Ioi a =
        {U | ∀ s ∈ Icc 0 a, 0 < deficit hε hT U z ρ δ s} := by
        ext U; exact lt_stop_iff hε hT hTp U z ρ δ ⟨not_lt.1 ha,hat⟩
      rw [he]; exact (isOpen_positive_on hε hT z ρ δ a).measurableSet
    · have he : (fun U => stop hε hT U z ρ δ) ⁻¹' Ioi a = ∅ := by
        ext U; simp only [mem_preimage, mem_Ioi, mem_empty_iff_false, iff_false]
        exact not_lt_of_ge ((stop_bounds hε hT U z ρ δ).2.trans (not_lt.1 hat))
      rw [he]; exact MeasurableSet.empty

lemma integral_drift_nonpos {κ η ρ : ℝ} (hκ : 0 < κ ∧ κ < 8) (hη : 0 < η) (_hρ : 0 < ρ)
    (hTp : 0 < T) (U : C(I, ℝ)) (z : ℂ) (δ : ℝ) (B : ℝ → ℝ) (hB : Continuous B)
    (hU : ∀ s ∈ Icc 0 T, extendDriver T U s = Real.sqrt κ*B s) :
    (∫ t in (0:ℝ)..(stop hε hT U z ρ δ), drift hε hT (κ/2) ((8/κ-1)/2) η ρ (Real.sqrt κ) U z t (B t)) +
    (1/2:ℝ)*∫ t in (0:ℝ)..(stop hε hT U z ρ δ),
      iteratedDeriv 2 (field hε hT (κ/2) ((8/κ-1)/2) η ρ (Real.sqrt κ) U z t) (B t) ≤ 0 := by
  have hl : 0 < κ/2 := div_pos hκ.1 (by norm_num)
  have hb : 0 < (8/κ-1)/2 := by
    have hh : 1 < 8/κ := (lt_div_iff₀ hκ.1).2 (by simpa using hκ.2)
    linarith
  have htau := (stop_bounds hε hT U z ρ δ).1
  have hm : Continuous (fun t : ℝ => ((U,t),B t)) :=
    (continuous_const.prodMk continuous_id).prodMk hB
  have hv := ((continuous_drift hε hT hl hb hη ρ (Real.sqrt κ) z).comp hm).continuousOn (s := Icc 0 (stop hε hT U z ρ δ))
  have hc := ((continuous_derivative hε hT hl hb hη ρ (Real.sqrt κ) z 2).comp hm).continuousOn (s := Icc 0 (stop hε hT U z ρ δ))
  have hiV := hv.intervalIntegrable_of_Icc (μ:=volume) htau
  have hiC := hc.intervalIntegrable_of_Icc (μ:=volume) htau
  dsimp only [Function.comp_def] at hiV hiC
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add hiV (hiC.const_mul (1/2:ℝ))]
  rw [intervalIntegral.integral_of_le htau]
  apply integral_nonpos_of_ae
  have hne : ∀ᵐ t : ℝ ∂volume, t ≠ stop hε hT U z ρ δ := by simp [ae_iff]
  filter_upwards [ae_restrict_mem measurableSet_Ioc,
    ae_restrict_of_ae hne] with t ht he
  have hlt : t < stop hε hT U z ρ δ := lt_of_le_of_ne ht.2 he
  have hh := (deficit_pos_iff hε hT U z ρ δ t).1
    (positive_before hε hT hTp U z ρ δ ht.1.le hlt)
  exact drift_nonpos hε hT hκ hη ρ U z t (B t) hh.2.1.le
    (hU t ⟨ht.1.le,ht.2.trans (stop_bounds hε hT U z ρ δ).2⟩)

end SLEExactGauge.GammaField

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.FiniteTilt.Cutoff
open LoewnerCutoff LoewnerExit LoewnerField LoewnerLocalized GammaField AngularBarrier
variable {z : ℂ} {u : ℝ} (C : Cutoff z u)
variable {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (sample : Ω)
variable {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}
variable (h : IsLoewnerTraceUsing (fun t => Real.sqrt κ*B t.toNNReal sample) γ g f)
variable (hz : z ∈ halfPlane) (hu : 0 < u)
variable (hc : Continuous (fun t => B t sample)) (hb0 : B 0 sample = 0)
include h hz hu hc hb0

lemma remaining_upper (η : ℝ) {t : ℝ} (ht : t ∈ Icc 0 (C.stopTime κ B sample)) :
    remaining C.height_pos C.horizon.coe_nonneg η ((2*z.im)*Real.exp (-u)) (C.paths κ B sample) z t ≤ η+u := by
  have h0 := C.initial_deficit_brownian κ B sample hz hu hc hb0
  have hh := ((deficit_nonneg_iff C.height_pos C.horizon.coe_nonneg _ z _ C.angle t).1
    (nonneg_until C.height_pos C.horizon.coe_nonneg C.horizon_pos _ z _ C.angle h0 ht)).2.1
  have hrad := radius_eq_source C.height_pos C.horizon_pos h
    ((continuous_const.mul (hc.comp continuous_real_toNNReal)).continuousOn) _ z _ C.angle
    (C.path_eq κ B sample hc) h0 ht
  have ha := (h.log_radius_strictAnti (C.bounds κ B sample).1
    ((continuous_const.mul (hc.comp continuous_real_toNNReal)).continuousOn)
    (C.source_live κ B sample h hz hu hc hb0)).antitoneOn
    (show (0:ℝ) ∈ Icc 0 (C.stopTime κ B sample) from ⟨le_rfl,(C.bounds κ B sample).1⟩) ht ht.1
  rw [h.radius_initial hz] at ha
  unfold remaining
  apply max_le (by linarith)
  rw [rawRemaining_eq C.height_pos C.horizon.coe_nonneg η _ _ z t hh, hrad,
    Real.log_mul (by have hy : 0 < z.im := hz; positivity) (Real.exp_pos _).ne', Real.log_exp]
  linarith

omit h in
lemma ratio_upper {t : ℝ} (ht : t ∈ Icc 0 (C.stopTime κ B sample)) :
    |angleRatio C.height_pos C.horizon.coe_nonneg (Real.sqrt κ) (C.paths κ B sample) z t (B t.toNNReal sample)| ≤ 1/C.angle := by
  have h0 := C.initial_deficit_brownian κ B sample hz hu hc hb0
  have hh := (deficit_nonneg_iff C.height_pos C.horizon.coe_nonneg _ z _ C.angle t).1
    (nonneg_until C.height_pos C.horizon.coe_nonneg C.horizon_pos _ z _ C.angle h0 ht)
  exact ratio_bound C.height_pos C.horizon.coe_nonneg C.angle_pos _ _ z t _ hh.2.1 hh.2.2
    (C.path_eq κ B sample hc ⟨ht.1,ht.2.trans (C.bounds κ B sample).2⟩)

end SLEExactGauge.FiniteTilt.Cutoff

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.GammaField
open LoewnerCutoff LoewnerExit AngularBarrier

def pathTerminal {ε : ℝ} (hε : 0 < ε) (T : ℝ≥0)
    (l b η ρ δ sdev : ℝ) (z : ℂ) (U : C(I, ℝ)) : ℝ :=
  let tau := stop hε T.coe_nonneg U z ρ δ
  field hε T.coe_nonneg l b η ρ sdev U z tau (extendDriver T U tau/sdev)

lemma continuous_actualField {ε : ℝ} (hε : 0 < ε) (T : ℝ≥0)
    {l b η : ℝ} (hl : 0 < l) (hb : 0 < b) (hη : 0 < η) (ρ sdev : ℝ) (z : ℂ) :
    Continuous (fun v : C(I, ℝ) × ℝ =>
      field hε T.coe_nonneg l b η ρ sdev v.1 z v.2 (extendDriver T v.1 v.2/sdev)) := by
  have hp : Continuous (fun v : C(I, ℝ) × ℝ => (v,extendDriver T v.1 v.2/sdev)) :=
    continuous_id.prodMk ((continuous_joint_extendDriver T).div_const sdev)
  have hh := Continuous.comp (g := fun v : (C(I, ℝ) × ℝ) × ℝ =>
    field hε T.coe_nonneg l b η ρ sdev v.1.1 z v.1.2 v.2)
    (f := fun v : C(I, ℝ) × ℝ => (v,extendDriver T v.1 v.2/sdev))
    (continuous_field hε T.coe_nonneg hl hb hη ρ sdev z) hp
  dsimp only [Function.comp_def] at hh
  exact hh

lemma pathTerminal_measurable {ε : ℝ} (hε : 0 < ε) (T : ℝ≥0) (hT : 0 < (T:ℝ))
    {l b η : ℝ} (hl : 0 < l) (hb : 0 < b) (hη : 0 < η) (ρ δ sdev : ℝ) (z : ℂ) :
    @Measurable C(I, ℝ) ℝ (borel _) _ (pathTerminal hε T l b η ρ δ sdev z) := by
  let : MeasurableSpace C(I, ℝ) := borel _
  let : BorelSpace C(I, ℝ) := ⟨rfl⟩
  have hτ : Measurable (fun U : C(I, ℝ) => stop hε T.coe_nonneg U z ρ δ) :=
    measurable_stop hε T.coe_nonneg hT z ρ δ
  have hm : Measurable (fun U : C(I, ℝ) => (U,stop hε T.coe_nonneg U z ρ δ)) :=
    measurable_id.prodMk hτ
  have hh := (continuous_actualField hε T hl hb hη ρ sdev z).measurable.comp hm
  dsimp only [Function.comp_def] at hh
  exact hh

lemma pathTerminal_eq {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (sample : Ω)
    (hc : Continuous (fun t => B t sample)) {ε : ℝ} (hε : 0 < ε) (T : ℝ≥0)
    (l b η ρ δ sdev : ℝ) (hsdev : sdev ≠ 0) (z : ℂ) :
    let U := BrownianDriver.path B sdev T sample
    let tau := stop hε T.coe_nonneg U z ρ δ
    pathTerminal hε T l b η ρ δ sdev z U =
      field hε T.coe_nonneg l b η ρ sdev U z tau (B tau.toNNReal sample) := by
  dsimp only [pathTerminal]
  congr 1
  rw [BrownianDriver.extend_eq B sdev T sample hc (stop_bounds hε T.coe_nonneg _ z ρ δ),
    mul_div_cancel_left₀ _ hsdev]

lemma terminal_aemeasurable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    {ε : ℝ} (hε : 0 < ε) (T : ℝ≥0) (hT : 0 < (T:ℝ))
    {l b η : ℝ} (hl : 0 < l) (hb : 0 < b) (hη : 0 < η) (ρ δ sdev : ℝ) (hsdev : sdev ≠ 0) (z : ℂ) :
    let U := BrownianDriver.path B sdev T
    let τ := fun sample => stop hε T.coe_nonneg (U sample) z ρ δ
    AEMeasurable (fun sample => field hε T.coe_nonneg l b η ρ sdev (U sample) z (τ sample)
      (B (τ sample).toNNReal sample)) P := by
  let : MeasurableSpace C(I, ℝ) := borel _
  have hm := (pathTerminal_measurable hε T hT hl hb hη ρ δ sdev z).comp_aemeasurable
    (BrownianDriver.path_aemeasurable hB sdev T)
  apply hm.congr
  filter_upwards [hB.cont] with sample hc
  exact pathTerminal_eq B sample hc hε T l b η ρ δ sdev hsdev z

end SLEExactGauge.GammaField

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.FiniteTilt.Cutoff
open GammaField
variable {z : ℂ} {u : ℝ} (C : Cutoff z u)

def barrier {Ω : Type*} (η κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (sample : Ω) : ℝ :=
  field C.height_pos C.horizon.coe_nonneg (κ/2) ((8/κ-1)/2) η ((2*z.im)*Real.exp (-u)) (Real.sqrt κ)
    (C.paths κ B sample) z (C.stopTime κ B sample) (B (C.stopTime κ B sample).toNNReal sample)

lemma barrier_nonneg {Ω : Type*} (η κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (sample : Ω)
    (hκ : 0 < κ ∧ κ < 8) (hη : 0 < η) : 0 ≤ C.barrier η κ B sample := by
  have hl : 0 < κ/2 := div_pos hκ.1 (by norm_num)
  have hb : 0 < (8/κ-1)/2 := by
    have hh : 1 < 8/κ := (lt_div_iff₀ hκ.1).2 (by simpa using hκ.2)
    linarith
  exact field_nonneg C.height_pos C.horizon.coe_nonneg hl hb hη _ _ _ z _ _

lemma barrier_aemeasurable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (η κ : ℝ)
    (hκ : 0 < κ ∧ κ < 8) (hη : 0 < η) : AEMeasurable (C.barrier η κ B) P := by
  have hl : 0 < κ/2 := div_pos hκ.1 (by norm_num)
  have hb : 0 < (8/κ-1)/2 := by
    have hh : 1 < 8/κ := (lt_div_iff₀ hκ.1).2 (by simpa using hκ.2)
    linarith
  exact terminal_aemeasurable hB C.height_pos C.horizon C.horizon_pos hl hb hη _ _ _
    (Real.sqrt_pos.2 hκ.1).ne' z

end SLEExactGauge.FiniteTilt.Cutoff

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.FiniteTilt.Cutoff
open GammaField GammaPredictable BrownianPredictable BrownianStopped BrownianIto TaylorMeshes
variable {z : ℂ} {u : ℝ} (C : Cutoff z u)

lemma barrier_expectation {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (η κ : ℝ)
    (hκ : 0 < κ ∧ κ < 8) (hη : 0 < η) (hz : z ∈ halfPlane) (hu : 0 < u)
    (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
    (hmaps : ∀ᵐ sample ∂P, IsLoewnerTraceUsing
      (fun t => Real.sqrt κ*B t.toNNReal sample) (γ sample) (g sample) (f sample)) :
    Integrable (C.barrier η κ B) P ∧
      (∫ sample, C.barrier η κ B sample ∂P) ≤ AngularBarrier.profile (κ/2) ((8/κ-1)/2) (η+u) (z.re/z.im) := by
  let l := κ/2
  let b := (8/κ-1)/2
  let ρ := (2*z.im)*Real.exp (-u)
  have hl : 0 < l := div_pos hκ.1 (by norm_num)
  have hb : 0 < b := by
    have hh : 1 < 8/κ := (lt_div_iff₀ hκ.1).2 (by simpa using hκ.2)
    dsimp [b]; linarith
  have hρ : 0 < ρ := by have hy : 0 < z.im := hz; dsimp [ρ]; positivity
  let U := C.paths κ B
  let τ := C.stopTime κ B
  let F := fun sample => field C.height_pos C.horizon.coe_nonneg l b η ρ (Real.sqrt κ) (U sample) z
  let V := fun sample => drift C.height_pos C.horizon.coe_nonneg l b η ρ (Real.sqrt κ) (U sample) z
  let G := AngularBarrier.profile l b (η+u) (z.re/z.im)
  have hreg : ∀ᵐ sample ∂P, BrownianLocal.LocalRegular (F sample) (V sample)
      (fun t => B t.toNNReal sample) (τ sample) := by
    filter_upwards [hB.cont] with sample hc
    exact regular C.height_pos C.horizon.coe_nonneg hl hb hη hρ C.horizon_pos
      (Real.sqrt κ) (U sample) z C.angle _ (hc.comp continuous_real_toNNReal)
  have htau : ∀ᵐ sample ∂P, 0 ≤ τ sample ∧ τ sample ≤ C.horizon :=
    Filter.Eventually.of_forall (fun sample => C.bounds κ B sample)
  obtain ⟨K₁,hK₁,hb₁⟩ := coefficient_bound C.height_pos C.horizon.coe_nonneg hl hb hη
    ρ (Real.sqrt κ) (η+u) (1/C.angle) z 1
  obtain ⟨K₂,hK₂,hb₂⟩ := coefficient_bound C.height_pos C.horizon.coe_nonneg hl hb hη
    ρ (Real.sqrt κ) (η+u) (1/C.angle) z 2
  have hsbound (k : ℕ) (K : ℝ) (hK : 0 ≤ K)
      (hb : ∀ (W : C(I, ℝ)) (t x : ℝ), remaining C.height_pos C.horizon.coe_nonneg η ρ W z t ≤ η+u →
        |angleRatio C.height_pos C.horizon.coe_nonneg (Real.sqrt κ) W z t x| ≤ 1/C.angle →
        |iteratedDeriv k (field C.height_pos C.horizon.coe_nonneg l b η ρ (Real.sqrt κ) W z t) x| ≤ K)
      (n i : ℕ) : ∀ᵐ sample ∂P, |stoppedCoeff k B C.horizon τ F n i sample| ≤ K := by
    filter_upwards [hB.cont,hB.toIsPreBrownianReal.eval_zero_ae_eq_zero,hmaps] with sample hc hb0 hm
    unfold stoppedCoeff
    split_ifs with hh
    · have ht : mesh C.horizon n i ∈ Icc 0 (C.stopTime κ B sample) :=
        ⟨by unfold mesh; positivity,hh.le⟩
      exact hb (U sample) _ _ (C.remaining_upper κ B sample hm hz hu hc hb0 η ht)
        (by simpa only [mesh_toNNReal] using C.ratio_upper κ B sample hz hu hc hb0 ht)
    · simpa only [abs_zero] using hK
  let A := fun n i => rawCoeff C.height_pos 1 B C.horizon (dyadicTime C.horizon n i) l b η (Real.sqrt κ) z ρ C.angle
  let D := fun n i => rawCoeff C.height_pos 2 B C.horizon (dyadicTime C.horizon n i) l b η (Real.sqrt κ) z ρ C.angle
  have hAe (n i : ℕ) : A n i =ᵐ[P] stoppedCoeff 1 B C.horizon τ F n i :=
    rawCoeff_stoppedCoeff_ae C.height_pos hB 1 C.horizon C.horizon_pos l b η (Real.sqrt κ) z ρ C.angle n i
  have hDe (n i : ℕ) : D n i =ᵐ[P] stoppedCoeff 2 B C.horizon τ F n i :=
    rawCoeff_stoppedCoeff_ae C.height_pos hB 2 C.horizon C.horizon_pos l b η (Real.sqrt κ) z ρ C.angle n i
  have hAm (n i : ℕ) : Measurable[pastSigma B (dyadicTime C.horizon n i)] (A n i) :=
    rawCoeff_measurable_past C.height_pos 1 (Or.inl rfl) B C.horizon _ l b η (Real.sqrt κ) hl hb hη z ρ C.angle
  have hDm (n i : ℕ) : Measurable[pastSigma B (dyadicTime C.horizon n i)] (D n i) :=
    rawCoeff_measurable_past C.height_pos 2 (Or.inr rfl) B C.horizon _ l b η (Real.sqrt κ) hl hb hη z ρ C.angle
  have hA2 (n i : ℕ) : MemLp (A n i) 2 P := by
    apply MemLp.of_bound (rawCoeff_aemeasurable C.height_pos hB 1 (Or.inl rfl) C.horizon _ l b η (Real.sqrt κ) hl hb hη z ρ C.angle).aestronglyMeasurable K₁
    filter_upwards [hAe n i,hsbound 1 K₁ hK₁ hb₁ n i] with sample he hh
    change |A n i sample| ≤ K₁
    rw [he]
    exact hh
  have hD2 (n i : ℕ) : MemLp (D n i) 2 P := by
    apply MemLp.of_bound (rawCoeff_aemeasurable C.height_pos hB 2 (Or.inr rfl) C.horizon _ l b η (Real.sqrt κ) hl hb hη z ρ C.angle).aestronglyMeasurable K₂
    filter_upwards [hDe n i,hsbound 2 K₂ hK₂ hb₂ n i] with sample he hh
    change |D n i sample| ≤ K₂
    rw [he]
    exact hh
  have hi := BrownianLocal.stopped_field_ito_centered_ae hB C.horizon τ F V htau hreg
    A D hAe hDe hDm hD2 K₂ hK₂ (hsbound 2 K₂ hK₂ hb₂) hAm hA2 K₁ hK₁ (hsbound 1 K₁ hK₁ hb₁)
  let Y := fun sample => F sample (τ sample) (B (τ sample).toNNReal sample) - F sample 0 (B 0 sample) -
    (∫ t in (0:ℝ)..(τ sample), V sample t (B t.toNNReal sample)) -
    (1/2:ℝ)*∫ t in (0:ℝ)..(τ sample), iteratedDeriv 2 (F sample t) (B t.toNNReal sample)
  change Integrable Y P ∧ (∫ sample, Y sample ∂P) = 0 at hi
  have hmaj : ∀ᵐ sample ∂P, C.barrier η κ B sample ≤ Y sample+G := by
    filter_upwards [hB.cont,hB.toIsPreBrownianReal.eval_zero_ae_eq_zero] with sample hc hb0
    have hd := integral_drift_nonpos C.height_pos C.horizon.coe_nonneg hκ hη hρ C.horizon_pos
      (U sample) z C.angle (fun t => B t.toNNReal sample) (hc.comp continuous_real_toNNReal)
      (C.path_eq κ B sample hc)
    have hin : F sample 0 (B 0 sample) = G := by
      rw [hb0]
      exact field_initial C.height_pos C.horizon.coe_nonneg (C.height_initial hz hu.le).le hu.le l b η (Real.sqrt κ) (U sample)
    change _ ≤ Y sample+G
    dsimp only [Y]
    rw [hin]
    change C.barrier η κ B sample ≤ C.barrier η κ B sample - G - _ - _ + G
    change (∫ t in (0:ℝ)..(τ sample), V sample t (B t.toNNReal sample)) +
      (1/2:ℝ)*∫ t in (0:ℝ)..(τ sample), iteratedDeriv 2 (F sample t) (B t.toNNReal sample) ≤ 0 at hd
    linarith only [hd]
  have hInt : Integrable (fun sample => Y sample+G) P := hi.1.add (integrable_const G)
  have hI : Integrable (C.barrier η κ B) P := by
    apply hInt.mono' (C.barrier_aemeasurable hB η κ hκ hη).aestronglyMeasurable
    filter_upwards [hmaj] with sample hh
    simpa only [Real.norm_eq_abs, abs_of_nonneg (C.barrier_nonneg η κ B sample hκ hη)] using hh
  refine ⟨hI, ?_⟩
  calc
    (∫ sample, C.barrier η κ B sample ∂P) ≤ ∫ sample, Y sample+G ∂P := integral_mono_ae hI hInt hmaj
    _ = G := by rw [integral_add hi.1 (integrable_const G), hi.2]; simp

end SLEExactGauge.FiniteTilt.Cutoff

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.FiniteTilt.Cutoff
open LoewnerCutoff LoewnerExit LoewnerField LoewnerLocalized GammaField AngularBarrier
variable {z : ℂ} {u : ℝ} (C : Cutoff z u)
variable {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (sample : Ω)
variable {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}
variable (h : IsLoewnerTraceUsing (fun t => Real.sqrt κ*B t.toNNReal sample) γ g f)
variable (hz : z ∈ halfPlane) (hu : 0 < u)
variable (hc : Continuous (fun t => B t sample)) (hb0 : B 0 sample = 0)
include h hz hu hc hb0

lemma barrier_at_radius (η : ℝ) {t : ℝ≥0} (ht : C.stopTime κ B sample = t)
    (hrt : loewnerRadius g t z = (2*z.im)*Real.exp (-u)) :
    C.barrier η κ B sample = profile (κ/2) ((8/κ-1)/2) η
      (((g t z).re-Real.sqrt κ*B t sample)/(g t z).im) := by
  have h0 := C.initial_deficit_brownian κ B sample hz hu hc hb0
  have hs := source_until_stop C.height_pos C.horizon_pos h _ z _ C.angle
    (C.path_eq κ B sample hc) h0
  have hh := ((deficit_nonneg_iff C.height_pos C.horizon.coe_nonneg _ z _ C.angle _).1
    (nonneg_until C.height_pos C.horizon.coe_nonneg C.horizon_pos _ z _ C.angle h0
      ⟨(C.bounds κ B sample).1,le_rfl⟩)).2.1
  have hpos := hs.2 ⟨(C.bounds κ B sample).1,le_rfl⟩
  have hr := C.source_radius κ B sample h hz hu hc hb0
  rw [ht,hrt] at hr
  unfold barrier GammaField.field remaining
  rw [rawRemaining_eq C.height_pos C.horizon.coe_nonneg η _ _ z _ hh, ht, hr]
  simp only [add_sub_cancel_right, max_self]
  unfold angleRatio LoewnerField.height
  rw [← ht, max_eq_right hh, ← hpos, ht, Real.toNNReal_coe]

end SLEExactGauge.FiniteTilt.Cutoff

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.FiniteTilt
open AngularBarrier
variable {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (sample : Ω)
variable {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}
variable (h : IsLoewnerTraceUsing (fun t => Real.sqrt κ*B t.toNNReal sample) γ g f)
variable {z : ℂ} (hz : z ∈ halfPlane) {u : ℝ} (hu : 0 < u)
variable (hc : Continuous (fun t => B t sample)) (hb0 : B 0 sample = 0)
include h hz hu hc hb0

lemma eventually_stop_at_radius {t : ℝ≥0} (hzt : z ∈ localizationDomain γ t)
    (hrt : loewnerRadius g t z = (2*z.im)*Real.exp (-u)) :
    ∀ᶠ n : ℕ in atTop, (cutoffs hz u hu.le n).stopTime κ B sample = t := by
  obtain ⟨η,hη,hm⟩ := h.sine_positive_minimum (κ := κ) (B := fun t => B t sample) hc t.coe_nonneg hzt
  have hδ : ∀ᶠ n : ℕ in atTop, shrinkingAngle z n < η :=
    (shrinkingAngle_tendsto z).eventually (gt_mem_nhds hη)
  filter_upwards [hδ] with n hn
  let C := cutoffs hz u hu.le n
  have hh : loewnerRadius g (C.stopTime κ B sample) z = (2*z.im)*Real.exp (-u) := by
    rcases C.source_terminal κ B sample h hz hu hc hb0 with hr | hs
    · exact hr
    · have htm := hm (C.stopTime κ B sample)
        ⟨(C.bounds κ B sample).1,C.stopTime_le_radius κ B sample h hz hu hc hb0 t.coe_nonneg hzt hrt⟩
      rw [hs] at htm
      exact False.elim ((not_lt_of_ge htm) hn)
  exact h.live_radius_injective
    ((continuous_const.mul (hc.comp continuous_real_toNNReal)).continuousOn)
    (C.bounds κ B sample).1 t.coe_nonneg (C.source_live κ B sample h hz hu hc hb0) hzt
    (hh.trans hrt.symm)

omit h hz hu hc hb0 in
def timeShift (n : ℕ) : ℝ := 1/((n:ℝ)+1)

omit h hz hu hc hb0 in
lemma timeShift_pos (n : ℕ) : 0 < timeShift n := by unfold timeShift; positivity

omit h hz hu hc hb0 in
lemma timeShift_tendsto : Tendsto timeShift atTop (𝓝[>] (0:ℝ)) := by
  apply tendsto_nhdsWithin_iff.2
  constructor
  · change Tendsto (fun n : ℕ => (1:ℝ)/((n:ℝ)+1)) atTop (𝓝 0)
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_const_div_atTop_nhds_zero_nat (1:ℝ)).comp (tendsto_add_atTop_nat 1)
  · exact Filter.Eventually.of_forall timeShift_pos

lemma barrier_tendsto_on_hit (hκ : 0 < κ ∧ κ < 8)
    (hhit : firstLiveRadiusStop γ g z u ≠ (⊤ : ℝ≥0∞)) :
    Tendsto (fun n : ℕ => ENNReal.ofReal ((cutoffs hz u hu.le n).barrier (timeShift n) κ B sample)) atTop (𝓝 1) := by
  have hex : ∃ t : ℝ≥0, z ∈ localizationDomain γ t ∧ loewnerRadius g t z = (2*z.im)*Real.exp (-u) := by
    by_contra hn
    have he : {t : ℝ≥0 | z ∈ localizationDomain γ t ∧ loewnerRadius g t z = (2*z.im)*Real.exp (-u)} = ∅ := by
      exact Set.eq_empty_iff_forall_notMem.2 (fun t ht => hn ⟨t,ht⟩)
    exact hhit (by simp only [firstLiveRadiusStop, he, Set.image_empty, sInf_empty])
  obtain ⟨t,hzt,hrt⟩ := hex
  have he : (fun n : ℕ => (cutoffs hz u hu.le n).barrier (timeShift n) κ B sample) =ᶠ[atTop]
      (fun n => profile (κ/2) ((8/κ-1)/2) (timeShift n)
        (((g t z).re-Real.sqrt κ*B t sample)/(g t z).im)) := by
    filter_upwards [eventually_stop_at_radius κ B sample h hz hu hc hb0 hzt hrt] with n hn
    exact (cutoffs hz u hu.le n).barrier_at_radius κ B sample h hz hu hc hb0 (timeShift n) hn hrt
  have hl : 0 < κ/2 := div_pos hκ.1 (by norm_num)
  have hb : 0 < (8/κ-1)/2 := by
    have hh : 1 < 8/κ := (lt_div_iff₀ hκ.1).2 (by simpa using hκ.2)
    linarith
  have ht := (value_tendsto_zero_time hl hb (squaredSine_pos
    (((g t z).re-Real.sqrt κ*B t sample)/(g t z).im))).comp timeShift_tendsto
  have ht' := ht.congr' he.symm
  simpa only [ENNReal.ofReal_one, Function.comp_def] using
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht'

end SLEExactGauge.FiniteTilt

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
open FiniteTilt AngularBarrier

lemma radiusApproachProfile {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ ∧ κ < 8)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
    (hmaps : ∀ᵐ sample ∂P, IsLoewnerTraceUsing
      (fun t => Real.sqrt κ*B t.toNNReal sample) (γ sample) (g sample) (f sample))
    (z : ℂ) (hz : z ∈ halfPlane) (u : ℝ) (hu : 0 < u) :
    P {sample | firstLiveRadiusStop (γ sample) (g sample) z u ≠ (⊤ : ℝ≥0∞)} ≤
      ENNReal.ofReal (profile (κ/2) ((8/κ-1)/2) u (z.re/z.im)) := by
  let C := cutoffs hz u hu.le
  let F := fun n sample => ENNReal.ofReal ((C n).barrier (timeShift n) κ B sample)
  let Y := fun sample => liminf (fun n => F n sample) atTop
  have hFm (n : ℕ) : AEMeasurable (F n) P :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((C n).barrier_aemeasurable hB (timeShift n) κ hκ (timeShift_pos n))
  have hYm : AEMeasurable Y P := by
    dsimp only [Y]
    simp_rw [liminf_eq_iSup_iInf_of_nat]
    exact AEMeasurable.iSup (fun n => AEMeasurable.iInf (fun i => AEMeasurable.iInf (fun (_ : n ≤ i) => hFm i)))
  have hsub : {sample | firstLiveRadiusStop (γ sample) (g sample) z u ≠ (⊤ : ℝ≥0∞)} ≤ᵐ[P]
      {sample | (1:ℝ≥0∞) ≤ Y sample} := by
    filter_upwards [hmaps,hB.cont,hB.toIsPreBrownianReal.eval_zero_ae_eq_zero] with sample hm hc hb0 hhit
    have hh := barrier_tendsto_on_hit κ B sample hm hz hu hc hb0 hκ hhit
    have he : Y sample = 1 := hh.liminf_eq
    exact he.ge
  have hexp (n : ℕ) : (∫⁻ sample, F n sample ∂P) ≤
      ENNReal.ofReal (profile (κ/2) ((8/κ-1)/2) (timeShift n+u) (z.re/z.im)) := by
    have hi := (C n).barrier_expectation hB (timeShift n) κ hκ (timeShift_pos n) hz hu γ g f hmaps
    rw [← ofReal_integral_eq_lintegral_ofReal hi.1 (Filter.Eventually.of_forall
      (fun sample => (C n).barrier_nonneg (timeShift n) κ B sample hκ (timeShift_pos n)))]
    exact ENNReal.ofReal_le_ofReal hi.2
  have hl : 0 < κ/2 := div_pos hκ.1 (by norm_num)
  have hb : 0 < (8/κ-1)/2 := by
    have hh : 1 < 8/κ := (lt_div_iff₀ hκ.1).2 (by simpa using hκ.2)
    linarith
  have ht : Tendsto (fun n : ℕ => ENNReal.ofReal
      (profile (κ/2) ((8/κ-1)/2) (timeShift n+u) (z.re/z.im))) atTop
      (𝓝 (ENNReal.ofReal (profile (κ/2) ((8/κ-1)/2) u (z.re/z.im)))) := by
    have hs : Tendsto (fun n => (timeShift n+u,z.re/z.im)) atTop (𝓝 (u,z.re/z.im)) := by
      have ht0 : Tendsto timeShift atTop (𝓝 (0:ℝ)) := timeShift_tendsto.mono_right nhdsWithin_le_nhds
      simpa only [zero_add] using (ht0.add_const u).prodMk_nhds tendsto_const_nhds
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      ((contDiffAt_profile (v := (u,z.re/z.im)) hl hb 0 hu).continuousAt.tendsto.comp hs)
  calc
    P {sample | firstLiveRadiusStop (γ sample) (g sample) z u ≠ (⊤ : ℝ≥0∞)} ≤
        P {sample | (1:ℝ≥0∞) ≤ Y sample} := measure_mono_ae hsub
    _ ≤ ∫⁻ sample, Y sample ∂P := by
      simpa only [div_one] using meas_ge_le_lintegral_div hYm (by norm_num : (1:ℝ≥0∞) ≠ 0) (by norm_num : (1:ℝ≥0∞) ≠ ⊤)
    _ ≤ liminf (fun n => ∫⁻ sample, F n sample ∂P) atTop := lintegral_liminf_le' hFm
    _ ≤ liminf (fun n => ENNReal.ofReal (profile (κ/2) ((8/κ-1)/2) (timeShift n+u) (z.re/z.im))) atTop :=
      liminf_le_liminf (Filter.Eventually.of_forall hexp)
    _ = _ := ht.liminf_eq

lemma squaredSine_initial {z : ℂ} (hz : z ∈ halfPlane) :
    squaredSine (z.re/z.im) = (z.im/‖z‖)^2 := by
  have hy : 0 < z.im := hz
  have hn : 0 < ‖z‖ := lt_of_lt_of_le hy (le_trans (le_abs_self _) (Complex.abs_im_le_norm z))
  have he : ‖z‖^2 = z.re^2+z.im^2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  unfold squaredSine
  field_simp
  nlinarith

theorem radiusApproachBound (κ : ℝ) (hκ : 0 < κ ∧ κ < 8) :
    ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (B : ℝ≥0 → Ω → ℝ) (_hB : IsBrownianReal B P)
      (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
      (_hγ : ∀ t, 0 ≤ t → AEMeasurable (fun sample => γ sample t) P)
      (_hmaps : ∀ᵐ sample ∂P, IsLoewnerTraceUsing
        (fun t => Real.sqrt κ * B t.toNNReal sample) (γ sample) (g sample) (f sample))
      (z : ℂ) (_hz : z ∈ halfPlane) (u : ℝ) (_hu : 1 ≤ u),
      P {sample | firstLiveRadiusStop (γ sample) (g sample) z u ≠ (⊤ : ℝ≥0∞)} ≤
        ENNReal.ofReal (C * Real.exp (-codimension κ * u) *
          (z.im / ‖z‖) ^ (8 / κ - 1)) := by
  have hl : 0 < κ/2 := div_pos hκ.1 (by norm_num)
  have hb : 0 < (8/κ-1)/2 := by
    have hh : 1 < 8/κ := (lt_div_iff₀ hκ.1).2 (by simpa using hκ.2)
    linarith
  obtain ⟨C,hC,hdec⟩ := value_decay hl hb
  refine ⟨C,hC,?_⟩
  intro Ω _ P _ B hB γ g f hγ hmaps z hz u hu
  have hu0 : 0 < u := by linarith
  apply (radiusApproachProfile κ hκ B hB γ g f hmaps z hz u hu0).trans
  apply ENNReal.ofReal_le_ofReal
  have hp : (κ/2)*((8/κ-1)/2)/2 = codimension κ := by
    unfold codimension dimension
    field_simp [hκ.1.ne']
    ring
  have hq : (squaredSine (z.re/z.im))^((8/κ-1)/2) = (z.im/‖z‖)^(8/κ-1) := by
    rw [squaredSine_initial hz, ← Real.rpow_natCast (z.im/‖z‖) 2,
      ← Real.rpow_mul (initial_sine_pos hz).le]
    congr 1
    ring
  have hh := hdec u (squaredSine (z.re/z.im)) hu (squaredSine_pos _).le
  simpa only [profile,hp,hq] using hh

end SLEExactGauge

end

end

section
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
namespace SLEExactGauge.UnivalentDistance

lemma derivative_variation {f : ℂ → ℂ} {a : ℂ} {r A : ℝ}
    (hr : 0 < r) (hd : DifferentiableOn ℂ f (ball a (2*r)))
    (hb : ∀ z ∈ closedBall a r, ‖deriv f z‖ ≤ 2*A)
    {z : ℂ} (hz : z ∈ closedBall a (r/2)) :
    ‖deriv f z - deriv f a‖ ≤ (4*A/r)*‖z-a‖ := by
  have hd' := hd.deriv isOpen_ball
  have hsub : closedBall a (r/2) ⊆ ball a (2*r) := closedBall_subset_ball (by linarith)
  have hbound (w : ℂ) (hw : w ∈ closedBall a (r/2)) :
      ‖deriv (deriv f) w‖ ≤ 4*A/r := by
    have hs : closedBall w (r/2) ⊆ closedBall a r := by
      apply closedBall_subset_closedBall'
      have hh := mem_closedBall.1 hw
      linarith
    have hsc : closure (ball w (r/2)) ⊆ ball a (2*r) := by
      rw [closure_ball _ (by linarith : r/2 ≠ 0)]
      exact hs.trans (closedBall_subset_ball (by linarith))
    have hh := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
      (f := deriv f) (by linarith : 0 < r/2) (hd'.mono hsc).diffContOnCl
      (fun v hv => hb v (hs (sphere_subset_closedBall hv)))
    convert hh using 1; field_simp; ring
  exact (convex_closedBall a (r/2)).norm_image_sub_le_of_norm_deriv_le
    (fun w hw => hd'.differentiableAt (isOpen_ball.mem_nhds (hsub hw))) hbound
    (mem_closedBall_self (by linarith)) hz

lemma local_image_disk {f : ℂ → ℂ} {a : ℂ} {r : ℝ}
    (hr : 0 < r) (hd : DifferentiableOn ℂ f (ball a (2*r)))
    (ha : deriv f a ≠ 0)
    (hb : ∀ z ∈ closedBall a r, ‖deriv f z‖ ≤ 2*‖deriv f a‖) :
    closedBall (f a) (‖deriv f a‖*r/32) ⊆ f '' closedBall a (r/16) := by
  let F : ℂ → ℂ := fun z => (f z-f a)/deriv f a
  have hA : 0 < ‖deriv f a‖ := norm_pos_iff.2 ha
  have hs : closedBall a (r/16) ⊆ ball a (2*r) := closedBall_subset_ball (by linarith)
  have hdF (z : ℂ) (hz : z ∈ closedBall a (r/16)) :
      HasDerivAt F (deriv f z/deriv f a) z :=
    ((hd.differentiableAt (isOpen_ball.mem_nhds (hs hz))).hasDerivAt.sub_const _).div_const _
  have hbound (z : ℂ) (hz : z ∈ closedBall a (r/16)) :
      ‖deriv f z/deriv f a-1‖ ≤ (1/2:ℝ) := by
    have hv := derivative_variation hr hd hb
      (closedBall_subset_closedBall (by linarith : r/16 ≤ r/2) hz)
    have he : deriv f z/deriv f a-1 = (deriv f z-deriv f a)/deriv f a := by
      field_simp
    rw [he,norm_div,div_le_iff₀ hA]
    have hn := mem_closedBall_iff_norm.1 hz
    have hn' : (4*‖deriv f a‖/r)*‖z-a‖ ≤ (4*‖deriv f a‖/r)*(r/16) :=
      mul_le_mul_of_nonneg_left hn (by positivity)
    have he' : (4*‖deriv f a‖/r)*(r/16) = ‖deriv f a‖/4 := by field_simp; ring
    rw [he'] at hn'
    linarith
  have happ : ApproximatesLinearOn F (ContinuousLinearMap.id ℂ ℂ)
      (closedBall a (r/16)) (1/2:ℝ≥0) := by
    intro x hx y hy
    have hh := (convex_closedBall a (r/16)).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z hz => ((hdF z hz).sub (hasDerivAt_id z)).hasDerivWithinAt) hbound hy hx
    change ‖(F x-x)-(F y-y)‖ ≤ (1/2:ℝ)*‖x-y‖ at hh
    have he : (F x-x)-(F y-y) = F x-F y-(x-y) := by ring
    rw [he] at hh
    exact hh
  have hsurj := happ.surjOn_closedBall_of_nonlinearRightInverse
    (ContinuousLinearEquiv.refl ℂ ℂ).toNonlinearRightInverse (by linarith : 0 ≤ r/16) Subset.rfl
  have hsurj' : closedBall 0 (r/32) ⊆ F '' closedBall a (r/16) := by
    change closedBall (F a) (((↑(ContinuousLinearEquiv.refl ℂ ℂ).toNonlinearRightInverse.nnnorm : ℝ)⁻¹ - (1/2)) * (r/16)) ⊆ _ at hsurj
    have hn : (↑(ContinuousLinearEquiv.refl ℂ ℂ).toNonlinearRightInverse.nnnorm : ℝ) = 1 := by
      simp [ContinuousLinearEquiv.toNonlinearRightInverse]
    rw [hn,show ((1:ℝ)⁻¹-(1/2))*(r/16) = r/32 by norm_num; ring] at hsurj
    simpa only [F,sub_self,zero_div] using hsurj
  intro w hw
  have hw' : (w-f a)/deriv f a ∈ closedBall (0:ℂ) (r/32) := by
    rw [mem_closedBall_iff_norm,sub_zero,norm_div,div_le_iff₀ hA]
    have hh := mem_closedBall_iff_norm.1 hw
    nlinarith
  obtain ⟨v,hv,he⟩ := hsurj' hw'
  refine ⟨v,hv,?_⟩
  dsimp only [F] at he
  have he' : f v-f a = w-f a := (div_left_inj' ha).mp he
  exact sub_left_injective he'

lemma image_disk {f : ℂ → ℂ} (hd : DifferentiableOn ℂ f (ball 0 1))
    (h0 : deriv f 0 ≠ 0) :
    ∃ b : ℂ, closedBall b (‖deriv f 0‖/128) ⊆ f '' ball 0 1 := by
  have hs : closedBall (0:ℂ) (1/2:ℝ) ⊆ ball 0 1 := closedBall_subset_ball (by norm_num)
  have hc : ContinuousOn (fun z : ℂ => (1/2-‖z‖)*‖deriv f z‖)
      (closedBall 0 (1/2:ℝ)) :=
    (continuous_const.sub continuous_norm).continuousOn.mul
      ((hd.deriv isOpen_ball).continuousOn.mono hs).norm
  obtain ⟨a,ha,hm⟩ := (isCompact_closedBall (0:ℂ) (1/2:ℝ)).exists_isMaxOn
    (nonempty_closedBall.mpr (by norm_num)) hc
  have ham : ‖a‖ ≤ (1/2:ℝ) := by simpa using ha
  have hmax0 := hm (mem_closedBall_self (by norm_num : (0:ℝ) ≤ 1/2))
  change (1/2-‖(0:ℂ)‖)*‖deriv f 0‖ ≤ (1/2-‖a‖)*‖deriv f a‖ at hmax0
  simp only [norm_zero,sub_zero] at hmax0
  have h0p := norm_pos_iff.mpr h0
  have hAp : 0 < ‖deriv f a‖ := by
    by_contra hh
    have he : ‖deriv f a‖ = 0 := le_antisymm (le_of_not_gt hh) (norm_nonneg _)
    rw [he,mul_zero] at hmax0
    linarith
  have halt : ‖a‖ < (1/2:ℝ) := by nlinarith
  let r : ℝ := (1/2-‖a‖)/2
  have hr : 0 < r := by dsimp [r]; linarith
  have he : 2*r = 1/2-‖a‖ := by dsimp [r]; ring
  have hsub : ball a (2*r) ⊆ ball (0:ℂ) 1 := by
    apply ball_subset_ball'
    rw [dist_zero_right,he]
    linarith
  have hb (z : ℂ) (hz : z ∈ closedBall a r) : ‖deriv f z‖ ≤ 2*‖deriv f a‖ := by
    have hzn : ‖z‖ ≤ ‖a‖+r := by
      have hh := norm_le_norm_add_norm_sub a z
      rw [norm_sub_rev a z] at hh
      have hz' := mem_closedBall_iff_norm.1 hz
      linarith
    have hz0 : z ∈ closedBall (0:ℂ) (1/2:ℝ) := by
      simp only [mem_closedBall_iff_norm,sub_zero]
      linarith
    have hmz := hm hz0
    change (1/2-‖z‖)*‖deriv f z‖ ≤ (1/2-‖a‖)*‖deriv f a‖ at hmz
    have hwel : r ≤ 1/2-‖z‖ := by linarith
    have hh := mul_le_mul_of_nonneg_right hwel (norm_nonneg (deriv f z))
    nlinarith
  refine ⟨f a,?_⟩
  have hrad : ‖deriv f 0‖/128 ≤ ‖deriv f a‖*r/32 := by nlinarith
  apply (closedBall_subset_closedBall hrad).trans
  apply (local_image_disk hr (hd.mono hsub) (norm_pos_iff.mp hAp) hb).trans
  apply image_mono
  apply closedBall_subset_ball'
  rw [dist_zero_right]
  linarith

lemma exp_injective_derivative_bound {h : ℂ → ℂ}
    (hd : DifferentiableOn ℂ h (ball 0 1)) (hi : InjOn (Complex.exp ∘ h) (ball 0 1)) :
    ‖deriv h 0‖ ≤ 256*Real.pi := by
  by_contra hb
  have hp := Real.pi_pos
  have hn : 0 < ‖deriv h 0‖ := by linarith
  obtain ⟨b,hbim⟩ := image_disk hd (norm_pos_iff.mp hn)
  have hb0 : b ∈ closedBall b (‖deriv h 0‖/128) := mem_closedBall_self (by positivity)
  have hb1 : b+2*Real.pi*Complex.I ∈ closedBall b (‖deriv h 0‖/128) := by
    rw [mem_closedBall_iff_norm,add_sub_cancel_left]
    norm_num [norm_mul,Complex.norm_real,abs_of_pos hp]
    linarith
  obtain ⟨z0,hz0,hz0'⟩ := hbim hb0
  obtain ⟨z1,hz1,hz1'⟩ := hbim hb1
  have he : z1 = z0 := hi hz1 hz0 (by
    simp only [Function.comp_apply,hz0',hz1']
    exact Complex.exp_periodic b)
  have he' : (2:ℂ)*Real.pi*Complex.I = 0 := by
    rw [he,hz0'] at hz1'
    linear_combination -hz1'
  have hh : (Real.pi:ℂ) = 0 := (mul_eq_zero.mp he').resolve_right Complex.I_ne_zero |>
    (fun h => (mul_eq_zero.mp h).resolve_left (by norm_num))
  exact Real.pi_ne_zero (Complex.ofReal_eq_zero.mp hh)

lemma omitted_value_bound {f : ℂ → ℂ} (hd : DifferentiableOn ℂ f (ball 0 1))
    (hi : InjOn f (ball 0 1)) {w : ℂ} (hw : w ∉ f '' ball 0 1) :
    ‖deriv f 0‖ ≤ (256*Real.pi)*‖f 0-w‖ := by
  have hzero : (0:ℂ) ∈ ball 0 1 := mem_ball_self zero_lt_one
  have hn (z : ℂ) (hz : z ∈ ball (0:ℂ) 1) : f z-w ≠ 0 := by
    intro he
    exact hw ⟨z,hz,sub_eq_zero.mp he⟩
  have hc : IsSimplyConnected (ball (0:ℂ) 1) := by
    let := (convex_ball (0:ℂ) (1:ℝ)).contractibleSpace (nonempty_ball.mpr zero_lt_one)
    change SimplyConnectedSpace (ball (0:ℂ) 1)
    infer_instance
  obtain ⟨h,hhc,hhe⟩ := Complex.exists_continuousOn_eqOn_exp_comp hc isOpen_ball
    (hd.continuousOn.sub continuousOn_const) (by
      rintro ⟨z,hz,he⟩
      exact hn z hz he)
  have hhd (z : ℂ) (hz : z ∈ ball (0:ℂ) 1) :
      HasDerivAt h (deriv f z/(f z-w)) z := by
    have hh := HasDerivAt.of_comp_left
      (hhc.continuousAt (isOpen_ball.mem_nhds hz))
      (Complex.hasDerivAt_exp (h z))
      ((hd.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt.sub_const w)
      (Complex.exp_ne_zero _) (hhe.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz))
    have he : Complex.exp (h z) = f z-w := hhe hz
    simpa only [he] using hh
  have hhd' : DifferentiableOn ℂ h (ball 0 1) := fun z hz => (hhd z hz).differentiableAt.differentiableWithinAt
  have hhi : InjOn (Complex.exp ∘ h) (ball 0 1) := by
    intro z hz v hv he
    apply hi hz hv
    rw [hhe hz,hhe hv] at he
    exact sub_left_injective he
  have hh := exp_injective_derivative_bound hhd' hhi
  rw [(hhd 0 hzero).deriv,norm_div,div_le_iff₀ (norm_pos_iff.mpr (hn 0 hzero))] at hh
  exact hh

end SLEExactGauge.UnivalentDistance

end

end

section
noncomputable section
open Set Filter Metric
open scoped Topology NNReal
namespace SLEExactGauge.IsLoewnerTraceUsing
variable {driver : ℝ → ℝ} {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}

lemma radius_le_complement_distance (h : IsLoewnerTraceUsing driver γ g f)
    {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : z ∈ localizationDomain γ t)
    {w : ℂ} (hw : w ∉ localizationDomain γ t) :
    loewnerRadius g t z ≤ (512*Real.pi)*dist z w := by
  have hpos := h.im_pos ht hz
  have hdn := h.deriv_ne_zero ht hz
  rcases h with ⟨hγ,hzero,him,htrans,hinit,hg,hf,hgmap,hfmap,hfg,hgf,hc,hd,htip⟩
  let φ : ℂ → ℂ := fun q => g t z + ((g t z).im:ℂ)*q
  let F : ℂ → ℂ := fun q => f t (φ q)
  have hφ0 : φ 0 = g t z := by simp [φ]
  have hφ (q : ℂ) (hq : q ∈ ball (0:ℂ) 1) : φ q ∈ halfPlane := by
    have hqn : ‖q‖ < 1 := by simpa using hq
    have hqi := Complex.abs_im_le_norm q
    have hql := neg_abs_le q.im
    change 0 < (φ q).im
    simp only [φ,Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      zero_mul,add_zero]
    nlinarith
  have hdφ (q : ℂ) : HasDerivAt φ ((g t z).im:ℂ) q := by
    simpa only [mul_one,id_eq] using! ((hasDerivAt_id q).const_mul ((g t z).im:ℂ)).const_add (g t z)
  have hdF (q : ℂ) (hq : q ∈ ball (0:ℂ) 1) : DifferentiableAt ℂ F q :=
    (hf t ht _ (hφ q hq)).differentiableAt.comp q (hdφ q).differentiableAt
  have hiF : InjOn F (ball 0 1) := by
    intro q hq v hv he
    have hh := congrArg (g t) he
    change g t (f t (φ q)) = g t (f t (φ v)) at hh
    rw [hgf t ht _ (hφ q hq),hgf t ht _ (hφ v hv)] at hh
    dsimp only [φ] at hh
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hpos.ne') (add_left_cancel hh)
  have hFw : w ∉ F '' ball 0 1 := by
    rintro ⟨q,hq,he⟩
    exact hw (he ▸ hfmap t ht (hφ q hq))
  have hgd := (hg t ht z hz).differentiableAt.hasDerivAt
  have hfd := (hf t ht _ (hgmap t ht hz)).differentiableAt.hasDerivAt
  have heq : (fun v => f t (g t v)) =ᶠ[𝓝 z] id := by
    filter_upwards [(survivingDomain_open hγ ht).mem_nhds hz] with v hv
    exact hfg t ht v hv
  have he := ((hfd.comp z hgd).congr_of_eventuallyEq heq.symm).unique (hasDerivAt_id z)
  have hen : ‖deriv (f t) (g t z)‖*‖deriv (g t) z‖ = 1 := by
    simpa only [norm_mul,norm_one] using congrArg norm he
  have hFd : deriv F 0 = deriv (f t) (g t z)*((g t z).im:ℂ) := by
    have hfd' : HasDerivAt (f t) (deriv (f t) (g t z)) (φ 0) := hφ0.symm ▸ hfd
    exact (hfd'.comp 0 (hdφ 0)).deriv
  have hF0 : F 0 = z := by simp only [F,hφ0,hfg t ht z hz]
  have hR : loewnerRadius g t z = 2*‖deriv F 0‖ := by
    rw [loewnerRadius,hFd,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hpos,
      div_eq_iff (norm_ne_zero_iff.mpr hdn)]
    nlinarith
  have hh := UnivalentDistance.omitted_value_bound
    (fun q hq => (hdF q hq).differentiableWithinAt) hiF hFw
  rw [hF0] at hh
  rw [hR,dist_eq_norm]
  nlinarith

lemma radius_le_boundary_distance (h : IsLoewnerTraceUsing driver γ g f)
    {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (hz : z ∈ localizationDomain γ t) :
    loewnerRadius g t z ≤ (512*Real.pi)*infDist z (localizationDomain γ t)ᶜ := by
  have hp : 0 < 512*Real.pi := by positivity
  have hn : ((localizationDomain γ t)ᶜ).Nonempty := by
    refine ⟨0,?_⟩
    intro h0
    exact (lt_irrefl (0:ℝ)) (by simpa [halfPlane] using h0.1.1)
  rw [mul_comm (512*Real.pi),← div_le_iff₀ hp]
  apply (le_infDist hn).2
  intro w hw
  rw [div_le_iff₀ hp]
  exact (h.radius_le_complement_distance ht hz hw).trans_eq (mul_comm _ _)

end SLEExactGauge.IsLoewnerTraceUsing

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge

def liveDistanceApproach (γ : ℝ → ℂ) (z : ℂ) (ε : ℝ) : Prop :=
  ∃ t : ℝ≥0, z ∈ localizationDomain γ t ∧ infDist z (localizationDomain γ t)ᶜ < ε

lemma liveDistanceApproach_radius_hit {driver : ℝ → ℝ} {γ : ℝ → ℂ}
    {g f : ℝ → ℂ → ℂ} (h : IsLoewnerTraceUsing driver γ g f)
    (hd : ContinuousOn driver (Ici 0)) {z : ℂ} (hz : z ∈ halfPlane)
    {ε u : ℝ} (hr : (2*z.im)*Real.exp (-u) = (512*Real.pi)*ε)
    (hsmall : (512*Real.pi)*ε ≤ 2*z.im)
    (hhit : liveDistanceApproach γ z ε) :
    firstLiveRadiusStop γ g z u ≠ (⊤ : ℝ≥0∞) := by
  obtain ⟨t,hzt,hclose⟩ := hhit
  have hrt : loewnerRadius g t z < (2*z.im)*Real.exp (-u) := by
    rw [hr]
    exact (h.radius_le_boundary_distance t.coe_nonneg hzt).trans_lt
      (mul_lt_mul_of_pos_left hclose (by positivity))
  obtain ⟨s,hs,hseq⟩ := intermediate_value_Icc' t.coe_nonneg
    (h.continuous_radius t.coe_nonneg (hd.mono Icc_subset_Ici_self) hzt)
    ⟨hrt.le,by rw [h.radius_initial hz,hr]; exact hsmall⟩
  apply ne_top_of_le_ne_top (ENNReal.coe_ne_top (r := ⟨s,hs.1⟩))
  apply sInf_le
  exact ⟨⟨s,hs.1⟩,⟨survivingDomain_mono hs.2 hzt,hseq⟩,rfl⟩

theorem euclideanApproachBound (κ : ℝ) (hκ : 0 < κ ∧ κ < 8) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ c < 1 ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (B : ℝ≥0 → Ω → ℝ) (_hB : IsBrownianReal B P)
      (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
      (_hγ : ∀ t, 0 ≤ t → AEMeasurable (fun sample => γ sample t) P)
      (_hmaps : ∀ᵐ sample ∂P, IsLoewnerTraceUsing
        (fun t => Real.sqrt κ * B t.toNNReal sample) (γ sample) (g sample) (f sample))
      (z : ℂ) (_hz : z ∈ halfPlane) (ε : ℝ) (_hε : 0 < ε) (_hsmall : ε < c*z.im),
      P {sample | liveDistanceApproach (γ sample) z ε} ≤
        ENNReal.ofReal (C * ((2*z.im)^(-codimension κ) *
          (z.im/‖z‖)^(8/κ-1)) * ε^(codimension κ)) := by
  obtain ⟨C,hC,hbound⟩ := radiusApproachBound κ hκ
  let K : ℝ := 512*Real.pi
  have hK : 0 < K := by dsimp [K]; positivity
  have hK1 : 1 < K := by dsimp [K]; nlinarith [Real.pi_gt_three]
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have heK : 1 < K*Real.exp 1 := by nlinarith
  refine ⟨C*K^(codimension κ),1/(K*Real.exp 1),mul_pos hC (Real.rpow_pos_of_pos hK _),
    by positivity,(div_lt_one (by positivity)).2 heK,?_⟩
  intro Ω _ P _ B hB γ g f hγ hmaps z hz ε hε hsmall
  have hy : 0 < z.im := hz
  have hsmall' : ε*(K*Real.exp 1) < z.im := by
    rw [one_div_mul_eq_div] at hsmall
    exact (lt_div_iff₀ (by positivity)).mp hsmall
  have hKε : 0 < K*ε := mul_pos hK hε
  let u : ℝ := Real.log ((2*z.im)/(K*ε))
  have hu : 1 ≤ u := by
    have hh : Real.exp 1 ≤ (2*z.im)/(K*ε) := by
      rw [le_div_iff₀ hKε]
      nlinarith
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hh
  have hr : (2*z.im)*Real.exp (-u) = K*ε := by
    rw [Real.exp_neg,Real.exp_log (by positivity : 0 < (2*z.im)/(K*ε))]
    field_simp
  have hstart : K*ε ≤ 2*z.im := by
    have hh : K*ε ≤ ε*(K*Real.exp 1) := by nlinarith
    linarith
  have hsub : {sample | liveDistanceApproach (γ sample) z ε} ≤ᵐ[P]
      {sample | firstLiveRadiusStop (γ sample) (g sample) z u ≠ (⊤ : ℝ≥0∞)} := by
    filter_upwards [hmaps,hB.cont] with sample hm hc hhit
    exact liveDistanceApproach_radius_hit hm
      ((continuous_const.mul (hc.comp continuous_real_toNNReal)).continuousOn)
      hz hr hstart hhit
  apply (measure_mono_ae hsub).trans
  apply (hbound P B hB γ g f hγ hmaps z hz u hu).trans
  apply ENNReal.ofReal_le_ofReal
  have hexp : Real.exp (-codimension κ*u) =
      (K*ε)^(codimension κ)*(2*z.im)^(-codimension κ) := by
    rw [Real.rpow_def_of_pos hKε,Real.rpow_def_of_pos (by positivity : 0 < 2*z.im),
      ← Real.exp_add]
    congr 1
    dsimp [u]
    rw [Real.log_div (by positivity : 2*z.im ≠ 0) hKε.ne']
    ring
  rw [hexp,Real.mul_rpow hK.le hε.le]
  exact le_of_eq (by ring)

end SLEExactGauge

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal
namespace SLEExactGauge.IsLoewnerTraceUsing
variable {driver : ℝ → ℝ} {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}

lemma future_tip_mem_closure (h : IsLoewnerTraceUsing driver γ g f)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) : γ t ∈ closure (localizationDomain γ s) := by
  rcases h with ⟨hγ,hzero,him,htrans,hinit,hg,hf,hgmap,hfmap,hfg,hgf,hc,hd,htip⟩
  apply isClosed_closure.mem_of_tendsto (htip t (hs.trans hst))
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hh : (driver t : ℂ) + (y:ℂ)*Complex.I ∈ halfPlane := by
    simpa only [halfPlane,mem_ofPred_eq,mem_Ioi,Complex.add_im,Complex.ofReal_im,Complex.mul_im,
      Complex.ofReal_re,Complex.I_im,Complex.I_re,mul_one,mul_zero,zero_mul,add_zero,zero_add] using hy
  exact subset_closure (survivingDomain_mono hst (hfmap t (hs.trans hst) hh))

end SLEExactGauge.IsLoewnerTraceUsing

end

end

end OAI

import Mathlib
import OAI.Probability.SLELocalization.ConditionalTilts
import OAI.Probability.SLE.ClippedCoordinates
import OAI.Probability.SLE.IntegralLimits
import OAI.Probability.SLE.ItoIsometry
import OAI.Probability.SLE.StochasticIntegrals

namespace OAI


/-! Conformal localization and Finite Tilt estimates. -/

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.FiniteTilt.Cutoff
open LoewnerCutoff LoewnerField LoewnerExit LoewnerLocalized BrownianPredictable
  BrownianStopped BrownianIto TaylorMeshes PredictableLimit

lemma target_setIntegral_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (η κ : ℝ) (hκ : 0 < κ ∧ κ < 8) (hη : 0 < η)
    {z : ℂ} (hz : z ∈ halfPlane) {u v : ℝ} (hu : 0 ≤ u) (huv1 : u+1 ≤ v)
    (C : Cutoff z v) (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
    (hsle : ∀ᵐ sample ∂P, IsLoewnerTraceUsing
      (fun t => Real.sqrt κ*B t.toNNReal sample) (γ sample) (g sample) (f sample))
    (E : Set Ω) (hE : NullMeasurableSet E P)
    (hstop : ∀ t : ℝ≥0, ∃ S : Set Ω, MeasurableSet[pastSigma B t] S ∧
      S =ᵐ[P] (E ∩ {sample | firstLiveRadiusStop (γ sample) (g sample) z u ≤ (t : ℝ≥0∞)} : Set Ω)) :
    (∫ sample in E, C.barrier η κ B sample ∂P) ≤
      ∫ sample in E, C.targetValue hz (by linarith : u ≤ v) η κ B sample ∂P := by
  have huv : u ≤ v := by linarith
  have hv : 0 < v := by linarith
  let D := C.retarget hz huv
  let Q := C.targetCoeff 1 η κ B
  have hQe (w : ℝ) (hwv : w ≤ v) (n i : ℕ) := C.targetCoeff_eq hB 1 η κ hz w hwv n i
  obtain ⟨K,hK,hQb⟩ := C.targetCoeff_bound hB 1 η κ hκ hη hz hv γ g f hsle
  have hQm (w : ℝ) (n i : ℕ) : Measurable[pastSigma B (dyadicTime C.horizon n i)] (Q w n i) :=
    C.targetCoeff_measurable B 1 (Or.inl rfl) η κ hκ hη w n i
  have hQ2 (w : ℝ) (hwv : w ≤ v) (n i : ℕ) : MemLp (Q w n i) 2 P := by
    apply MemLp.of_bound (C.targetCoeff_aemeasurable hB 1 (Or.inl rfl) η κ hκ hη w n i).aestronglyMeasurable K
    simpa only [Real.norm_eq_abs] using hQb w hwv n i
  have hsupport (n i : ℕ) : ∀ᵐ sample ∂P,
      (dyadicTime C.horizon n i : ℝ≥0∞) < firstLiveRadiusStop (γ sample) (g sample) z u →
        Q v n i sample = Q u n i sample := by
    filter_upwards [hQe v le_rfl n i,hQe u huv n i,hsle,hB.cont,
      hB.toIsPreBrownianReal.eval_zero_ae_eq_zero] with sample hev heu hs hc hb0
    intro ht
    rcases eq_or_lt_of_le hu with rfl | hu'
    · rw [firstLiveRadiusStop_zero hs hz] at ht
      exact False.elim (not_lt_of_ge bot_le ht)
    dsimp only [Q]
    rw [hev,heu]
    change (if mesh C.horizon n i < C.stopTime κ B sample then _ else 0) =
      (if mesh C.horizon n i < D.stopTime κ B sample then _ else 0)
    have hle := C.retarget_stop_le hz huv κ B sample
    by_cases hD : mesh C.horizon n i < D.stopTime κ B sample
    · rw [ite_eq_left hD,ite_eq_left (hD.trans_le hle)]
    · by_cases hC : mesh C.horizon n i < C.stopTime κ B sample
      · have hh := C.retarget_has_hit_of_lt hz hu' huv κ B sample hs hc hb0
          ((le_of_not_gt hD).trans_lt hC)
        have hbad : firstLiveRadiusStop (γ sample) (g sample) z u ≤
            (dyadicTime C.horizon n i : ℝ≥0∞) := by
          rw [hh,← ENNReal.ofReal_coe_nnreal,coe_dyadicTime]
          exact ENNReal.ofReal_le_ofReal (le_of_not_gt hD)
        exact False.elim ((not_lt_of_ge hbad) ht)
      · rw [ite_eq_right hC,ite_eq_right hD]
  have hlv := C.target_sum_tendsto hB η κ hκ hη hz hv γ g f hsle v le_rfl
  have hlu := C.target_sum_tendsto hB η κ hκ hη hz hv γ g f hsle u huv
  have hcenter := indicator_difference_centered hB C.horizon (Q v) (Q u)
    (hQm v) (hQm u) (hQ2 v le_rfl) (hQ2 u huv) K hK (hQb v le_rfl) (hQb u huv)
    (fun sample => firstLiveRadiusStop (γ sample) (g sample) z u) hsupport E hE hstop
    (C.targetRemainder η κ B (C.stopTime κ B))
    (C.targetRemainder η κ B (D.stopTime κ B)) hlv hlu
  have hdiff : (∫ sample in E, C.targetRemainder η κ B (C.stopTime κ B) sample -
      C.targetRemainder η κ B (D.stopTime κ B) sample ∂P) = 0 := by
    simpa only [integral_indicator₀ hE] using hcenter.2
  have hdiffint : IntegrableOn (fun sample => C.targetRemainder η κ B (C.stopTime κ B) sample -
      C.targetRemainder η κ B (D.stopTime κ B) sample) E P :=
    hcenter.1.integrableOn.congr (by
      filter_upwards [ae_restrict_mem₀ hE] with sample hs
      exact Set.indicator_of_mem hs _)
  have hbi := (C.barrier_expectation hB η κ hκ hη hz hv γ g f hsle).1
  obtain ⟨L,hL,hLb⟩ := targetValue_bound κ hκ
  have hint : Integrable (C.targetValue hz huv η κ B) P := by
    apply ((D.expectation hB κ hκ hz hu).1.const_mul
      (L*((2*z.im)*Real.exp (-v))^(codimension κ))).mono'
      (C.targetValue_aemeasurable hB hz huv η κ hκ hη).aestronglyMeasurable
    filter_upwards [hB.cont,hB.toIsPreBrownianReal.eval_zero_ae_eq_zero] with sample hc hb0
    rw [Real.norm_eq_abs,abs_of_nonneg (C.targetValue_nonneg hz huv η κ hκ hη B sample)]
    exact hLb hz hu huv1 C B sample η hη hc hb0
  have hle : (∫ sample in E, C.barrier η κ B sample-C.targetValue hz huv η κ B sample ∂P) ≤ 0 := by
    rw [← hdiff]
    apply integral_mono_ae (hbi.integrableOn.sub hint.integrableOn) hdiffint
    filter_upwards [ae_restrict_of_ae hB.cont] with sample hc
    exact C.target_difference_le_remainder hz huv η κ hκ hη B sample hc
  rw [integral_sub hbi.integrableOn hint.integrableOn] at hle
  exact sub_nonpos.mp hle

end SLEExactGauge.FiniteTilt.Cutoff

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.LoewnerLocalized
open LoewnerCutoff LoewnerField LoewnerExit BrownianPredictable BrownianStopped BrownianIto TaylorMeshes PredictableLimit

theorem localized_sum_tendsto {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (κ : ℝ) (hκ : 0 < κ ∧ κ < 8)
    {ε : ℝ} (hε : 0 < ε) (T : ℝ≥0) (hT : 0 < (T:ℝ)) (z : ℂ) (ρ δ : ℝ) :
    let U := BrownianDriver.path B (Real.sqrt κ) T
    let τ := fun sample => stop hε T.coe_nonneg (U sample) z ρ δ
    let F := fun sample => field hε T.coe_nonneg (1-κ/8) (8/κ-1) (Real.sqrt κ) (U sample) z
    ∀ᵐ sample ∂P, Tendsto (fun n => dyadicDriverSum B T
      (fun n i => rawCoeff hε 1 B T (dyadicTime T n i) (1-κ/8) (8/κ-1) (Real.sqrt κ) z ρ δ)
      n sample) atTop
      (𝓝 (F sample (τ sample) (B (τ sample).toNNReal sample) - F sample 0 (B 0 sample))) := by
  dsimp only
  let U := BrownianDriver.path B (Real.sqrt κ) T
  let τ := fun sample => stop hε T.coe_nonneg (U sample) z ρ δ
  let F := fun sample => field hε T.coe_nonneg (1-κ/8) (8/κ-1) (Real.sqrt κ) (U sample) z
  let V := fun sample => drift hε T.coe_nonneg (1-κ/8) (8/κ-1) (Real.sqrt κ) (U sample) z
  have hp : 0 ≤ 1-κ/8 := by linarith [hκ.2]
  have ha : 0 ≤ 8/κ-1 := by
    have hh : (1:ℝ) ≤ 8/κ := (le_div_iff₀ hκ.1).2 (by simpa using hκ.2.le)
    linarith
  have hreg : ∀ᵐ sample ∂P, BrownianField.FieldRegular (F sample) (V sample)
      (fun t => B t.toNNReal sample) (τ sample) := by
    filter_upwards [hB.cont] with sample hc
    exact regular hε hT (1-κ/8) (8/κ-1) (Real.sqrt κ) hp ha (U sample) z ρ δ _
      (hc.comp continuous_real_toNNReal)
  have htau : ∀ᵐ sample ∂P, 0 ≤ τ sample ∧ τ sample ≤ T :=
    Filter.Eventually.of_forall (fun sample => stop_bounds hε T.coe_nonneg (U sample) z ρ δ)
  obtain ⟨K₁,hK₁,hb₁⟩ := coeff_uniform_bound hε T.coe_nonneg 1 (Or.inl rfl)
    (1-κ/8) (8/κ-1) (Real.sqrt κ) hp ha z
  obtain ⟨K₂,hK₂,hb₂⟩ := coeff_uniform_bound hε T.coe_nonneg 2 (Or.inr rfl)
    (1-κ/8) (8/κ-1) (Real.sqrt κ) hp ha z
  have hsbound (k : ℕ) (K : ℝ) (hK : 0 ≤ K)
      (hb : ∀ (W : C(I, ℝ)) (t b : ℝ),
        |iteratedDeriv k (field hε T.coe_nonneg (1-κ/8) (8/κ-1) (Real.sqrt κ) W z t) b| ≤ K)
      (n i : ℕ) : ∀ᵐ sample ∂P, |stoppedCoeff k B T τ F n i sample| ≤ K := by
    apply Filter.Eventually.of_forall
    intro sample
    unfold stoppedCoeff
    split_ifs
    · exact hb _ _ _
    · simpa only [abs_zero] using hK
  let A := fun n i => rawCoeff hε 1 B T (dyadicTime T n i) (1-κ/8) (8/κ-1) (Real.sqrt κ) z ρ δ
  let C := fun n i => rawCoeff hε 2 B T (dyadicTime T n i) (1-κ/8) (8/κ-1) (Real.sqrt κ) z ρ δ
  have hAe (n i : ℕ) : A n i =ᵐ[P] stoppedCoeff 1 B T τ F n i :=
    rawCoeff_stoppedCoeff_ae hε hB 1 T hT (1-κ/8) (8/κ-1) (Real.sqrt κ) z ρ δ n i
  have hCe (n i : ℕ) : C n i =ᵐ[P] stoppedCoeff 2 B T τ F n i :=
    rawCoeff_stoppedCoeff_ae hε hB 2 T hT (1-κ/8) (8/κ-1) (Real.sqrt κ) z ρ δ n i
  have hAm (n i : ℕ) : Measurable[pastSigma B (dyadicTime T n i)] (A n i) :=
    rawCoeff_measurable_past hε 1 (Or.inl rfl) B T _ _ _ _ z ρ δ
  have hCm (n i : ℕ) : Measurable[pastSigma B (dyadicTime T n i)] (C n i) :=
    rawCoeff_measurable_past hε 2 (Or.inr rfl) B T _ _ _ _ z ρ δ
  have hA2 (n i : ℕ) : MemLp (A n i) 2 P := by
    apply MemLp.of_bound (rawCoeff_aemeasurable hε hB 1 (Or.inl rfl) T _ _ _ _ z ρ δ).aestronglyMeasurable K₁
    filter_upwards [hAe n i, hsbound 1 K₁ hK₁ hb₁ n i] with sample he hb
    rw [Real.norm_eq_abs]
    change |A n i sample| ≤ K₁
    rw [he]
    exact hb
  have hC2 (n i : ℕ) : MemLp (C n i) 2 P := by
    apply MemLp.of_bound (rawCoeff_aemeasurable hε hB 2 (Or.inr rfl) T _ _ _ _ z ρ δ).aestronglyMeasurable K₂
    filter_upwards [hCe n i, hsbound 2 K₂ hK₂ hb₂ n i] with sample he hb
    rw [Real.norm_eq_abs]
    change |C n i sample| ≤ K₂
    rw [he]
    exact hb
  have hi := stopped_fieldSum_tendsto_ae hB T τ F V htau hreg C hCe hCm hC2
    K₂ hK₂ (hsbound 2 K₂ hK₂ hb₂) K₁ hK₁ (hsbound 1 K₁ hK₁ hb₁)
  have he : (fun sample => F sample (τ sample) (B (τ sample).toNNReal sample) - F sample 0 (B 0 sample) -
      (∫ t in (0:ℝ)..(τ sample), V sample t (B t.toNNReal sample)) -
      (1/2:ℝ)*∫ t in (0:ℝ)..(τ sample), iteratedDeriv 2 (F sample t) (B t.toNNReal sample)) =ᵐ[P]
      (fun sample => F sample (τ sample) (B (τ sample).toNNReal sample) - F sample 0 (B 0 sample)) := by
    filter_upwards [hB.cont] with sample hc
    have hcanc := integral_drift_cancel hε hT κ hκ.1 (U sample) z ρ δ
      (fun t => B t.toNNReal sample) (fun t ht => BrownianDriver.extend_eq B _ T sample hc ht)
    dsimp only [F,V,τ]
    linarith
  have hAeall : ∀ᵐ sample ∂P, ∀ n i, A n i sample = stoppedCoeff 1 B T τ F n i sample :=
    ae_all_iff.2 (fun n => ae_all_iff.2 (hAe n))
  filter_upwards [hi,he,hAeall] with sample hi he ha
  rw [he] at hi
  convert hi using 1
  funext n
  unfold dyadicDriverSum
  simp only [← ha]
  rfl

end SLEExactGauge.LoewnerLocalized

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal unitInterval
namespace SLEExactGauge.FiniteTilt.Cutoff
open LoewnerCutoff LoewnerField LoewnerExit LoewnerLocalized BrownianPredictable
  BrownianStopped BrownianIto TaylorMeshes PredictableLimit

lemma retarget_setIntegral {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (κ : ℝ) (hκ : 0 < κ ∧ κ < 8)
    {z : ℂ} (hz : z ∈ halfPlane) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (C : Cutoff z v) (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
    (hsle : ∀ᵐ sample ∂P, IsLoewnerTraceUsing
      (fun t => Real.sqrt κ*B t.toNNReal sample) (γ sample) (g sample) (f sample))
    (E : Set Ω) (hE : NullMeasurableSet E P)
    (hstop : ∀ t : ℝ≥0, ∃ S : Set Ω, MeasurableSet[pastSigma B t] S ∧
      S =ᵐ[P] (E ∩ {sample | firstLiveRadiusStop (γ sample) (g sample) z u ≤ (t : ℝ≥0∞)} : Set Ω)) :
    (∫ sample in E, C.value κ B sample ∂P) =
      ∫ sample in E, (C.retarget hz huv).value κ B sample ∂P := by
  let D := C.retarget hz huv
  let F := fun sample => field C.height_pos C.horizon.coe_nonneg (1-κ/8) (8/κ-1)
    (Real.sqrt κ) (C.paths κ B sample) z
  let Q := fun w n i => rawCoeff C.height_pos 1 B C.horizon (dyadicTime C.horizon n i)
    (1-κ/8) (8/κ-1) (Real.sqrt κ) z ((2*z.im)*Real.exp (-w)) C.angle
  have hQe (w : ℝ) (n i : ℕ) : Q w n i =ᵐ[P]
      stoppedCoeff 1 B C.horizon
        (fun sample => stop C.height_pos C.horizon.coe_nonneg (C.paths κ B sample) z
          ((2*z.im)*Real.exp (-w)) C.angle) F n i :=
    rawCoeff_stoppedCoeff_ae C.height_pos hB 1 C.horizon C.horizon_pos
      (1-κ/8) (8/κ-1) (Real.sqrt κ) z ((2*z.im)*Real.exp (-w)) C.angle n i
  have hp : 0 ≤ 1-κ/8 := by linarith [hκ.2]
  have ha : 0 ≤ 8/κ-1 := sub_nonneg.2 ((le_div_iff₀ hκ.1).2 (by linarith [hκ.2]))
  obtain ⟨K,hK,hKb⟩ := coeff_uniform_bound C.height_pos C.horizon.coe_nonneg 1 (Or.inl rfl)
    (1-κ/8) (8/κ-1) (Real.sqrt κ) hp ha z
  have hQb (w : ℝ) (n i : ℕ) : ∀ᵐ sample ∂P, |Q w n i sample| ≤ K := by
    filter_upwards [hQe w n i] with sample he
    rw [he]
    unfold stoppedCoeff
    split_ifs
    · exact hKb _ _ _
    · simpa only [abs_zero] using hK
  have hQm (w : ℝ) (n i : ℕ) : Measurable[pastSigma B (dyadicTime C.horizon n i)] (Q w n i) :=
    rawCoeff_measurable_past C.height_pos 1 (Or.inl rfl) B C.horizon _ _ _ _ z _ C.angle
  have hQ2 (w : ℝ) (n i : ℕ) : MemLp (Q w n i) 2 P := by
    apply MemLp.of_bound (rawCoeff_aemeasurable C.height_pos hB 1 (Or.inl rfl) C.horizon
      (dyadicTime C.horizon n i) (1-κ/8) (8/κ-1) (Real.sqrt κ) z _ C.angle).aestronglyMeasurable K
    simpa only [Real.norm_eq_abs] using hQb w n i
  have hsupport (n i : ℕ) : ∀ᵐ sample ∂P,
      (dyadicTime C.horizon n i : ℝ≥0∞) < firstLiveRadiusStop (γ sample) (g sample) z u →
        Q v n i sample = Q u n i sample := by
    filter_upwards [hQe v n i,hQe u n i,hsle,hB.cont,
      hB.toIsPreBrownianReal.eval_zero_ae_eq_zero] with sample hev heu hs hc hb0
    intro ht
    rcases eq_or_lt_of_le hu with rfl | hu'
    · rw [firstLiveRadiusStop_zero hs hz] at ht
      exact False.elim (not_lt_of_ge bot_le ht)
    rw [hev,heu]
    change (if mesh C.horizon n i < C.stopTime κ B sample then _ else 0) =
      (if mesh C.horizon n i < D.stopTime κ B sample then _ else 0)
    have hle := C.retarget_stop_le hz huv κ B sample
    by_cases hD : mesh C.horizon n i < D.stopTime κ B sample
    · rw [ite_eq_left hD,ite_eq_left (hD.trans_le hle)]
    · by_cases hC : mesh C.horizon n i < C.stopTime κ B sample
      · have hh := C.retarget_has_hit_of_lt hz hu' huv κ B sample hs hc hb0
          ((le_of_not_gt hD).trans_lt hC)
        have hbad : firstLiveRadiusStop (γ sample) (g sample) z u ≤
            (dyadicTime C.horizon n i : ℝ≥0∞) := by
          rw [hh,← ENNReal.ofReal_coe_nnreal,coe_dyadicTime]
          exact ENNReal.ofReal_le_ofReal (le_of_not_gt hD)
        exact False.elim ((not_lt_of_ge hbad) ht)
      · rw [ite_eq_right hC,ite_eq_right hD]
  have hlv := localized_sum_tendsto hB κ hκ C.height_pos C.horizon C.horizon_pos z
    ((2*z.im)*Real.exp (-v)) C.angle
  have hlu := localized_sum_tendsto hB κ hκ C.height_pos C.horizon C.horizon_pos z
    ((2*z.im)*Real.exp (-u)) C.angle
  have hcenter := indicator_difference_centered hB C.horizon (Q v) (Q u)
    (hQm v) (hQm u) (hQ2 v) (hQ2 u) K hK (hQb v) (hQb u)
    (fun sample => firstLiveRadiusStop (γ sample) (g sample) z u) hsupport E hE hstop
    (fun sample => C.value κ B sample-F sample 0 (B 0 sample))
    (fun sample => D.value κ B sample-F sample 0 (B 0 sample)) hlv hlu
  have hdiff : (∫ sample in E, C.value κ B sample-D.value κ B sample ∂P) = 0 := by
    simpa only [sub_sub_sub_cancel_right,integral_indicator₀ hE] using hcenter.2
  have hv : Integrable (C.value κ B) P := (C.expectation hB κ hκ hz (hu.trans huv)).1
  have hu' : Integrable (D.value κ B) P := (D.expectation hB κ hκ hz hu).1
  rw [integral_sub hv.integrableOn hu'.integrableOn] at hdiff
  exact sub_eq_zero.mp hdiff

end SLEExactGauge.FiniteTilt.Cutoff

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge.FiniteTilt
variable {Ω : Type*} (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (sample : Ω)
variable {γ : ℝ → ℂ} {g f : ℝ → ℂ → ℂ}
variable (h : IsLoewnerTraceUsing (fun t => Real.sqrt κ*B t.toNNReal sample) γ g f)
variable {z : ℂ} (hz : z ∈ halfPlane) {u : ℝ} (hu : 0 < u)
variable (hc : Continuous (fun t => B t sample)) (hb0 : B 0 sample = 0)
variable (C : ℕ → Cutoff z u) (hC : Tendsto (fun n => (C n).angle) atTop (𝓝 0))
include h hz hu hc hb0 hC

lemma eventually_value_at_radius_general {t : ℝ≥0} (hzt : z ∈ localizationDomain γ t)
    (hrt : loewnerRadius g t z = (2*z.im)*Real.exp (-u)) :
    ∀ᶠ n : ℕ in atTop, ENNReal.ofReal ((C n).value κ B sample) =
      finiteStoppedDensity κ (fun t => B t sample) γ g z u := by
  obtain ⟨η, hη, hm⟩ := h.sine_positive_minimum (κ := κ) (B := fun t => B t sample) hc t.coe_nonneg hzt
  have hδ : ∀ᶠ n : ℕ in atTop, (C n).angle < η :=
    hC.eventually (gt_mem_nhds hη)
  filter_upwards [hδ] with n hn
  let D := C n
  have hh : loewnerRadius g (D.stopTime κ B sample) z = (2*z.im)*Real.exp (-u) := by
    rcases D.source_terminal κ B sample h hz hu hc hb0 with hr | hs
    · exact hr
    · have htm := hm (D.stopTime κ B sample)
        ⟨(D.bounds κ B sample).1,D.stopTime_le_radius κ B sample h hz hu hc hb0 t.coe_nonneg hzt hrt⟩
      rw [hs] at htm
      exact False.elim ((not_lt_of_ge htm) hn)
  have he : D.stopTime κ B sample = t := h.live_radius_injective
    ((continuous_const.mul (hc.comp continuous_real_toNNReal)).continuousOn)
    (D.bounds κ B sample).1 t.coe_nonneg (D.source_live κ B sample h hz hu hc hb0) hzt
    (hh.trans hrt.symm)
  have htau := h.firstLiveRadiusStop_eq
    ((continuous_const.mul (hc.comp continuous_real_toNNReal)).continuousOn) hzt hrt
  have hp : codimension κ = 1-κ/8 := by unfold codimension dimension; ring
  rw [finiteStoppedDensity, htau, ite_eq_right (ENNReal.coe_ne_top), ENNReal.coe_toReal, hp,
    ← he, ← D.value_eq_source κ B sample h hz hu hc hb0]

lemma tendsto_value_killed_general (hκ : 0 < κ ∧ κ < 8) :
    Tendsto (fun n : ℕ => ENNReal.ofReal ((C n).value κ B sample)) atTop
      (𝓝 (finiteStoppedDensity κ (fun t => B t sample) γ g z u)) := by
  by_cases he : ∃ t : ℝ≥0, z ∈ localizationDomain γ t ∧
      loewnerRadius g t z = (2*z.im)*Real.exp (-u)
  · obtain ⟨t, hzt, hrt⟩ := he
    have hh : (fun n : ℕ => ENNReal.ofReal ((C n).value κ B sample)) =ᶠ[atTop]
        (fun _ => finiteStoppedDensity κ (fun t => B t sample) γ g z u) :=
      eventually_value_at_radius_general κ B sample h hz hu hc hb0 C hC hzt hrt
    exact tendsto_const_nhds.congr' hh.symm
  · have hset : {t : ℝ≥0 | z ∈ localizationDomain γ t ∧
        loewnerRadius g t z = (2*z.im)*Real.exp (-u)} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      intro t ht
      exact he ⟨t,ht⟩
    have htau : firstLiveRadiusStop γ g z u = (⊤ : ℝ≥0∞) := by
      simp only [firstLiveRadiusStop, hset, Set.image_empty, sInf_empty]
    rw [finiteStoppedDensity, htau, ite_eq_left rfl]
    have ha : 0 < 8/κ-1 := sub_pos.2 ((lt_div_iff₀ hκ.1).2 (by simpa using hκ.2))
    have hlim := hC.rpow_const_nhds_zero ha
    have hlim' : Tendsto (fun n : ℕ => ((2*z.im)*Real.exp (-u))^(-(1-κ/8)) *
        ((C n).angle)^(8/κ-1)) atTop (𝓝 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul hlim
    have hl : Tendsto (fun n : ℕ => (C n).value κ B sample) atTop (𝓝 0) := by
      apply squeeze_zero (fun n => (C n).value_nonneg κ B sample) _ hlim'
      intro n
      let D := C n
      have hs : loewnerAngleSine κ (fun t => B t sample) g (D.stopTime κ B sample) z = D.angle := by
        rcases D.source_terminal κ B sample h hz hu hc hb0 with hr | hs
        · exact False.elim (he ⟨⟨D.stopTime κ B sample,(D.bounds κ B sample).1⟩,
            D.source_live κ B sample h hz hu hc hb0, hr⟩)
        · exact hs
      exact D.angle_exit_bound κ B sample h hz hu hc hb0 hκ hs
    simpa only [ENNReal.ofReal_zero, Function.comp_def] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp hl

end SLEExactGauge.FiniteTilt

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge.FiniteTilt

lemma tendsto_setLIntegral_value {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) (κ : ℝ) (hκ : 0 < κ ∧ κ < 8)
    (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
    (hmaps : ∀ᵐ sample ∂P, IsLoewnerTraceUsing
      (fun t => Real.sqrt κ*B t.toNNReal sample) (γ sample) (g sample) (f sample))
    {z : ℂ} (hz : z ∈ halfPlane) {u : ℝ} (hu : 0 ≤ u)
    (C : ℕ → Cutoff z u) (hC : Tendsto (fun n => (C n).angle) atTop (𝓝 0)) (E : Set Ω) :
    Tendsto (fun n => ∫⁻ sample in E, ENNReal.ofReal ((C n).value κ B sample) ∂P) atTop
      (𝓝 (∫⁻ sample in E, finiteStoppedDensity κ (fun t => B t sample)
        (γ sample) (g sample) z u ∂P)) := by
  rcases eq_or_lt_of_le hu with rfl | hu
  · have he (n : ℕ) : (∫⁻ sample in E, ENNReal.ofReal ((C n).value κ B sample) ∂P) =
        ∫⁻ sample in E, finiteStoppedDensity κ (fun t => B t sample)
          (γ sample) (g sample) z 0 ∂P := by
      apply lintegral_congr_ae
      apply ae_restrict_of_ae
      filter_upwards [hmaps,hB.toIsPreBrownianReal.eval_zero_ae_eq_zero] with sample hm hb0
      rw [(C n).value_zero hz κ B sample hb0,finiteStoppedDensity_zero (κ := κ) (B := fun t => B t sample) hm hb0 hz]
    simp only [he]
    exact tendsto_const_nhds
  · let F := fun n sample => ENNReal.ofReal ((C n).value κ B sample)
    have hFm (n : ℕ) : AEMeasurable (F n) (P.restrict E) :=
      (ENNReal.measurable_ofReal.comp_aemeasurable
        ((C n).expectation hB κ hκ hz hu.le).1.aemeasurable).mono_measure Measure.restrict_le_self
    have hFb (n : ℕ) : ∀ᵐ sample ∂P.restrict E,
        F n sample ≤ ENNReal.ofReal (((2*z.im)*Real.exp (-u))^(-(1-κ/8))) := by
      apply ae_restrict_of_ae
      filter_upwards [hB.cont,hB.toIsPreBrownianReal.eval_zero_ae_eq_zero] with sample hc hb0
      exact ENNReal.ofReal_le_ofReal ((C n).value_bound κ hκ B sample hz hu hc hb0)
    have hFl : ∀ᵐ sample ∂P.restrict E, Tendsto (fun n => F n sample) atTop
        (𝓝 (finiteStoppedDensity κ (fun t => B t sample) (γ sample) (g sample) z u)) := by
      apply ae_restrict_of_ae
      filter_upwards [hmaps,hB.cont,hB.toIsPreBrownianReal.eval_zero_ae_eq_zero] with sample hm hc hb0
      exact tendsto_value_killed_general κ B sample hm hz hu hc hb0 C hC hκ
    have hfin : (∫⁻ _ : Ω in E, ENNReal.ofReal (((2*z.im)*Real.exp (-u))^(-(1-κ/8))) ∂P) ≠ ⊤ := by
      rw [lintegral_const]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
    exact tendsto_lintegral_of_dominated_convergence'
      (fun _ : Ω => ENNReal.ofReal (((2*z.im)*Real.exp (-u))^(-(1-κ/8)))) hFm hFb hfin hFl

end SLEExactGauge.FiniteTilt

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
open FiniteTilt BrownianPredictable

theorem finiteStoppedDensity_consistent {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ ∧ κ < 8)
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
    (_hγ : ∀ t, 0 ≤ t → AEMeasurable (fun sample => γ sample t) P)
    (hmaps : ∀ᵐ sample ∂P, IsLoewnerTraceUsing
      (fun t => Real.sqrt κ*B t.toNNReal sample) (γ sample) (g sample) (f sample))
    (z : ℂ) (hz : z ∈ halfPlane) (u v : ℝ) (hu : 0 ≤ u) (huv : u ≤ v)
    (A : Set Ω) (hA : NullMeasurableSet A P)
    (hstop : ∀ t : ℝ≥0, ∃ E : Set Ω, MeasurableSet[pastSigma B t] E ∧
      E =ᵐ[P] (A ∩ {sample | firstLiveRadiusStop (γ sample) (g sample) z u ≤ (t : ℝ≥0∞)} : Set Ω)) :
    (∫⁻ sample in A, finiteStoppedDensity κ (fun t => B t sample) (γ sample) (g sample) z v ∂P) =
      ∫⁻ sample in A, finiteStoppedDensity κ (fun t => B t sample) (γ sample) (g sample) z u ∂P := by
  let C := cutoffs hz v (hu.trans huv)
  let D := fun n => (C n).retarget hz huv
  have hv := tendsto_setLIntegral_value hB κ hκ γ g f hmaps hz (hu.trans huv) C
    (shrinkingAngle_tendsto z) A
  have hu' := tendsto_setLIntegral_value hB κ hκ γ g f hmaps hz hu D
    (shrinkingAngle_tendsto z) A
  have he (n : ℕ) : (∫⁻ sample in A, ENNReal.ofReal ((C n).value κ B sample) ∂P) =
      ∫⁻ sample in A, ENNReal.ofReal ((D n).value κ B sample) ∂P := by
    rw [← ofReal_integral_eq_lintegral_ofReal ((C n).expectation hB κ hκ hz (hu.trans huv)).1.integrableOn
      (Filter.Eventually.of_forall (fun sample => (C n).value_nonneg κ B sample)),
      ← ofReal_integral_eq_lintegral_ofReal ((D n).expectation hB κ hκ hz hu).1.integrableOn
      (Filter.Eventually.of_forall (fun sample => (D n).value_nonneg κ B sample))]
    congr 1
    exact (C n).retarget_setIntegral hB κ hκ hz hu huv γ g f hmaps A hA hstop
  exact tendsto_nhds_unique (hv.congr' (Filter.Eventually.of_forall he)) hu'

theorem conditionalRadiusApproachBound (κ : ℝ) (hκ : 0 < κ ∧ κ < 8) :
    ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (B : ℝ≥0 → Ω → ℝ) (_hB : IsBrownianReal B P)
      (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
      (_hγ : ∀ t, 0 ≤ t → AEMeasurable (fun sample => γ sample t) P)
      (_hmaps : ∀ᵐ sample ∂P, IsLoewnerTraceUsing
        (fun t => Real.sqrt κ*B t.toNNReal sample) (γ sample) (g sample) (f sample))
      (z : ℂ) (_hz : z ∈ halfPlane) (u v : ℝ) (_hu : 0 ≤ u) (_huv : u+1 ≤ v)
      (A : Set Ω) (_hA : NullMeasurableSet A P)
      (_hstop : ∀ t : ℝ≥0, ∃ E : Set Ω,
        MeasurableSet[pastSigma B t] E ∧
        E =ᵐ[P] (A ∩ {sample | firstLiveRadiusStop (γ sample) (g sample) z u ≤ (t : ℝ≥0∞)} : Set Ω)),
      P (A ∩ {sample | firstLiveRadiusStop (γ sample) (g sample) z v ≠ (⊤ : ℝ≥0∞)}) ≤
        ENNReal.ofReal (C * ((2*z.im)*Real.exp (-v))^(codimension κ)) *
          ∫⁻ sample in A, finiteStoppedDensity κ (fun t => B t sample) (γ sample) (g sample) z u ∂P := by
  obtain ⟨K,hK,hKb⟩ := Cutoff.targetValue_bound κ hκ
  refine ⟨K,hK,?_⟩
  intro Ω _ P _ B hB γ g f hγ hmaps z hz u v hu huv A hA hstop
  have hz0 : 0 < z.im := hz
  have hv : 0 < v := by linarith
  have huv' : u ≤ v := by linarith
  let C := cutoffs hz v hv.le
  let D := fun n => (C n).retarget hz huv'
  let F := fun n => A.indicator (fun sample => ENNReal.ofReal ((C n).barrier (timeShift n) κ B sample))
  let Y := fun sample => liminf (fun n => F n sample) atTop
  have hFm (n : ℕ) : AEMeasurable (F n) P :=
    (ENNReal.measurable_ofReal.comp_aemeasurable
      ((C n).barrier_aemeasurable hB (timeShift n) κ hκ (timeShift_pos n))).indicator₀ hA
  have hYm : AEMeasurable Y P := by
    dsimp only [Y]
    simp_rw [liminf_eq_iSup_iInf_of_nat]
    exact AEMeasurable.iSup (fun n => AEMeasurable.iInf (fun i => AEMeasurable.iInf (fun (_ : n ≤ i) => hFm i)))
  have hsub : (A ∩ {sample | firstLiveRadiusStop (γ sample) (g sample) z v ≠ (⊤ : ℝ≥0∞)} : Set Ω) ≤ᵐ[P]
      {sample | (1:ℝ≥0∞) ≤ Y sample} := by
    filter_upwards [hmaps,hB.cont,hB.toIsPreBrownianReal.eval_zero_ae_eq_zero] with sample hm hc hb0 hs
    have hh := barrier_tendsto_on_hit κ B sample hm hz hv hc hb0 hκ hs.2
    have he : Y sample = 1 := by
      dsimp only [Y,F]
      simp only [Set.indicator_of_mem hs.1]
      exact hh.liminf_eq
    exact he.ge
  have hexp (n : ℕ) : (∫⁻ sample, F n sample ∂P) ≤
      ENNReal.ofReal (K*((2*z.im)*Real.exp (-v))^(codimension κ)) *
        ∫⁻ sample in A, ENNReal.ofReal ((D n).value κ B sample) ∂P := by
    have hbi := ((C n).barrier_expectation hB (timeShift n) κ hκ (timeShift_pos n) hz hv γ g f hmaps).1
    have hti : Integrable ((C n).targetValue hz huv' (timeShift n) κ B) P := by
      apply (((D n).expectation hB κ hκ hz hu).1.const_mul
        (K*((2*z.im)*Real.exp (-v))^(codimension κ))).mono'
        ((C n).targetValue_aemeasurable hB hz huv' (timeShift n) κ hκ (timeShift_pos n)).aestronglyMeasurable
      filter_upwards [hB.cont,hB.toIsPreBrownianReal.eval_zero_ae_eq_zero] with sample hc hb0
      rw [Real.norm_eq_abs,abs_of_nonneg ((C n).targetValue_nonneg hz huv' (timeShift n) κ hκ (timeShift_pos n) B sample)]
      exact hKb hz hu huv (C n) B sample (timeShift n) (timeShift_pos n) hc hb0
    have hle := (C n).target_setIntegral_le hB (timeShift n) κ hκ (timeShift_pos n) hz hu huv
      γ g f hmaps A hA hstop
    rw [lintegral_indicator₀ hA]
    calc
      _ = ENNReal.ofReal (∫ sample in A, (C n).barrier (timeShift n) κ B sample ∂P) := by
        symm
        exact ofReal_integral_eq_lintegral_ofReal hbi.integrableOn (Eventually.of_forall
          (fun sample => (C n).barrier_nonneg (timeShift n) κ B sample hκ (timeShift_pos n)))
      _ ≤ ENNReal.ofReal (∫ sample in A, (C n).targetValue hz huv' (timeShift n) κ B sample ∂P) :=
        ENNReal.ofReal_le_ofReal hle
      _ = ∫⁻ sample in A, ENNReal.ofReal ((C n).targetValue hz huv' (timeShift n) κ B sample) ∂P :=
        ofReal_integral_eq_lintegral_ofReal hti.integrableOn (Eventually.of_forall
          (fun sample => (C n).targetValue_nonneg hz huv' (timeShift n) κ hκ (timeShift_pos n) B sample))
      _ ≤ ∫⁻ sample in A, ENNReal.ofReal (K*((2*z.im)*Real.exp (-v))^(codimension κ)) *
          ENNReal.ofReal ((D n).value κ B sample) ∂P := by
        apply lintegral_mono_ae
        apply ae_restrict_of_ae
        filter_upwards [hB.cont,hB.toIsPreBrownianReal.eval_zero_ae_eq_zero] with sample hc hb0
        rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ K*((2*z.im)*Real.exp (-v))^(codimension κ))]
        exact ENNReal.ofReal_le_ofReal (hKb hz hu huv (C n) B sample (timeShift n) (timeShift_pos n) hc hb0)
      _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have ht := tendsto_setLIntegral_value hB κ hκ γ g f hmaps hz hu D (shrinkingAngle_tendsto z) A
  have ht' := ENNReal.Tendsto.const_mul ht (Or.inr (ENNReal.ofReal_ne_top (r := K*((2*z.im)*Real.exp (-v))^(codimension κ))))
  calc
    _ ≤ P {sample | (1:ℝ≥0∞) ≤ Y sample} := measure_mono_ae hsub
    _ ≤ ∫⁻ sample, Y sample ∂P := by
      simpa only [div_one] using meas_ge_le_lintegral_div hYm (by norm_num : (1:ℝ≥0∞) ≠ 0) (by norm_num : (1:ℝ≥0∞) ≠ ⊤)
    _ ≤ liminf (fun n => ∫⁻ sample, F n sample ∂P) atTop := lintegral_liminf_le' hFm
    _ ≤ _ := (liminf_le_liminf (Eventually.of_forall hexp)).trans_eq ht'.liminf_eq

end SLEExactGauge

end

end

section
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SLEExactGauge
open BrownianPredictable FiniteTilt

theorem conditionalCenteredInverseAngleBound (κ : ℝ) (hκ : 0 < κ ∧ κ < 8) :
    ∃ C : ℝ, 0 < C ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (B : ℝ≥0 → Ω → ℝ) (_hB : IsBrownianReal B P)
      (γ : Ω → ℝ → ℂ) (g f : Ω → ℝ → ℂ → ℂ)
      (_hγ : ∀ t, 0 ≤ t → AEMeasurable (fun sample => γ sample t) P)
      (_hmaps : ∀ᵐ sample ∂P, IsLoewnerTraceUsing
        (fun t => Real.sqrt κ*B t.toNNReal sample) (γ sample) (g sample) (f sample))
      (z : ℂ) (_hz : z ∈ halfPlane) (u v : ℝ) (_hu : 0 ≤ u) (_huv : u+1 ≤ v)
      (A : Set Ω) (_hA : NullMeasurableSet A P)
      (_hstop : ∀ t : ℝ≥0, ∃ E : Set Ω,
        MeasurableSet[pastSigma B t] E ∧
        E =ᵐ[P] (A ∩ {sample | firstLiveRadiusStop (γ sample) (g sample) z u ≤ (t : ℝ≥0∞)} : Set Ω)),
      (∫⁻ sample in A, radiusStoppedInverseAngle κ B γ g z v sample
          ∂finiteCenteredMeasure κ P B γ g z v) ≤
        ENNReal.ofReal C * (finiteCenteredMeasure κ P B γ g z u) A := by
  obtain ⟨C,hC,hbound⟩ := conditionalRadiusApproachBound κ hκ
  refine ⟨C,hC,?_⟩
  intro Ω _ P _ B hB γ g f hγ hmaps z hz u v hu huv A hA hstop
  have hv : 0 < v := by linarith
  have hz0 : 0 < z.im := hz
  let M₀ := ENNReal.ofReal ((2*z.im)^(-codimension κ)*(z.im/‖z‖)^(8/κ-1))
  let K := ENNReal.ofReal (((2*z.im)*Real.exp (-v))^(-codimension κ)) / M₀
  let H : Set Ω := {sample | firstLiveRadiusStop (γ sample) (g sample) z v ≠ (⊤ : ℝ≥0∞)}
  have hmpos := localizationInitialGreen_pos κ hz
  have hm0 : M₀ ≠ 0 := (ENNReal.ofReal_pos.2 hmpos).ne'
  have hd := finiteStoppedDensity_aemeasurable κ hκ B hB γ g f hmaps z hz v hv
  have hdm : AEMeasurable (fun sample => finiteStoppedDensity κ (fun t => B t sample)
      (γ sample) (g sample) z v / M₀) P := hd.div_const M₀
  have hdf : ∀ᵐ sample ∂P, finiteStoppedDensity κ (fun t => B t sample)
      (γ sample) (g sample) z v / M₀ < (⊤ : ℝ≥0∞) := Filter.Eventually.of_forall
    (fun sample => ENNReal.div_lt_top (finiteStoppedDensity_lt_top κ _ _ _ z v).ne hm0)
  have he : (fun sample => (finiteStoppedDensity κ (fun t => B t sample)
      (γ sample) (g sample) z v / M₀) * radiusStoppedInverseAngle κ B γ g z v sample) =ᵐ[P]
      H.indicator (fun _ => K) := by
    filter_upwards [hmaps,hB.cont] with sample hm hc
    have hh := finiteStoppedDensity_mul_inverseAngle κ B γ g f z hz v sample hm hc
    rw [show (finiteStoppedDensity κ (fun t => B t sample) (γ sample) (g sample) z v / M₀) *
      radiusStoppedInverseAngle κ B γ g z v sample = (finiteStoppedDensity κ (fun t => B t sample)
      (γ sample) (g sample) z v * radiusStoppedInverseAngle κ B γ g z v sample) / M₀ by
        simp only [div_eq_mul_inv]; ac_rfl, hh]
    classical
    by_cases hhit : sample ∈ H
    · simp only [H] at hhit
      simp only [H, Set.indicator_of_mem hhit, K]
    · simp only [H] at hhit
      simp only [H, Set.indicator_of_notMem hhit, ENNReal.zero_div]
  have heleft : (∫⁻ sample in A, radiusStoppedInverseAngle κ B γ g z v sample
      ∂finiteCenteredMeasure κ P B γ g z v) ≤ K*P (A∩H) := by
    change (∫⁻ sample in A, _ ∂P.withDensity _) ≤ _
    rw [setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable₀' P A hdm.restrict _
      (ae_restrict_of_ae hdf)]
    simp only [Pi.mul_apply]
    rw [lintegral_congr_ae (ae_restrict_of_ae he)]
    calc
      _ ≤ K*(P.restrict A) H := lintegral_indicator_const_le H K
      _ = _ := by rw [Measure.restrict_apply₀' hA,inter_comm]
  have hemeasure : (finiteCenteredMeasure κ P B γ g z u) A =
      M₀⁻¹ * ∫⁻ sample in A, finiteStoppedDensity κ (fun t => B t sample)
        (γ sample) (g sample) z u ∂P := by
    rw [finiteCenteredMeasure,withDensity_apply₀ _ hA]
    simp_rw [ENNReal.div_eq_inv_mul]
    exact lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hm0)
  have hcancel : ENNReal.ofReal (((2*z.im)*Real.exp (-v))^(-codimension κ)) *
      ENNReal.ofReal (C*((2*z.im)*Real.exp (-v))^(codimension κ)) = ENNReal.ofReal C := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)]
    congr 1
    calc
      _ = C*(((2*z.im)*Real.exp (-v))^(-codimension κ)*((2*z.im)*Real.exp (-v))^(codimension κ)) := by ring
      _ = C := by rw [← Real.rpow_add (by positivity),neg_add_cancel,Real.rpow_zero,mul_one]
  calc
    _ ≤ K*P (A∩H) := heleft
    _ ≤ K*(ENNReal.ofReal (C*((2*z.im)*Real.exp (-v))^(codimension κ)) *
        ∫⁻ sample in A, finiteStoppedDensity κ (fun t => B t sample) (γ sample) (g sample) z u ∂P) :=
      mul_le_mul' le_rfl (hbound P B hB γ g f hγ hmaps z hz u v hu huv A hA hstop)
    _ = _ := by
      rw [hemeasure]
      dsimp only [K]
      rw [div_eq_mul_inv]
      calc
        _ = (ENNReal.ofReal (((2*z.im)*Real.exp (-v))^(-codimension κ)) *
            ENNReal.ofReal (C*((2*z.im)*Real.exp (-v))^(codimension κ))) *
            (M₀⁻¹ * ∫⁻ sample in A, finiteStoppedDensity κ (fun t => B t sample) (γ sample) (g sample) z u ∂P) := by ac_rfl
        _ = _ := by rw [hcancel]

end SLEExactGauge

end

end

end OAI

import Mathlib
import OAI.Probability.SphericalField.Control.Filtration

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
open Matrix
open scoped InnerProductSpace

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
lemma indep_eventuallyMeasurable_left {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) {m n : MeasurableSpace Ω} (h : Indep m n μ) :
    Indep (eventuallyMeasurableSpace m (ae μ)) n μ := by
  rw [Indep_iff] at h ⊢
  rintro A B ⟨A', hA', hAA'⟩ hB
  rw [measure_congr (hAA'.inter (Filter.EventuallyEq.refl (ae μ) B)), measure_congr hAA']
  exact h A' B hA' hB

lemma nullSigma_le_eventuallyMeasurable (P : Measure BrownianPath)
    (m : MeasurableSpace BrownianPath) :
    nullSigma P ≤ eventuallyMeasurableSpace m (ae P) := by
  apply MeasurableSpace.generateFrom_le
  intro A hA
  exact ⟨∅, MeasurableSet.empty, ae_eq_empty.mpr hA⟩

@[instance_reducible] def rawBrownianSigma (s : ℝ≥0) : MeasurableSpace BrownianPath :=
  ⨆ r : {r : ℝ≥0 // r ≤ s},
    MeasurableSpace.comap (brownianEval r.val) (borel ℝ)

lemma rawBrownianSigma_le (s : ℝ≥0) : rawBrownianSigma s ≤ (inferInstance : MeasurableSpace BrownianPath) := by
  apply iSup_le
  intro r
  exact (brownianEval_measurable r.val).comap_le

lemma rawBrownianSigma_le_past_comap (s : ℝ≥0) :
    rawBrownianSigma s ≤
      MeasurableSpace.comap (fun ω (r : Set.Iic s) => brownianEval r.val ω) inferInstance := by
  apply iSup_le
  intro r
  rintro A ⟨B, hB, rfl⟩
  exact ⟨(fun f : Set.Iic s → ℝ => f r) ⁻¹' B, (measurable_pi_apply r) hB, rfl⟩

lemma usualBrownianSigma_le_ae_raw (P : Measure BrownianPath) (t : Time)
    (s : ℝ≥0) (hts : (t : ℝ) < s) :
    usualBrownianSigma P t ≤ eventuallyMeasurableSpace (rawBrownianSigma s) (ae P) := by
  apply (iInf_le _ (⟨s, hts⟩ : {s : ℝ≥0 // (t : ℝ) < s})).trans
  exact sup_le le_eventuallyMeasurableSpace (nullSigma_le_eventuallyMeasurable P _)

lemma brownian_future_indep_raw (P : Measure BrownianPath)
    (hB : IsBrownianReal brownianEval P) (s u : ℝ≥0) :
    Indep (rawBrownianSigma s)
      (MeasurableSpace.comap (fun ω => brownianEval (s+u) ω - brownianEval s ω) (borel ℝ)) P := by
  have h := (hB.toIsPreBrownianReal.indepFun_shift s).symm.comp
    measurable_id (measurable_pi_apply u)
  exact indep_of_indep_of_le_left h (rawBrownianSigma_le_past_comap s)

lemma brownian_future_indep_usual_earlier (P : Measure BrownianPath)
    (hB : IsBrownianReal brownianEval P) (t : Time) (s u : ℝ≥0)
    (hts : (t : ℝ) < s) :
    Indep (usualBrownianSigma P t)
      (MeasurableSpace.comap (fun ω => brownianEval (s+u) ω - brownianEval s ω) (borel ℝ)) P :=
  indep_of_indep_of_le_left
    (indep_eventuallyMeasurable_left P (brownian_future_indep_raw P hB s u))
    (usualBrownianSigma_le_ae_raw P t s hts)

lemma indep_setIntegral_eq_mul_null {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) {X : Ω → ℝ} {A : Set Ω}
    (hI : Indep m (MeasurableSpace.comap X (borel ℝ)) P)
    (hX : AEMeasurable X P) (hA : MeasurableSet[m] A) (hAn : NullMeasurableSet A P)
    (f : ℝ →ᵇ ℝ) :
    (∫ ω in A, f (X ω) ∂P) = P.real A * ∫ ω, f (X ω) ∂P := by
  calc
    _ = ∫ ω, id (A.indicator (1 : Ω → ℝ) ω) * f (X ω) ∂P := by
      rw [← integral_indicator₀ hAn]
      congr with ω
      by_cases hω : ω ∈ A <;> simp [hω]
    _ = _ := by
      simp only [Pi.one_def]
      rw [IndepFun.integral_fun_comp_mul_comp
        (hI.indicator_indepFun 1 hA)
        ((aemeasurable_indicator_const_iff 1).2 hAn) hX
        measurable_id.aestronglyMeasurable f.continuous.measurable.aestronglyMeasurable]
      simp only [id_eq, integral_indicator₀ hAn, integral_const, smul_eq_mul, mul_one,
        measureReal_def, Measure.restrict_apply_univ]

lemma indep_comap_of_ae_tendsto {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hm : ∀ A, MeasurableSet[m] A → NullMeasurableSet A P)
    {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    (hX : ∀ n, AEMeasurable (X n) P) (hY : AEMeasurable Y P)
    (hI : ∀ n, Indep m (MeasurableSpace.comap (X n) (borel ℝ)) P)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω))) :
    Indep m (MeasurableSpace.comap Y (borel ℝ)) P := by
  apply (Indep_iff_IndepSets _ _ P).2
  apply indepSets_comap_of_bcf (fun A hA => hm A hA) hY
  intro A hA f
  have hall := tendsto_integral_of_dominated_convergence (fun _ : Ω => ‖f‖)
    (fun n => (f.continuous.measurable.comp_aemeasurable (hX n)).aestronglyMeasurable)
    (integrable_const _) (fun n => Filter.Eventually.of_forall fun ω => f.norm_coe_le_norm _)
    (hlim.mono fun ω hω => f.continuous.continuousAt.tendsto.comp hω)
  have hres := tendsto_integral_of_dominated_convergence (μ := P.restrict A)
    (fun _ : Ω => ‖f‖)
    (fun n => (f.continuous.measurable.comp_aemeasurable (hX n)).aestronglyMeasurable.restrict)
    (integrable_const _) (fun n => Filter.Eventually.of_forall fun ω => f.norm_coe_le_norm _)
    ((ae_restrict_of_ae hlim).mono fun ω hω => f.continuous.continuousAt.tendsto.comp hω)
  apply tendsto_nhds_unique hres
  convert hall.const_mul (P.real A) using 1
  ext n
  exact indep_setIntegral_eq_mul_null P (hI n) (hX n) hA (hm A hA) f

lemma brownian_increment_indep_usual (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) (t : Time) (r : ℝ≥0) (htr : (t : ℝ) < r) :
    Indep (usualBrownianSigma P t)
      (MeasurableSpace.comap (fun ω => brownianEval r ω -
        brownianEval ⟨t.val, t.property.1⟩ ω) (borel ℝ)) P := by
  let t₀ : ℝ≥0 := ⟨t.val, t.property.1⟩
  have ht₀r : t₀ < r := htr
  obtain ⟨s, -, hs, hlim⟩ := exists_seq_strictAnti_tendsto' ht₀r
  apply indep_comap_of_ae_tendsto P (fun A hA =>
    (usualBrownianSigma_le_completion P t A hA))
    (X := fun n ω => brownianEval r ω - brownianEval (s n) ω)
    (fun n => ((brownianEval_measurable r).sub (brownianEval_measurable (s n))).aemeasurable)
    (((brownianEval_measurable r).sub (brownianEval_measurable t₀)).aemeasurable)
  · intro n
    have hI := brownian_future_indep_usual_earlier P hB t (s n) (r-s n) (hs n).1
    rwa [add_tsub_cancel_of_le (hs n).2.le] at hI
  · exact Filter.Eventually.of_forall fun ω => tendsto_const_nhds.sub
      (ω.continuous.continuousAt.tendsto.comp hlim)

def clipControl (L : ℝ) (v : Time → BrownianPath → ℝ) : Time → BrownianPath → ℝ :=
  fun t ω => max (-L) (min L (v t ω))

lemma progressive_clipControl (P : Measure BrownianPath) {v : Time → BrownianPath → ℝ}
    (hv : Progressive P v) (L : ℝ) : Progressive P (clipControl L v) := by
  intro t
  exact measurable_const.max (measurable_const.min (hv t))

lemma abs_clip_le {L : ℝ} (hL : 0 ≤ L) (x : ℝ) : |max (-L) (min L x)| ≤ L := by
  apply abs_le.mpr
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

lemma clip_cost_gain {L : ℝ} (hL : 0 ≤ L) (x : ℝ) :
    L * |x - max (-L) (min L x)| ≤ (x^2 - (max (-L) (min L x))^2)/2 := by
  by_cases hx : x ≤ -L
  · have hxL : x ≤ L := hx.trans (by linarith)
    rw [min_eq_right hxL, max_eq_left hx, abs_of_nonpos (by linarith)]
    nlinarith [sq_nonneg (x+L)]
  · by_cases hLx : L ≤ x
    · rw [min_eq_left hLx, max_eq_right (by linarith : -L ≤ L),
        abs_of_nonneg (by linarith : 0 ≤ x-L)]
      nlinarith [sq_nonneg (x-L)]
    · rw [min_eq_right (le_of_not_ge hLx), max_eq_right (le_of_not_ge hx)]
      simp

lemma clip_sq_le {L : ℝ} (hL : 0 ≤ L) (x : ℝ) :
    (max (-L) (min L x))^2 ≤ x^2 := by
  have h := clip_cost_gain hL x
  nlinarith [mul_nonneg hL (abs_nonneg (x - max (-L) (min L x)))]

lemma pathControlCost_clip_le (m : Trial) {L : ℝ} (hL : 0 ≤ L)
    (v : Time → BrownianPath → ℝ) (ω : BrownianPath) :
    pathControlCost m (clipControl L v) ω ≤ pathControlCost m v ω := by
  apply lintegral_mono
  intro t
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (clip_sq_le hL _) (m.nonneg t))

end SphericalPerceptron
end
end

end OAI

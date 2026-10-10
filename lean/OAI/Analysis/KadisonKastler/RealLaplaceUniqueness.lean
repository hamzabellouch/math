import OAI.Analysis.KadisonKastler.LocalLaplaceUniqueness
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Measure.OpenPos

namespace OAI

/-! # Local Laplace uniqueness for the signed averaging coefficient -/

namespace KadisonKastler

open MeasureTheory ProbabilityTheory Filter Set

noncomputable section

private theorem exp_positivePart_integrable (f : ℝ → ℝ) (hf : Measurable f) (s : ℝ)
    (hi : Integrable (fun t => Real.exp (s * t) * f t)) :
    Integrable (fun t => Real.exp (s * t) * max (f t) 0) := by
  apply hi.norm.mono' (by fun_prop)
  exact Eventually.of_forall fun t => by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_mul,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (max_le (le_abs_self _) (abs_nonneg _))
      (Real.exp_pos _).le

private theorem exp_density_integrable (f : ℝ → ℝ) (hf : Measurable f)
    (hf0 : ∀ t, 0 ≤ f t) (s : ℝ)
    (hi : Integrable (fun t => Real.exp (s * t) * f t)) :
    Integrable (fun t => Real.exp (s * t)) (volume.withDensity fun t => ENNReal.ofReal (f t)) := by
  apply (integrable_withDensity_iff_integrable_smul' hf.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mpr
  simpa only [ENNReal.toReal_ofReal (hf0 _), smul_eq_mul, mul_comm] using hi

private theorem mgf_density (f : ℝ → ℝ) (hf : Measurable f)
    (hf0 : ∀ t, 0 ≤ f t) (s : ℝ) :
    mgf id (volume.withDensity fun t => ENNReal.ofReal (f t)) s =
      ∫ t, Real.exp (s * t) * f t := by
  rw [mgf, integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  exact Eventually.of_forall fun t => by simp only [ENNReal.toReal_ofReal (hf0 t),
    smul_eq_mul, id_eq, mul_comm]

/-- A real coefficient with an open interval of exponential integrability is
zero almost everywhere if all its Laplace values in that interval vanish. -/
theorem ae_zero_of_local_laplace (f : ℝ → ℝ) (hf : Measurable f)
    {a : ℝ} (ha : 0 < a)
    (hi : ∀ s ∈ Ioo (-a) a, Integrable (fun t => Real.exp (s * t) * f t))
    (hz : ∀ s ∈ Ioo (-a) a, (∫ t, Real.exp (s * t) * f t) = 0) :
    f =ᵐ[volume] 0 := by
  let p : ℝ → ℝ := fun t => max (f t) 0
  let q : ℝ → ℝ := fun t => max (-f t) 0
  have hp : Measurable p := hf.max measurable_const
  have hq : Measurable q := hf.neg.max measurable_const
  have hp0 (t) : 0 ≤ p t := le_max_right _ _
  have hq0 (t) : 0 ≤ q t := le_max_right _ _
  have hzero : (0 : ℝ) ∈ Ioo (-a) a := ⟨by linarith, ha⟩
  have hpi (s) (hs : s ∈ Ioo (-a) a) : Integrable (fun t => Real.exp (s * t) * p t) :=
    exp_positivePart_integrable f hf s (hi s hs)
  have hqi (s) (hs : s ∈ Ioo (-a) a) : Integrable (fun t => Real.exp (s * t) * q t) := by
    apply exp_positivePart_integrable (fun t => -f t) hf.neg s
    apply (hi s hs).neg.congr
    filter_upwards [] with t
    simp only [Pi.neg_apply, mul_neg]
  have hpI : Integrable p := by simpa only [zero_mul, Real.exp_zero, one_mul] using hpi 0 hzero
  have hqI : Integrable q := by simpa only [zero_mul, Real.exp_zero, one_mul] using hqi 0 hzero
  let μ := volume.withDensity (fun t => ENNReal.ofReal (p t))
  let ν := volume.withDensity (fun t => ENNReal.ofReal (q t))
  let : IsFiniteMeasure μ := isFiniteMeasure_withDensity
    ((lintegral_ofReal_ne_top_iff_integrable hp.aestronglyMeasurable
      (Eventually.of_forall hp0)).mpr hpI)
  let : IsFiniteMeasure ν := isFiniteMeasure_withDensity
    ((lintegral_ofReal_ne_top_iff_integrable hq.aestronglyMeasurable
      (Eventually.of_forall hq0)).mpr hqI)
  have hdiff (t) : f t = p t - q t := by
    dsimp [p, q]
    rcases le_total 0 (f t) with ht | ht
    · rw [max_eq_left ht, max_eq_right (neg_nonpos.mpr ht), sub_zero]
    · rw [max_eq_right ht, max_eq_left (neg_nonneg.mpr ht)]
      ring
  have hm : μ = ν := finiteMeasure_eq_of_local_laplace ha
    (fun s hs => exp_density_integrable p hp hp0 s (hpi s hs))
    (fun s hs => exp_density_integrable q hq hq0 s (hqi s hs)) (by
      intro s hs
      rw [mgf_density p hp hp0, mgf_density q hq hq0]
      have he := hz s hs
      have hf' : (fun t => Real.exp (s * t) * f t) =
          (fun t => Real.exp (s * t) * p t - Real.exp (s * t) * q t) := by
        funext t
        rw [hdiff, mul_sub]
      rw [hf', integral_sub (hpi s hs) (hqi s hs)] at he
      exact sub_eq_zero.mp he)
  have he := (withDensity_eq_iff_of_sigmaFinite hp.ennreal_ofReal.aemeasurable
    hq.ennreal_ofReal.aemeasurable).mp hm
  filter_upwards [he] with t ht
  have hpq : p t = q t := by
    have hh := congrArg ENNReal.toReal ht
    simpa only [ENNReal.toReal_ofReal (hp0 t), ENNReal.toReal_ofReal (hq0 t)] using hh
  simpa only [Pi.zero_apply, hpq, sub_self] using hdiff t

/-- For continuous coefficients, the conclusion holds at every real parameter. -/
theorem zero_of_local_laplace (f : ℝ → ℝ) (hf : Continuous f)
    {a : ℝ} (ha : 0 < a)
    (hi : ∀ s ∈ Ioo (-a) a, Integrable (fun t => Real.exp (s * t) * f t))
    (hz : ∀ s ∈ Ioo (-a) a, (∫ t, Real.exp (s * t) * f t) = 0) :
    f = 0 :=
  (Continuous.ae_eq_iff_eq volume hf continuous_const).mp
    (ae_zero_of_local_laplace f hf.measurable ha hi hz)

end

end KadisonKastler

end OAI

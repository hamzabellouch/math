import Mathlib

namespace OAI

open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal

namespace Problem367

theorem preBrownian_tendstoInMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {s : ℕ → ℝ≥0} {t : ℝ≥0} (hs : Tendsto s atTop (𝓝 t)) :
    TendstoInMeasure P (fun n => B (s n)) atTop (B t) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have hmean (n : ℕ) : (∫ ω, B (s n) ω - B t ω ∂P) = 0 := by
    rw [integral_sub (hB.integrable_eval _) (hB.integrable_eval _),
      hB.integral_eval, hB.integral_eval, sub_self]
  have hvar (n : ℕ) : variance (B (s n) - B t) P = dist (s n) t := by
    rw [(hB.hasLaw_sub (s n) t).variance_eq, variance_id_gaussianReal]
    rfl
  have hbound (n : ℕ) : P {ω | ε ≤ ‖B (s n) ω - B t ω‖} ≤
      ENNReal.ofReal (dist (s n) t / ε ^ 2) := by
    simpa only [hvar, Pi.sub_apply, hmean, sub_zero, Real.norm_eq_abs] using
      meas_ge_le_variance_div_sq (hB.hasLaw_sub (s n) t).hasGaussianLaw.memLp_two hε
  have hlim : Tendsto (fun n => ENNReal.ofReal (dist (s n) t / ε ^ 2))
      atTop (𝓝 0) := by
    simpa [Function.comp_def] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      ((hs.dist (tendsto_const_nhds : Tendsto (fun _ : ℕ => t) atTop (𝓝 t))).div_const
        (ε ^ 2))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => bot_le) hbound

theorem preBrownian_ae_eq_of_approximating_sequence
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B Y : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hY : ∀ᵐ ω ∂P, Continuous (fun t => Y t ω))
    {s : ℕ → ℝ≥0} {t : ℝ≥0} (hs : Tendsto s atTop (𝓝 t))
    (hseq : ∀ n, B (s n) =ᵐ[P] Y (s n)) : B t =ᵐ[P] Y t := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n => B (s n) ω) atTop (𝓝 (Y t ω)) := by
    filter_upwards [hY, ae_all_iff.mpr hseq] with ω hcont heq
    have ht := (hcont.tendsto t).comp hs
    simpa only [Function.comp_def, fun n => heq n] using ht
  exact tendstoInMeasure_ae_unique (preBrownian_tendstoInMeasure hB hs)
    (tendstoInMeasure_of_tendsto_ae
      (fun n => (hB.aemeasurable (s n)).aestronglyMeasurable) hlim)

theorem preBrownian_ae_eq_of_dense
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B Y : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hY : ∀ᵐ ω ∂P, Continuous (fun t => Y t ω))
    {D : Set ℝ≥0} (hD : Dense D) (heq : ∀ t ∈ D, B t =ᵐ[P] Y t) :
    ∀ t, B t =ᵐ[P] Y t := by
  intro t
  obtain ⟨s, hsD, hst⟩ := mem_closure_iff_seq_limit.mp (hD t)
  exact preBrownian_ae_eq_of_approximating_sequence hB hY hst
    (fun n => heq (s n) (hsD n))

theorem isBrownianReal_of_dense_agreement
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B Y : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hY : ∀ᵐ ω ∂P, Continuous (fun t => Y t ω))
    {D : Set ℝ≥0} (hD : Dense D) (heq : ∀ t ∈ D, B t =ᵐ[P] Y t) :
    IsBrownianReal Y P :=
  ⟨hB.congr (preBrownian_ae_eq_of_dense hB hY hD heq), hY⟩

end Problem367

end OAI

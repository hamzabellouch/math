import OAI.Analysis.KadisonSimilarity.Representation.ScalarLocalizationApproximation
import OAI.Analysis.KadisonSimilarity.Representation.VectorL2Multiplication
import OAI.Analysis.KadisonSimilarity.Representation.L2Localization
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! Measurable localizations are strong limits of uniformly bounded continuous
scalar multipliers. Consequently their commutant is already determined by the
continuous scalar multipliers. -/

noncomputable section
namespace KadisonSimilarity
open MeasureTheory Filter
open scoped Topology ENNReal

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]
  [MeasurableSpace X] [BorelSpace X] (μ : Measure X)
  [IsFiniteMeasure μ] [μ.Regular]

/-- One bounded sequence works almost everywhere for a fixed measurable set. -/
theorem exists_continuous_indicator_ae_sequence (s : Set X) (hs : MeasurableSet s) :
    ∃ f : ℕ → C(X, ℂ), (∀ n x, ‖f n x‖ ≤ 1) ∧
      ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop
        (𝓝 (s.indicator (fun _ => (1 : ℂ)) x)) := by
  have hex (n : ℕ) := exists_continuous_indicator_eLpNorm_approx μ s hs
    (ε := (2 : ℝ≥0∞)⁻¹ ^ n) (pow_ne_zero n (ENNReal.inv_ne_zero.mpr (by norm_num)))
  choose f hf he using hex
  have ht : Tendsto
      (fun n => eLpNorm (fun x => f n x - s.indicator (fun _ => (1 : ℂ)) x) 2 μ)
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (2 : ℝ≥0∞)⁻¹ < 1))
      (fun _ => bot_le) he
  obtain ⟨u, _, hu⟩ := (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) ht).exists_seq_tendsto_ae
  exact ⟨fun n => f (u n), fun n => hf (u n), hu⟩

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [T2Space X] [IsFiniteMeasure μ] [μ.Regular] [CompleteSpace H] in
/-- Dominated convergence for bounded scalar multipliers on vector-valued L². -/
theorem continuous_scalar_tendsto_localization
    (s : Set X) (hs : MeasurableSet s) (f : ℕ → C(X, ℂ))
    (hf : ∀ n x, ‖f n x‖ ≤ 1)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop
      (𝓝 (s.indicator (fun _ => (1 : ℂ)) x))) (ξ : Lp H 2 μ) :
    Tendsto (fun n => VectorL2.continuousL2Mul μ (f n) ξ) atTop
      (𝓝 (l2Localization μ s hs ξ)) := by
  let d (n : ℕ) : Lp H 2 μ :=
    VectorL2.continuousL2Mul μ (f n) ξ - l2Localization μ s hs ξ
  have hda (n : ℕ) : ∀ᵐ x ∂μ,
      d n x = (f n x - s.indicator (fun _ => (1 : ℂ)) x) • ξ x := by
    filter_upwards [Lp.coeFn_sub (VectorL2.continuousL2Mul μ (f n) ξ)
      (l2Localization μ s hs ξ), VectorL2.continuousL2Mul_ae μ (f n) ξ,
      l2Localization_ae μ s hs ξ] with x hd hm hl
    change (VectorL2.continuousL2Mul μ (f n) ξ - l2Localization μ s hs ξ) x = _
    rw [hd, Pi.sub_apply, hm, hl]
    by_cases hx : x ∈ s <;> simp [hx, sub_smul]
  have hint : Integrable (fun x => 4 * ‖ξ x‖ ^ 2) μ :=
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable ξ)).mp
      (Lp.memLp ξ)).const_mul 4
  have hb (n : ℕ) : ∀ᵐ x ∂μ, ‖‖d n x‖ ^ 2‖ ≤ 4 * ‖ξ x‖ ^ 2 := by
    filter_upwards [hda n] with x hx
    rw [hx, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hi : ‖s.indicator (fun _ => (1 : ℂ)) x‖ ≤ 1 := by
      by_cases hx : x ∈ s <;> simp [hx]
    have hh : ‖f n x - s.indicator (fun _ => (1 : ℂ)) x‖ ≤ 2 :=
      (norm_sub_le _ _).trans (by linarith [hf n x])
    have hm := mul_le_mul_of_nonneg_right hh (norm_nonneg (ξ x))
    nlinarith [norm_nonneg (f n x - s.indicator (fun _ => (1 : ℂ)) x),
      sq_nonneg (2 * ‖ξ x‖ - ‖f n x - s.indicator (fun _ => (1 : ℂ)) x‖ * ‖ξ x‖)]
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => ‖d n x‖ ^ 2) atTop (𝓝 0) := by
    filter_upwards [ht, eventually_countable_forall.mpr hda] with x hx hd
    have hzero : Tendsto
        (fun n => (f n x - s.indicator (fun _ => (1 : ℂ)) x) • ξ x) atTop (𝓝 0) := by
      simpa only [sub_self, zero_smul] using (hx.sub (tendsto_const_nhds (x := s.indicator (fun _ => (1 : ℂ)) x))).smul_const (ξ x)
    simpa only [hd, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using hzero.norm.pow 2
  have hsq : Tendsto (fun n => ‖d n‖ ^ 2) atTop (𝓝 0) := by
    simpa only [Pi.pow_apply, ← l2_norm_sq_eq_integral, integral_zero] using
      (tendsto_integral_of_dominated_convergence (fun x => 4 * ‖ξ x‖ ^ 2)
        (fun n => (Lp.aestronglyMeasurable (d n)).norm.pow 2) hint hb hlim)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  change Tendsto (fun n => Real.sqrt (‖d n‖ ^ 2)) atTop (𝓝 (Real.sqrt 0)) at h
  have he : (fun n => Real.sqrt (‖d n‖ ^ 2)) = (fun n => ‖d n‖) :=
    funext fun n => Real.sqrt_sq (norm_nonneg (d n))
  rw [he, Real.sqrt_zero] at h
  exact h

omit [CompleteSpace H] in
/-- Commutation with continuous scalar functions implies commutation with every
measurable localization, on the actual vector-valued L² space. -/
theorem commutes_localizations_of_continuous
    (T : Lp H 2 μ →L[ℂ] Lp H 2 μ)
    (hT : ∀ f : C(X, ℂ),
      T * VectorL2.continuousL2Mul μ f = VectorL2.continuousL2Mul μ f * T)
    (s : Set X) (hs : MeasurableSet s) :
    T * l2Localization μ s hs = l2Localization μ s hs * T := by
  obtain ⟨f, hf, ht⟩ := exists_continuous_indicator_ae_sequence μ s hs
  apply ContinuousLinearMap.ext
  intro ξ
  have h₁ := T.continuous.continuousAt.tendsto.comp
    (continuous_scalar_tendsto_localization μ s hs f hf ht ξ)
  have h₂ := continuous_scalar_tendsto_localization μ s hs f hf ht (T ξ)
  have he (n : ℕ) : T (VectorL2.continuousL2Mul μ (f n) ξ) =
      VectorL2.continuousL2Mul μ (f n) (T ξ) :=
    congrArg (fun S : Lp H 2 μ →L[ℂ] Lp H 2 μ => S ξ) (hT (f n))
  exact tendsto_nhds_unique h₁ (h₂.congr (fun n => (he n).symm))

end KadisonSimilarity

end

end OAI

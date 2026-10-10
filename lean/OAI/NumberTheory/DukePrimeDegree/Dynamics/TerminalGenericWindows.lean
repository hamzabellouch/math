import OAI.NumberTheory.DukePrimeDegree.Dynamics.RealFlowWindows

namespace OAI

/-!
# Generic control on a fixed terminal fraction of a real orbit

Polynomial shearing changes uniformly little on a sufficiently short
fixed terminal fraction.  Prefix genericity controls that fraction
with the explicit loss `2 / delta`.  The fraction is chosen after the
finite test accuracy, and is independent of the pair and stopping time.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BoundedContinuousFunction

namespace DukePrimeDegree

theorem terminal_window_average_error
    (F : ℝ → ℝ) (c ε δ T : ℝ)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hT : 0 < T) (hε : 0 ≤ ε)
    (hint : ∀ a b, IntervalIntegrable F volume a b)
    (hfull : |T⁻¹ * (∫ t in (0 : ℝ)..T, F t) - c| ≤ ε)
    (hprefix : |((1 - δ) * T)⁻¹ *
      (∫ t in (0 : ℝ)..((1 - δ) * T), F t) - c| ≤ ε) :
    |(δ * T)⁻¹ * (∫ t in ((1 - δ) * T)..T, F t) - c| ≤ 2 * ε / δ := by
  let a := (1 - δ) * T
  have ha : 0 < a := mul_pos (sub_pos.mpr hδ1) hT
  have haT : a ≤ T := by dsimp only [a]; nlinarith
  have hdT : 0 < δ * T := mul_pos hδ hT
  have heq : (δ * T)⁻¹ * (∫ t in a..T, F t) - c =
      (δ * T)⁻¹ * (T * (T⁻¹ * (∫ t in (0 : ℝ)..T, F t) - c) -
        a * (a⁻¹ * (∫ t in (0 : ℝ)..a, F t) - c)) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 a) (hint a T)]
    dsimp only [a]
    field_simp [ne_of_gt hδ, ne_of_gt hT, ne_of_gt (sub_pos.mpr hδ1)]
    ring
  rw [heq, abs_mul, abs_of_pos (inv_pos.mpr hdT)]
  calc
    _ ≤ (δ * T)⁻¹ * (|T * (T⁻¹ * (∫ t in (0 : ℝ)..T, F t) - c)| +
        |a * (a⁻¹ * (∫ t in (0 : ℝ)..a, F t) - c)|) := by
      apply mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hdT.le)
      simpa only [sub_zero, zero_sub, abs_neg] using
        (abs_sub_le (T * (T⁻¹ * (∫ t in (0 : ℝ)..T, F t) - c)) 0
          (a * (a⁻¹ * (∫ t in (0 : ℝ)..a, F t) - c)))
    _ = (δ * T)⁻¹ * (T * |T⁻¹ * (∫ t in (0 : ℝ)..T, F t) - c| +
        a * |a⁻¹ * (∫ t in (0 : ℝ)..a, F t) - c|) := by
      rw [abs_mul, abs_mul, abs_of_pos hT, abs_of_pos ha]
    _ ≤ (δ * T)⁻¹ * (T * ε + a * ε) := by
      apply mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hdT.le)
      exact add_le_add (mul_le_mul_of_nonneg_left hfull hT.le)
        (mul_le_mul_of_nonneg_left hprefix ha.le)
    _ ≤ (δ * T)⁻¹ * (2 * T * ε) := by
      apply mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hdT.le)
      nlinarith
    _ = 2 * ε / δ := by field_simp

/-- One prefix-generic set controls every sufficiently late terminal
window, including a stopping time depending on both initial points. -/
theorem terminal_window_control_of_prefix_control
    {Y : Type*} (U : ℝ → Y → Y) (f : Y → ℝ)
    (hint : ∀ x a b, IntervalIntegrable (fun t => f (U t x)) volume a b)
    (G : Set Y) (c ε δ R : ℝ)
    (hε : 0 ≤ ε) (hδ : 0 < δ) (hδ1 : δ < 1) (hR : 0 < R)
    (hgood : ∀ x ∈ G, ∀ T ≥ R,
      |T⁻¹ * (∫ t in (0 : ℝ)..T, f (U t x)) - c| ≤ ε) :
    ∀ x ∈ G, ∀ T ≥ R / (1 - δ),
      |(δ * T)⁻¹ * (∫ t in ((1 - δ) * T)..T, f (U t x)) - c| ≤ 2 * ε / δ := by
  intro x hx T hT
  have hden : 0 < 1 - δ := sub_pos.mpr hδ1
  have hprefix : R ≤ (1 - δ) * T := by
    have he := (div_le_iff₀ hden).mp hT
    linarith
  have hTpos : 0 < T := by nlinarith
  have hTR : R ≤ T := by nlinarith
  exact terminal_window_average_error (fun t => f (U t x)) c ε δ T
    hδ hδ1 hTpos hε (hint x) (hgood x hx T hTR)
    (hgood x hx ((1 - δ) * T) hprefix)

/-- Actual full-real-flow ergodicity supplies the fixed good set. No
ergodicity of an arbitrarily chosen discrete time is assumed. -/
theorem exists_uniform_terminal_flow_generic_set
    {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    [MulAction (Multiplicative ℝ) Y] [ContinuousSMul (Multiplicative ℝ) Y]
    (μ : Measure Y) [IsProbabilityMeasure μ] [ErgodicSMul (Multiplicative ℝ) Y μ]
    (f : Y →ᵇ ℝ) (ε δ η : ℝ)
    (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1) (hη : 0 < η) :
    ∃ G : Set Y, MeasurableSet G ∧ μ Gᶜ ≤ ENNReal.ofReal η ∧
      ∃ R : ℝ, 0 < R ∧ ∀ x ∈ G, ∀ T ≥ R,
        |(δ * T)⁻¹ * (∫ t in ((1 - δ) * T)..T,
          f (realActionTime t x)) - ∫ y, f y ∂μ| ≤ ε := by
  have hsmall : 0 < ε * δ / 2 := by positivity
  obtain ⟨G, hG, hGμ, R, hR, hgood⟩ :=
    exists_uniform_real_flow_generic_set μ f (ε * δ / 2) η hsmall hη
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  refine ⟨G, hG, hGμ, R / (1 - δ), div_pos hRpos (sub_pos.mpr hδ1), ?_⟩
  intro x hx T hT
  have he := terminal_window_control_of_prefix_control realActionTime f
    (fun x a b => ((continuous_flow_observable f).comp
      (continuous_id.prodMk continuous_const)).intervalIntegrable a b)
    G (∫ y, f y ∂μ) (ε * δ / 2) δ R hsmall.le hδ hδ1 hRpos hgood x hx T hT
  convert he using 1
  field_simp

end DukePrimeDegree

end

end OAI

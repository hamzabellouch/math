import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.CutoffError
import OAI.Analysis.RieszRectifiability.Kernel.EnergyFromTruncations

namespace OAI

/-!
# Integral estimates for cutoff energies

Bounded multipliers preserve the square-integrability needed for cutoff estimates. An
almost-everywhere diameter bound makes the near-pair error estimate global, while the
fractional energy identity separates the bilinear contribution from the cutoff error.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function
open scoped NNReal

theorem bounded_multiplier_memLp {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (w χ : X → ℝ) (hw : Measurable w) (hχ : Measurable χ)
    (hL2 : MemLp w 2 μ) (H : ℝ) (hH : ∀ᵐ x ∂μ, ‖χ x‖ ≤ H) :
    MemLp (fun x => χ x * w x) 2 μ := by
  apply (hL2.norm.const_mul H).mono' ((hχ.mul hw).aestronglyMeasurable)
  filter_upwards [hH] with x hx
  rw [Pi.mul_apply, norm_mul]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

theorem cutoffError_integrable_and_bound_of_ae_diameter {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (w χ : Ambient d → ℝ) (hw : Measurable w) (hL2 : MemLp w 2 μ)
    (L : ℝ≥0) (hχ : LipschitzWith L χ) (r : ℝ) (hr : 0 < r)
    (hdiam : ∀ᵐ q ∂μ.prod μ, dist q.1 q.2 ≤ r) :
    Integrable (fun q : Ambient d × Ambient d => cutoffError (p + 1) w χ q.1 q.2) (μ.prod μ) ∧
      (∫ q : Ambient d × Ambient d, |cutoffError (p + 1) w χ q.1 q.2| ∂μ.prod μ) ≤
        (L : ℝ) ^ 2 * (2 * (C * 2 ^ (p + 1) * 2 ^ p * r)) * (∫ x, w x ^ 2 ∂μ) := by
  have hmem : ∀ᵐ q ∂μ.prod μ, q ∈ nearPairSet r := by
    simpa only [nearPairSet, mem_ofPred_eq, mem_closedBall, dist_comm] using! hdiam
  have heq := Measure.restrict_eq_self_of_ae_mem hmem
  simpa only [IntegrableOn, heq] using!
    near_cutoffError_integrable_and_bound p C μ hg w χ hw hL2 L hχ r hr

theorem cutoff_fractionalEnergy_identity {d : ℕ} (m : ℕ)
    (w χ : Ambient d → ℝ) (x y : Ambient d) :
    fractionalPairEnergy m (fun z => χ z * w z) x y =
      fractionalBilinear m w (fun z => χ z ^ 2 * w z) x y + cutoffError m w χ x y := by
  simpa only [fractionalPairEnergy, fractionalBilinear, cutoffError, add_div, mul_div_assoc] using!
    congrArg (fun t : ℝ => t / dist x y ^ (m + 1))
      (cutoff_square_eq_pairing_add_error (w x) (w y) (χ x) (χ y))

theorem truncated_cutoff_integral_identity {d : ℕ} (m : ℕ)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ]
    (w χ : Ambient d → ℝ) (hw : Measurable w) (hχ : Measurable χ)
    (hcut : MemLp (fun x => χ x * w x) 2 μ)
    (herr : Integrable (fun q : Ambient d × Ambient d => cutoffError m w χ q.1 q.2) (μ.prod μ))
    (ε : ℝ) (hε : 0 < ε) :
    IntegrableOn (fun q : Ambient d × Ambient d =>
      fractionalBilinear m w (fun x => χ x ^ 2 * w x) q.1 q.2)
      {q | ε < dist q.1 q.2} (μ.prod μ) ∧
      (∫ q in {q : Ambient d × Ambient d | ε < dist q.1 q.2},
        fractionalPairEnergy m (fun x => χ x * w x) q.1 q.2 ∂μ.prod μ) =
      (∫ q in {q : Ambient d × Ambient d | ε < dist q.1 q.2},
        fractionalBilinear m w (fun x => χ x ^ 2 * w x) q.1 q.2 ∂μ.prod μ) +
      (∫ q in {q : Ambient d × Ambient d | ε < dist q.1 q.2},
        cutoffError m w χ q.1 q.2 ∂μ.prod μ) := by
  have hE := truncated_fractionalEnergy_integrable μ m (fun x => χ x * w x)
    (hχ.mul hw) hcut ε hε
  have heq : (fun q : Ambient d × Ambient d =>
      fractionalBilinear m w (fun x => χ x ^ 2 * w x) q.1 q.2) =
      fun q => fractionalPairEnergy m (fun x => χ x * w x) q.1 q.2 -
        cutoffError m w χ q.1 q.2 := by
    funext q
    linarith [cutoff_fractionalEnergy_identity m w χ q.1 q.2]
  have hpair : IntegrableOn (fun q : Ambient d × Ambient d =>
      fractionalBilinear m w (fun x => χ x ^ 2 * w x) q.1 q.2)
      {q | ε < dist q.1 q.2} (μ.prod μ) := by
    rw [heq]
    exact hE.sub herr.restrict
  refine ⟨hpair, ?_⟩
  simp_rw [cutoff_fractionalEnergy_identity]
  exact integral_add hpair herr.restrict

theorem cutoff_energy_from_interior_pairing_bound {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (w χ : Ambient d → ℝ) (hw : Measurable w) (hL2 : MemLp w 2 μ)
    (L : ℝ≥0) (hχ : LipschitzWith L χ) (H : ℝ) (hH : ∀ᵐ x ∂μ, ‖χ x‖ ≤ H)
    (r : ℝ) (hr : 0 < r) (hdiam : ∀ᵐ q ∂μ.prod μ, dist q.1 q.2 ≤ r)
    (A : ℝ) (hA : ∀ ε : ℝ, 0 < ε →
      (∫ q in {q : Ambient d × Ambient d | ε < dist q.1 q.2},
        fractionalBilinear (p + 1) w (fun x => χ x ^ 2 * w x) q.1 q.2 ∂μ.prod μ) ≤ A) :
    Integrable (fun q : Ambient d × Ambient d =>
      fractionalPairEnergy (p + 1) (fun x => χ x * w x) q.1 q.2) (μ.prod μ) ∧
      (∫ q : Ambient d × Ambient d,
        fractionalPairEnergy (p + 1) (fun x => χ x * w x) q.1 q.2 ∂μ.prod μ) ≤
        A + (L : ℝ) ^ 2 * (2 * (C * 2 ^ (p + 1) * 2 ^ p * r)) * (∫ x, w x ^ 2 ∂μ) := by
  obtain ⟨herr, herrorBound⟩ := cutoffError_integrable_and_bound_of_ae_diameter
    p C μ hg w χ hw hL2 L hχ r hr hdiam
  have hcut := bounded_multiplier_memLp μ w χ hw hχ.continuous.measurable hL2 H hH
  apply fractionalEnergy_integrable_of_uniform_bound μ (p + 1) (fun x => χ x * w x)
    (hχ.continuous.measurable.mul hw) hcut
  intro ε hε
  rw [(truncated_cutoff_integral_identity (p + 1) μ w χ hw hχ.continuous.measurable
    hcut herr ε hε).2]
  apply add_le_add (hA ε hε)
  calc
    _ ≤ ∫ q in {q : Ambient d × Ambient d | ε < dist q.1 q.2},
        |cutoffError (p + 1) w χ q.1 q.2| ∂μ.prod μ :=
      integral_mono herr.restrict herr.abs.restrict (fun _ => le_abs_self _)
    _ ≤ ∫ q : Ambient d × Ambient d, |cutoffError (p + 1) w χ q.1 q.2| ∂μ.prod μ :=
      setIntegral_le_integral herr.abs (Filter.Eventually.of_forall fun _ => abs_nonneg _)
    _ ≤ _ := herrorBound

theorem cutoff_energy_from_integrable_interior_pairing {d : ℕ} (p : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ] (hg : GlobalUpperGrowth (p + 1) C μ)
    (w χ : Ambient d → ℝ) (hw : Measurable w) (hL2 : MemLp w 2 μ)
    (L : ℝ≥0) (hχ : LipschitzWith L χ)
    (r : ℝ) (hr : 0 < r) (hdiam : ∀ᵐ q ∂μ.prod μ, dist q.1 q.2 ≤ r)
    (hpair : Integrable (fun q : Ambient d × Ambient d =>
      fractionalBilinear (p + 1) w (fun x => χ x ^ 2 * w x) q.1 q.2) (μ.prod μ))
    (A : ℝ) (hA : (∫ q : Ambient d × Ambient d,
      fractionalBilinear (p + 1) w (fun x => χ x ^ 2 * w x) q.1 q.2 ∂μ.prod μ) ≤ A) :
    Integrable (fun q : Ambient d × Ambient d =>
      fractionalPairEnergy (p + 1) (fun x => χ x * w x) q.1 q.2) (μ.prod μ) ∧
      (∫ q : Ambient d × Ambient d,
        fractionalPairEnergy (p + 1) (fun x => χ x * w x) q.1 q.2 ∂μ.prod μ) ≤
        A + (L : ℝ) ^ 2 * (2 * (C * 2 ^ (p + 1) * 2 ^ p * r)) * (∫ x, w x ^ 2 ∂μ) := by
  obtain ⟨herr, herrorBound⟩ := cutoffError_integrable_and_bound_of_ae_diameter
    p C μ hg w χ hw hL2 L hχ r hr hdiam
  constructor
  · simpa only [cutoff_fractionalEnergy_identity] using! hpair.add herr
  · simp_rw [cutoff_fractionalEnergy_identity]
    rw [integral_add hpair herr]
    exact add_le_add hA ((integral_mono herr herr.abs (fun _ => le_abs_self _)).trans herrorBound)

end

end RieszRectifiability

end OAI

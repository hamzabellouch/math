import OAI.Analysis.IrrationalRotation.Analysis.UniformQuantization
import OAI.Analysis.IrrationalRotation.Sampling.DigitAveraging

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Invariant233.UniformQuantization

local instance : IsProbabilityMeasure (volume.restrict (Ico (0 : ℝ) 1)) :=
  ⟨by simp⟩

theorem quantize_fiber_mass (q : ℕ) [NeZero q] (a : Fin q) :
    (volume.restrict (Ico (0 : ℝ) 1)).real {x | quantize q x = a} =
      1 / (q : ℝ) := by
  have hmass := map_quantize_singleton q a
  rw [Measure.map_apply (measurable_quantize q) (measurableSet_singleton a)] at hmass
  unfold Measure.real
  rw [show (volume.restrict (Ico (0 : ℝ) 1)) {x | quantize q x = a} =
      (q : ℝ≥0∞)⁻¹ from hmass]
  simp [one_div]

theorem binAverage_eq_interval (q : ℕ) [NeZero q] (h : ℝ → ℝ) (a : Fin q) :
    binAverage q h a =
      (q : ℝ) * ∫ x in Ico ((a : ℝ) / q) (((a : ℝ) + 1) / q), h x := by
  unfold binAverage
  congr 1
  change (∫ x, h x ∂(volume.restrict (Ico (0 : ℝ) 1)).restrict
    (quantize q ⁻¹' {a})) = _
  rw [Measure.restrict_restrict ((measurable_quantize q) (measurableSet_singleton a))]
  rw [preimage_singleton_inter_unit]

theorem map_withDensity_quantize (q : ℕ) [NeZero q] {h : ℝ → ℝ}
    (hh : Integrable h (volume.restrict (Ico (0 : ℝ) 1)))
    (hnonneg : ∀ᵐ x ∂volume.restrict (Ico (0 : ℝ) 1), 0 ≤ h x) :
    ((volume.restrict (Ico (0 : ℝ) 1)).withDensity (fun x => ENNReal.ofReal (h x))).map
      (quantize q) =
      (PMF.uniformOfFintype (Fin q)).toMeasure.withDensity
        (fun a => ENNReal.ofReal (binAverage q h a)) := by
  simpa only [map_quantize_uniform, binAverage] using
    DigitAveraging.map_withDensity_eq_digit_density (Nat.pos_of_ne_zero (NeZero.ne q))
      (measurable_quantize q) (quantize_fiber_mass q) hh hnonneg

theorem integral_binAverage_energy_le (q : ℕ) [NeZero q] {h : ℝ → ℝ}
    (hh : MemLp h 2 (volume.restrict (Ico (0 : ℝ) 1))) :
    (∫ a, (binAverage q h a - 1) ^ 2 ∂(PMF.uniformOfFintype (Fin q)).toMeasure) ≤
      ∫ x, (h x - 1) ^ 2 ∂volume.restrict (Ico (0 : ℝ) 1) := by
  simpa only [map_quantize_uniform, binAverage] using
    DigitAveraging.integral_digit_energy_le (Nat.pos_of_ne_zero (NeZero.ne q))
      (measurable_quantize q) (quantize_fiber_mass q) hh

theorem binAverage_nonneg (q : ℕ) [NeZero q] {h : ℝ → ℝ}
    (hh : ∀ᵐ x ∂volume.restrict (Ico (0 : ℝ) 1), 0 ≤ h x) (a : Fin q) :
    0 ≤ binAverage q h a := DigitAveraging.digit_average_nonneg hh a

theorem integral_binAverage (q : ℕ) [NeZero q] {h : ℝ → ℝ}
    (hh : Integrable h (volume.restrict (Ico (0 : ℝ) 1))) :
    (∫ a, binAverage q h a ∂(PMF.uniformOfFintype (Fin q)).toMeasure) =
      ∫ x, h x ∂volume.restrict (Ico (0 : ℝ) 1) := by
  rw [← map_quantize_uniform q,
    DigitAveraging.integral_map_eq_uniform_sum (measurable_quantize q) (quantize_fiber_mass q)]
  exact DigitAveraging.digit_average_mean (Nat.pos_of_ne_zero (NeZero.ne q))
    (measurable_quantize q) hh

theorem binAverage_le (q : ℕ) [NeZero q] {h : ℝ → ℝ} {B : ℝ}
    (hh : Integrable h (volume.restrict (Ico (0 : ℝ) 1)))
    (hB : ∀ᵐ x ∂volume.restrict (Ico (0 : ℝ) 1), h x ≤ B) (a : Fin q) :
    binAverage q h a ≤ B :=
  DigitAveraging.digit_average_le (Nat.pos_of_ne_zero (NeZero.ne q))
    (quantize_fiber_mass q) hh hB a

end Invariant233.UniformQuantization

end

end OAI

import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.CutoffEnergyIntegral
import OAI.Analysis.RieszRectifiability.Kernel.CappedBilinearKernel

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function
open scoped NNReal

def cappedPairEnergy {d : ℕ} (m : ℕ) (ε : ℝ) (w : Ambient d → ℝ)
    (q : Ambient d × Ambient d) : ℝ :=
  (w q.1 - w q.2) ^ 2 * cappedInverseDistancePow (m + 1) ε q

def cappedWeightedDifference {d : ℕ} (m : ℕ) (ε : ℝ) (w : Ambient d → ℝ)
    (q : Ambient d × Ambient d) : ℝ :=
  Real.sqrt (cappedInverseDistancePow (m + 1) ε q) * (w q.1 - w q.2)

theorem cappedWeightedDifference_sq {d : ℕ} (m : ℕ) (ε : ℝ) (w : Ambient d → ℝ)
    (q : Ambient d × Ambient d) :
    cappedWeightedDifference m ε w q ^ 2 = cappedPairEnergy m ε w q := by
  rw [cappedWeightedDifference, mul_pow, Real.sq_sqrt (cappedInverseDistancePow_nonneg (m + 1) ε q)]
  exact mul_comm _ _

theorem cappedWeightedDifference_mul {d : ℕ} (m : ℕ) (ε : ℝ) (w g : Ambient d → ℝ)
    (q : Ambient d × Ambient d) :
    cappedWeightedDifference m ε w q * cappedWeightedDifference m ε g q =
      (w q.1 - w q.2) * cappedTestKernel m ε g q := by
  unfold cappedWeightedDifference cappedTestKernel
  have heq : Real.sqrt (cappedInverseDistancePow (m + 1) ε q) ^ 2 =
      cappedInverseDistancePow (m + 1) ε q := Real.sq_sqrt (cappedInverseDistancePow_nonneg (m + 1) ε q)
  calc
    _ = Real.sqrt (cappedInverseDistancePow (m + 1) ε q) ^ 2 *
        ((w q.1 - w q.2) * (g q.1 - g q.2)) := by ring
    _ = _ := by rw [heq]; ring

theorem cappedWeightedDifference_memLp {d : ℕ} (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ] (w : Ambient d → ℝ) (hw : MemLp w 2 μ) :
    MemLp (cappedWeightedDifference m ε w) 2 (μ.prod μ) := by
  have hdiff : MemLp (fun q : Ambient d × Ambient d => w q.1 - w q.2) 2 (μ.prod μ) :=
    (hw.comp_fst μ).sub (hw.comp_snd μ)
  have hcap := (cappedInverseDistancePow_lipschitz (X := Ambient d) m ε hε).continuous
  have hsqrt : Measurable (fun q : Ambient d × Ambient d =>
      Real.sqrt (cappedInverseDistancePow (m + 1) ε q)) := hcap.sqrt.measurable
  apply (hdiff.norm.const_mul (Real.sqrt ((ε ^ (m + 1))⁻¹))).mono'
    (hsqrt.aestronglyMeasurable.mul hdiff.aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro q
  change ‖Real.sqrt (cappedInverseDistancePow (m + 1) ε q) * (w q.1 - w q.2)‖ ≤
    Real.sqrt ((ε ^ (m + 1))⁻¹) * ‖w q.1 - w q.2‖
  rw [norm_mul, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply Real.sqrt_le_sqrt
  exact (le_abs_self _).trans (cappedInverseDistancePow_bound (m + 1) ε hε q)

theorem cappedPairEnergy_integrable {d : ℕ} (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ] (w : Ambient d → ℝ) (hw : MemLp w 2 μ) :
    Integrable (cappedPairEnergy m ε w) (μ.prod μ) := by
  simpa only [cappedWeightedDifference_sq] using!
    (cappedWeightedDifference_memLp m ε hε μ w hw).integrable_sq

theorem capped_bilinear_cauchy_schwarz {d : ℕ} (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ] (w g : Ambient d → ℝ)
    (hw : MemLp w 2 μ) (hg : MemLp g 2 μ) :
    (∫ q : Ambient d × Ambient d, (w q.1 - w q.2) * cappedTestKernel m ε g q ∂μ.prod μ) ^ 2 ≤
      (∫ q, cappedPairEnergy m ε w q ∂μ.prod μ) * (∫ q, cappedPairEnergy m ε g q ∂μ.prod μ) := by
  simpa only [cappedWeightedDifference_mul, cappedWeightedDifference_sq] using!
    integral_mul_cauchy_schwarz_sq (μ.prod μ) (cappedWeightedDifference m ε w)
      (cappedWeightedDifference m ε g) (cappedWeightedDifference_memLp m ε hε μ w hw)
      (cappedWeightedDifference_memLp m ε hε μ g hg)

theorem cappedPairEnergy_le_fractional {d : ℕ} (m : ℕ) (ε : ℝ)
    (w : Ambient d → ℝ) (q : Ambient d × Ambient d) :
    cappedPairEnergy m ε w q ≤ fractionalPairEnergy m w q.1 q.2 := by
  by_cases hdiag : q.1 = q.2
  · simp only [cappedPairEnergy, fractionalPairEnergy, hdiag, sub_self,
      zero_pow two_ne_zero, zero_mul, zero_div, le_refl]
  · have hd : 0 < dist q.1 q.2 := dist_pos.mpr hdiag
    unfold cappedPairEnergy fractionalPairEnergy
    rw [div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    exact inv_anti₀ (pow_pos hd _) (pow_le_pow_left₀ hd.le (le_max_right _ _) _)

theorem capped_bilinear_variational_bound {d : ℕ} (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ] (w g : Ambient d → ℝ)
    (hw : MemLp w 2 μ) (hg : MemLp g 2 μ)
    (henergy : Integrable (fun q : Ambient d × Ambient d => fractionalPairEnergy m w q.1 q.2) (μ.prod μ))
    (E : ℝ) (hE : (∫ q : Ambient d × Ambient d, fractionalPairEnergy m w q.1 q.2 ∂μ.prod μ) ≤ E) :
    (∫ q : Ambient d × Ambient d, (w q.1 - w q.2) * cappedTestKernel m ε g q ∂μ.prod μ) ^ 2 ≤
      E * (∫ q, cappedPairEnergy m ε g q ∂μ.prod μ) := by
  have hcap : (∫ q, cappedPairEnergy m ε w q ∂μ.prod μ) ≤ E := by
    apply (integral_mono (cappedPairEnergy_integrable m ε hε μ w hw) henergy
      (fun q => cappedPairEnergy_le_fractional m ε w q)).trans hE
  exact (capped_bilinear_cauchy_schwarz m ε hε μ w g hw hg).trans
    (mul_le_mul_of_nonneg_right hcap (integral_nonneg fun q =>
      mul_nonneg (sq_nonneg _) (cappedInverseDistancePow_nonneg (m + 1) ε q)))

end

end RieszRectifiability

end OAI

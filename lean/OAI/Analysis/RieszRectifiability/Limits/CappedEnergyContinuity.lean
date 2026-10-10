import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.TestStepApproximation
import OAI.Analysis.RieszRectifiability.Kernel.CappedEnergy

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function Filter Topology
open scoped NNReal

theorem cappedWeightedDifference_sub {d : ℕ} (m : ℕ) (ε : ℝ)
    (f g : Ambient d → ℝ) (q : Ambient d × Ambient d) :
    cappedWeightedDifference m ε f q - cappedWeightedDifference m ε g q =
      cappedWeightedDifference m ε (fun x => f x - g x) q := by
  unfold cappedWeightedDifference
  ring

theorem capped_self_bilinear_eq_energy {d : ℕ} (m : ℕ) (ε : ℝ)
    (f : Ambient d → ℝ) (q : Ambient d × Ambient d) :
    (f q.1 - f q.2) * cappedTestKernel m ε f q = cappedPairEnergy m ε f q := by
  unfold cappedTestKernel cappedPairEnergy
  ring

theorem cappedPairEnergy_L2_bound {d : ℕ} (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ] (w : Ambient d → ℝ) (hw : MemLp w 2 μ) :
    (∫ q, cappedPairEnergy m ε w q ∂μ.prod μ) ≤
      (4 * μ.real univ * (ε ^ (m + 1))⁻¹) * ∫ x, w x ^ 2 ∂μ := by
  have hx : Integrable (fun q : Ambient d × Ambient d => w q.1 ^ 2) (μ.prod μ) :=
    hw.integrable_sq.comp_fst μ
  have hy : Integrable (fun q : Ambient d × Ambient d => w q.2 ^ 2) (μ.prod μ) :=
    hw.integrable_sq.comp_snd μ
  have hdom := ((hx.const_mul 2).add (hy.const_mul 2)).mul_const ((ε ^ (m + 1))⁻¹)
  calc
    _ ≤ ∫ q : Ambient d × Ambient d, (2 * w q.1 ^ 2 + 2 * w q.2 ^ 2) *
        (ε ^ (m + 1))⁻¹ ∂μ.prod μ := by
      apply integral_mono (cappedPairEnergy_integrable m ε hε μ w hw) hdom
      intro q
      change (w q.1 - w q.2) ^ 2 * cappedInverseDistancePow (m + 1) ε q ≤ _
      apply mul_le_mul
      · change (w q.1 - w q.2) ^ 2 ≤ 2 * w q.1 ^ 2 + 2 * w q.2 ^ 2
        nlinarith [sq_nonneg (w q.1 + w q.2)]
      · exact (le_abs_self _).trans (cappedInverseDistancePow_bound (m + 1) ε hε q)
      · exact cappedInverseDistancePow_nonneg _ _ _
      · change 0 ≤ 2 * w q.1 ^ 2 + 2 * w q.2 ^ 2
        positivity
    _ = _ := by
      rw [integral_mul_const, integral_add (hx.const_mul 2) (hy.const_mul 2)]
      simp only [integral_const_mul, integral_fun_fst (fun x => w x ^ 2),
        integral_fun_snd (fun x => w x ^ 2), smul_eq_mul]
      ring

theorem cappedWeightedDifference_L2_tendsto {d : ℕ} (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ]
    (f : ℕ → Ambient d → ℝ) (g : Ambient d → ℝ)
    (hf : ∀ k, MemLp (f k) 2 μ) (hg : MemLp g 2 μ)
    (herror : Tendsto (fun k => ∫ x, (f k x - g x) ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => (cappedWeightedDifference_memLp m ε hε μ (f k) (hf k)).toLp
      (cappedWeightedDifference m ε (f k))) atTop
      (𝓝 ((cappedWeightedDifference_memLp m ε hε μ g hg).toLp (cappedWeightedDifference m ε g))) := by
  apply L2_tendsto_of_squared_error (μ.prod μ) (fun k => cappedWeightedDifference m ε (f k))
    (cappedWeightedDifference m ε g)
    (fun k => cappedWeightedDifference_memLp m ε hε μ (f k) (hf k))
    (cappedWeightedDifference_memLp m ε hε μ g hg)
  simp_rw [cappedWeightedDifference_sub, cappedWeightedDifference_sq]
  apply squeeze_zero (fun k => integral_nonneg fun q =>
    mul_nonneg (sq_nonneg _) (cappedInverseDistancePow_nonneg (m + 1) ε q))
    (fun k => cappedPairEnergy_L2_bound m ε hε μ (fun x => f k x - g x) ((hf k).sub hg))
  simpa only [mul_zero] using! herror.const_mul (4 * μ.real univ * (ε ^ (m + 1))⁻¹)

theorem capped_energy_tendsto_of_L2_error {d : ℕ} (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ]
    (f : ℕ → Ambient d → ℝ) (g : Ambient d → ℝ)
    (hf : ∀ k, MemLp (f k) 2 μ) (hg : MemLp g 2 μ)
    (herror : Tendsto (fun k => ∫ x, (f k x - g x) ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ q, cappedPairEnergy m ε (f k) q ∂μ.prod μ) atTop
      (𝓝 (∫ q, cappedPairEnergy m ε g q ∂μ.prod μ)) := by
  have h := (cappedWeightedDifference_L2_tendsto m ε hε μ f g hf hg herror).norm.pow 2
  simpa only [toLp_norm_sq_eq_integral, cappedWeightedDifference_sq] using! h

theorem capped_pairing_tendsto_of_L2_error {d : ℕ} (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ]
    (f : ℕ → Ambient d → ℝ) (g : Ambient d → ℝ)
    (hf : ∀ k, MemLp (f k) 2 μ) (hg : MemLp g 2 μ)
    (herror : Tendsto (fun k => ∫ x, (f k x - g x) ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ q : Ambient d × Ambient d,
      (g q.1 - g q.2) * cappedTestKernel m ε (f k) q ∂μ.prod μ) atTop
      (𝓝 (∫ q, cappedPairEnergy m ε g q ∂μ.prod μ)) := by
  have hconv := cappedWeightedDifference_L2_tendsto m ε hε μ f g hf hg herror
  have h := (tendsto_const_nhds (x :=
    (cappedWeightedDifference_memLp m ε hε μ g hg).toLp (cappedWeightedDifference m ε g))).inner
      (𝕜 := ℝ) hconv
  simpa only [toLp_inner_eq_integral, cappedWeightedDifference_mul, capped_self_bilinear_eq_energy] using! h

end

end RieszRectifiability

end OAI

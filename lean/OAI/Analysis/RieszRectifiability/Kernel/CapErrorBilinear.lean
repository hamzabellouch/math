import Mathlib
import OAI.Analysis.RieszRectifiability.Foundations.CapErrorRows
import OAI.Analysis.RieszRectifiability.Packing.SchurBilinear

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function

theorem scalar_cap_error_bilinear_integrable_and_bound {d : ℕ} (m : ℕ) (C : ℝ)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ] (hgrowth : GlobalUpperGrowth m C μ)
    (e : Ambient d) (ε : ℝ) (hε : 0 < ε)
    (f g : Ambient d → ℝ) (hfm : Measurable f) (hgm : Measurable g)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun q : Ambient d × Ambient d => f q.1 * g q.2 *
      (scalarCappedRieszKernel m e ε q - scalarTruncatedKernel m e ε q)) (μ.prod μ) ∧
    |∫ q : Ambient d × Ambient d, f q.1 * g q.2 *
      (scalarCappedRieszKernel m e ε q - scalarTruncatedKernel m e ε q) ∂μ.prod μ| ≤
      (‖e‖ * (C * 2 ^ m)) * Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, g x ^ 2 ∂μ) := by
  let k := closedNearCapWeight (d := d) m ε
  let W := fun q : Ambient d × Ambient d => |f q.1| * |g q.2| * k q
  let E := fun q : Ambient d × Ambient d => f q.1 * g q.2 *
    (scalarCappedRieszKernel m e ε q - scalarTruncatedKernel m e ε q)
  have hC : 0 ≤ C * 2 ^ m := mul_nonneg hgrowth.1 (by positivity)
  obtain ⟨hW, hWsq⟩ := schur_bilinear_integrable_and_sq_bound μ k
    (closedNearCapWeight_measurable m ε) (closedNearCapWeight_nonneg m ε hε)
    (closedNearCapWeight_symm m ε)
    (fun x => (closedNearCapWeight_row_integrable_and_bound m C μ hgrowth ε hε x).1)
    (C * 2 ^ m) hC
    (fun x => (closedNearCapWeight_row_integrable_and_bound m C μ hgrowth ε hε x).2)
    (fun x => |f x|) (fun x => |g x|) hfm.abs hgm.abs hf.abs hg.abs
  simp only [sq_abs] at hWsq
  have hW0 (q : Ambient d × Ambient d) : 0 ≤ W q :=
    mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (closedNearCapWeight_nonneg m ε hε q)
  have hpoint (q : Ambient d × Ambient d) : |E q| ≤ ‖e‖ * W q := by
    dsimp only [E, W]
    rw [abs_mul, abs_mul]
    calc
      _ ≤ (|f q.1| * |g q.2|) * (‖e‖ * k q) :=
        mul_le_mul_of_nonneg_left (scalarCappedRieszKernel_hard_error m e ε hε q)
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = _ := by ring
  have hEm : Measurable E :=
    ((hfm.comp measurable_fst).mul (hgm.comp measurable_snd)).mul
      ((scalarCappedRieszKernel_continuous m e ε hε).measurable.sub
        (scalarTruncatedKernel_measurable m e ε))
  have hE : Integrable E (μ.prod μ) := by
    apply (hW.const_mul ‖e‖).mono' hEm.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun q => by
      simpa only [Real.norm_eq_abs] using! hpoint q
  have habs : |∫ q, E q ∂μ.prod μ| ≤ ‖e‖ * (∫ q, W q ∂μ.prod μ) := by
    calc
      _ ≤ ∫ q, |E q| ∂μ.prod μ := abs_integral_le_integral_abs
      _ ≤ ∫ q, ‖e‖ * W q ∂μ.prod μ := integral_mono hE.abs (hW.const_mul ‖e‖) hpoint
      _ = _ := integral_const_mul _ _
  refine ⟨hE, ?_⟩
  have hF0 : 0 ≤ ∫ x, f x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg (f x)
  have hG0 : 0 ≤ ∫ x, g x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg (g x)
  apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
  calc
    _ ≤ (‖e‖ * (∫ q, W q ∂μ.prod μ)) ^ 2 :=
      (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg _) (integral_nonneg hW0))).mpr habs
    _ ≤ ‖e‖ ^ 2 * ((C * 2 ^ m) ^ 2 * (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ)) := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left hWsq (sq_nonneg _)
    _ = _ := by
      simp only [mul_pow, Real.sq_sqrt hF0, Real.sq_sqrt hG0]
      ring

end

end RieszRectifiability

end OAI

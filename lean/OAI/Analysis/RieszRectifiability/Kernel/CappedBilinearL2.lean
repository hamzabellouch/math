import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.CapErrorBilinear
import OAI.Analysis.RieszRectifiability.Kernel.HardBilinearPairing

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory
open scoped NNReal ENNReal

theorem capped_bilinear_bound_of_native_L2 {d : ℕ} (m : ℕ) (hm : 1 ≤ m) (C : ℝ)
    (μ : Measure (Ambient d)) [IsFiniteMeasure μ] (hgrowth : GlobalUpperGrowth m C μ)
    (D : ℝ≥0) (ε : ℝ) (hε : 0 < ε) (e : Ambient d)
    (f g : Ambient d → ℝ) (hfm : Measurable f) (hgm : Measurable g)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hTf : MemLp (truncated m μ ε f) 2 μ)
    (hN : eLpNorm (truncated m μ ε f) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm f 2 μ) :
    |∫ q : Ambient d × Ambient d, g q.1 * f q.2 * scalarCappedRieszKernel m e ε q ∂μ.prod μ| ≤
      (‖e‖ * ((D : ℝ) + C * 2 ^ m)) *
        Real.sqrt (∫ x, g x ^ 2 ∂μ) * Real.sqrt (∫ x, f x ^ 2 ∂μ) := by
  have hf1 := hf.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hg1 := hg.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hcap := bounded_kernel_bilinear_integrable μ (scalarCappedRieszKernel m e ε)
    (scalarCappedRieszKernel_continuous m e ε hε).measurable (‖e‖ * (ε ^ m)⁻¹)
    (scalarCappedRieszKernel_bound m e ε hε) g f hgm hfm hg1 hf1
  have hhard := bounded_kernel_bilinear_integrable μ (scalarTruncatedKernel m e ε)
    (scalarTruncatedKernel_measurable m e ε) (‖e‖ * (ε ^ m)⁻¹)
    (scalarTruncatedKernel_bound m e ε hε) g f hgm hfm hg1 hf1
  have hb := hard_bilinear_bound_of_native_L2 m hm C μ hgrowth D ε hε e
    f g hfm hgm hf hg hf1 hg1 hTf hN
  have he := (scalar_cap_error_bilinear_integrable_and_bound m C μ hgrowth e ε hε
    g f hgm hfm hg hf).2
  have hdiff : (∫ q : Ambient d × Ambient d, g q.1 * f q.2 *
      (scalarCappedRieszKernel m e ε q - scalarTruncatedKernel m e ε q) ∂μ.prod μ) =
      (∫ q : Ambient d × Ambient d, g q.1 * f q.2 * scalarCappedRieszKernel m e ε q ∂μ.prod μ) -
      (∫ q : Ambient d × Ambient d, g q.1 * f q.2 * scalarTruncatedKernel m e ε q ∂μ.prod μ) := by
    simp only [mul_sub]
    exact integral_sub hcap hhard
  rw [hdiff] at he
  let P := ∫ q : Ambient d × Ambient d, g q.1 * f q.2 * scalarCappedRieszKernel m e ε q ∂μ.prod μ
  let H := ∫ q : Ambient d × Ambient d, g q.1 * f q.2 * scalarTruncatedKernel m e ε q ∂μ.prod μ
  have ht : |P| ≤ |H| + |P - H| := by
    have h := abs_add_le H (P - H)
    rw [show H + (P - H) = P by ring] at h
    exact h
  calc
    _ ≤ |H| + |P - H| := ht
    _ ≤ (‖e‖ * (D : ℝ)) * Real.sqrt (∫ x, g x ^ 2 ∂μ) * Real.sqrt (∫ x, f x ^ 2 ∂μ) +
        (‖e‖ * (C * 2 ^ m)) * Real.sqrt (∫ x, g x ^ 2 ∂μ) * Real.sqrt (∫ x, f x ^ 2 ∂μ) :=
      add_le_add hb he
    _ = _ := by ring

end

end RieszRectifiability

end OAI

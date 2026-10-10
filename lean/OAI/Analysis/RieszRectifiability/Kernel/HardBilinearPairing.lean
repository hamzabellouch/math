import Mathlib
import OAI.Analysis.RieszRectifiability.Kernel.FiniteRieszPairing
import OAI.Analysis.RieszRectifiability.Kernel.VectorL2PairingBounds

namespace OAI

/-!
# Bilinear pairings for hard truncations

Integrability of bounded-kernel products permits the product-space bilinear form
to be rewritten as a pairing with the hard-truncated Riesz transform. This
identification connects kernel integrals with the vector-valued L² estimates.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set Function
open scoped NNReal ENNReal

theorem bounded_kernel_bilinear_integrable {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] (k : X × X → ℝ) (hk : Measurable k)
    (B : ℝ) (hB : ∀ q, |k q| ≤ B)
    (f g : X → ℝ) (hfm : Measurable f) (hgm : Measurable g)
    (hf : Integrable f μ) (hg : Integrable g μ) :
    Integrable (fun q : X × X => f q.1 * g q.2 * k q) (μ.prod μ) := by
  apply ((hf.abs.mul_prod hg.abs).mul_const B).mono'
    (((hfm.comp measurable_fst).mul (hgm.comp measurable_snd)).mul hk).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun q => by
    simp only [Pi.mul_apply, Function.comp_apply, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hB q) (mul_nonneg (abs_nonneg _) (abs_nonneg _))

theorem truncated_inner_eq_weighted_scalar_integral {d : ℕ} (m : ℕ) (hm : 1 ≤ m) (C : ℝ)
    (μ : Measure (Ambient d)) (hgrowth : GlobalUpperGrowth m C μ)
    (e : Ambient d) (ε : ℝ) (hε : 0 < ε)
    (f : Ambient d → ℝ) (hf : MemLp f 2 μ) (x : Ambient d) :
    inner ℝ e (truncated m μ ε f x) =
      ∫ y, f y * scalarTruncatedKernel m e ε (x, y) ∂μ := by
  have hi := truncation_integrable_of_globalGrowth m hm C μ hgrowth f hf x ε hε
  have hs : MeasurableSet {y : Ambient d | ε < dist x y} :=
    measurableSet_lt measurable_const (continuous_const.dist continuous_id).measurable
  unfold truncated
  rw [← integral_inner (𝕜 := ℝ) hi e, ← integral_indicator hs]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  by_cases hy : ε < dist x y
  · rw [indicator_of_mem (show y ∈ {y : Ambient d | ε < dist x y} from hy)]
    simp only [scalarTruncatedKernel, ite_eq_left hy, real_inner_smul_right]
  · rw [indicator_of_notMem (show y ∉ {y : Ambient d | ε < dist x y} from hy)]
    simp only [scalarTruncatedKernel, ite_eq_right hy, mul_zero]

theorem hard_bilinear_eq_truncated_pairing {d : ℕ} (m : ℕ) (hm : 1 ≤ m) (C : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hgrowth : GlobalUpperGrowth m C μ)
    (e : Ambient d) (ε : ℝ) (hε : 0 < ε)
    (f g : Ambient d → ℝ) (hfm : Measurable f) (hgm : Measurable g)
    (hf : MemLp f 2 μ) (hf1 : Integrable f μ) (hg1 : Integrable g μ) :
    (∫ q : Ambient d × Ambient d, g q.1 * f q.2 * scalarTruncatedKernel m e ε q ∂μ.prod μ) =
      ∫ x, g x * inner ℝ e (truncated m μ ε f x) ∂μ := by
  have hI := bounded_kernel_bilinear_integrable μ (scalarTruncatedKernel m e ε)
    (scalarTruncatedKernel_measurable m e ε) (‖e‖ * (ε ^ m)⁻¹)
    (scalarTruncatedKernel_bound m e ε hε) g f hgm hfm hg1 hf1
  rw [integral_prod _ hI]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  simp only [mul_assoc]
  rw [integral_const_mul, ← truncated_inner_eq_weighted_scalar_integral m hm C μ hgrowth e ε hε f hf x]

theorem hard_bilinear_bound_of_native_L2 {d : ℕ} (m : ℕ) (hm : 1 ≤ m) (C : ℝ)
    (μ : Measure (Ambient d)) [SFinite μ] (hgrowth : GlobalUpperGrowth m C μ)
    (D : ℝ≥0) (ε : ℝ) (hε : 0 < ε) (e : Ambient d)
    (f g : Ambient d → ℝ) (hfm : Measurable f) (hgm : Measurable g)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (hf1 : Integrable f μ) (hg1 : Integrable g μ)
    (hTf : MemLp (truncated m μ ε f) 2 μ)
    (hN : eLpNorm (truncated m μ ε f) 2 μ ≤ (D : ℝ≥0∞) * eLpNorm f 2 μ) :
    |∫ q : Ambient d × Ambient d, g q.1 * f q.2 * scalarTruncatedKernel m e ε q ∂μ.prod μ| ≤
      (‖e‖ * (D : ℝ)) * Real.sqrt (∫ x, g x ^ 2 ∂μ) * Real.sqrt (∫ x, f x ^ 2 ∂μ) := by
  rw [hard_bilinear_eq_truncated_pairing m hm C μ hgrowth e ε hε f g hfm hgm hf hf1 hg1]
  exact (scalar_L2_pairing_of_vector_norm_bound μ f g (truncated m μ ε f) hf hg hTf D hN e).2

end

end RieszRectifiability

end OAI

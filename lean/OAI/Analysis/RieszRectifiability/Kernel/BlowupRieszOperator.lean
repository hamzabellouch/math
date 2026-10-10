import Mathlib
import OAI.Analysis.RieszRectifiability.Flatness.BlowupAffineGeometry

namespace OAI

/-!
# Riesz operators under affine blowup

Affine dilation rescales distances, the Riesz kernel, and the hard truncation radius.
The corresponding change of measure gives the square-seminorm scaling identity and
transports uniform Riesz bounds to blowups. The seminorm identity also covers functions
that are not almost everywhere strongly measurable, since its exponent is positive and finite.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

theorem physicalAffine_dist {d : ℕ} (a x y : Ambient d) (r : ℝ) (hr : 0 < r) :
    dist (physicalAffine a r hr x) (physicalAffine a r hr y) = r * dist x y := by
  simp only [physicalAffine_apply, dist_add_left, dist_smul₀, Real.norm_of_nonneg hr.le]

theorem kernel_physicalAffine {d : ℕ} (n : ℕ) (a x y : Ambient d) (r : ℝ) (hr : 0 < r) :
    kernel n (physicalAffine a r hr x) (physicalAffine a r hr y) =
      (r ^ n)⁻¹ • kernel n x y := by
  have hsub : physicalAffine a r hr x - physicalAffine a r hr y = r • (x - y) := by
    simp only [physicalAffine_apply, smul_sub]
    abel
  simp only [kernel, hsub, norm_smul, Real.norm_of_nonneg hr.le, mul_pow, mul_inv_rev,
    smul_smul]
  congr 1
  rw [pow_succ]
  field_simp
  ring

theorem truncated_blowup {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a x : Ambient d) (r ε : ℝ) (hr : 0 < r) (f : Ambient d → ℝ) :
    truncated n (blowupMeasure n μ a r) ε f x =
      truncated n μ (r * ε) (fun y => f (r⁻¹ • (y - a))) (physicalAffine a r hr x) := by
  have he : MeasurableEmbedding (fun y : Ambient d => r⁻¹ • (y - a)) :=
    (physicalHomeomorph a r hr).symm.measurableEmbedding
  have hdist (y : Ambient d) : dist (physicalAffine a r hr x) y =
      r * dist x (r⁻¹ • (y - a)) := by
    have h := physicalAffine_dist a x ((physicalAffine a r hr).symm y) r hr
    rw [(physicalAffine a r hr).apply_symm_apply] at h
    exact h
  have hset : (fun y : Ambient d => r⁻¹ • (y - a)) ⁻¹' {y | ε < dist x y} =
      {y | r * ε < dist (physicalAffine a r hr x) y} := by
    ext y
    simp only [mem_preimage, mem_ofPred_eq, hdist, mul_lt_mul_iff_right₀ hr]
  have hk (y : Ambient d) : kernel n (physicalAffine a r hr x) y =
      (r ^ n)⁻¹ • kernel n x (r⁻¹ • (y - a)) := by
    have h := kernel_physicalAffine n a x ((physicalAffine a r hr).symm y) r hr
    rw [(physicalAffine a r hr).apply_symm_apply] at h
    exact h
  unfold truncated
  rw [blowupMeasure, Measure.restrict_smul, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (r ^ n)⁻¹), he.setIntegral_map, hset,
    ← integral_smul]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [hk, smul_smul, smul_smul, mul_comm]

theorem memLp_blowup_iff {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (n : ℕ) (μ : Measure (Ambient d)) (a : Ambient d) (r : ℝ) (hr : 0 < r)
    (f : Ambient d → E) (p : ℝ≥0∞) :
    MemLp f p (blowupMeasure n μ a r) ↔ MemLp (fun y => f (r⁻¹ • (y - a))) p μ := by
  have he : MeasurableEmbedding (fun y : Ambient d => r⁻¹ • (y - a)) :=
    (physicalHomeomorph a r hr).symm.measurableEmbedding
  have hcancel : ENNReal.ofReal (r ^ n) • blowupMeasure n μ a r =
      μ.map (fun y => r⁻¹ • (y - a)) := by
    rw [blowupMeasure, smul_smul, ← ENNReal.ofReal_mul (by positivity : 0 ≤ r ^ n),
      mul_inv_cancel₀ (pow_ne_zero n hr.ne'), ENNReal.ofReal_one, one_smul]
  constructor
  · intro hf
    have hm := hf.smul_measure (ENNReal.ofReal_ne_top : ENNReal.ofReal (r ^ n) ≠ ⊤)
    rw [hcancel] at hm
    exact he.memLp_map_measure_iff.mp hm
  · intro hf
    have hm : MemLp f p (μ.map (fun y => r⁻¹ • (y - a))) := he.memLp_map_measure_iff.mpr hf
    exact hm.smul_measure ENNReal.ofReal_ne_top

theorem eLpNorm_blowup {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (n : ℕ) (μ : Measure (Ambient d)) (a : Ambient d) (r : ℝ) (hr : 0 < r)
    (f : Ambient d → E) :
    eLpNorm f 2 (blowupMeasure n μ a r) =
      (ENNReal.ofReal ((r ^ n)⁻¹)) ^ ((1 / (2 : ℝ≥0∞)).toReal) *
        eLpNorm (fun y => f (r⁻¹ • (y - a))) 2 μ := by
  have he : MeasurableEmbedding (fun y : Ambient d => r⁻¹ • (y - a)) :=
    (physicalHomeomorph a r hr).symm.measurableEmbedding
  rw [blowupMeasure, eLpNorm_smul_measure_of_ne_zero_of_ne_top
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤),
    he.eLpNorm_map_measure]
  rfl

theorem uniform_riesz_bound_blowup {d : ℕ} (n : ℕ) (μ : Measure (Ambient d))
    (a : Ambient d) (r : ℝ) (hr : 0 < r) (D : ℝ≥0)
    (hB : ∀ ε : ℝ, 0 < ε → ∀ f : Ambient d → ℝ, MemLp f 2 μ →
      MemLp (truncated n μ ε f) 2 μ ∧ eLpNorm (truncated n μ ε f) 2 μ ≤
        (D : ℝ≥0∞) * eLpNorm f 2 μ) :
    ∀ ε : ℝ, 0 < ε → ∀ f : Ambient d → ℝ, MemLp f 2 (blowupMeasure n μ a r) →
      MemLp (truncated n (blowupMeasure n μ a r) ε f) 2 (blowupMeasure n μ a r) ∧
      eLpNorm (truncated n (blowupMeasure n μ a r) ε f) 2 (blowupMeasure n μ a r) ≤
        (D : ℝ≥0∞) * eLpNorm f 2 (blowupMeasure n μ a r) := by
  intro ε hε f hf
  obtain ⟨hm, hn⟩ := hB (r * ε) (mul_pos hr hε) (fun y => f (r⁻¹ • (y - a)))
    ((memLp_blowup_iff n μ a r hr f 2).mp hf)
  have ht : (fun y => truncated n (blowupMeasure n μ a r) ε f (r⁻¹ • (y - a))) =
      truncated n μ (r * ε) (fun y => f (r⁻¹ • (y - a))) := by
    funext y
    rw [truncated_blowup n μ a _ r ε hr]
    change truncated n μ (r * ε) _
      (physicalAffine a r hr ((physicalAffine a r hr).symm y)) = _
    rw [(physicalAffine a r hr).apply_symm_apply]
  constructor
  · apply (memLp_blowup_iff n μ a r hr _ 2).mpr
    rw [ht]
    exact hm
  · rw [eLpNorm_blowup n μ a r hr, ht, eLpNorm_blowup n μ a r hr]
    calc
      _ ≤ _ * ((D : ℝ≥0∞) * eLpNorm (fun y => f (r⁻¹ • (y - a))) 2 μ) := mul_le_mul_right hn _
      _ = _ := by ac_rfl

end

end RieszRectifiability

end OAI

import OAI.Probability.PosteriorReplicas.Information.EntropyLossTest

namespace OAI

open MeasureTheory ProbabilityTheory InformationTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
namespace PosteriorReplicas

lemma log_tangent {x M : ℝ} (hx : 0 < x) (hM : 0 < M) :
    Real.log x ≤ Real.log M + x/M - 1 := by
  have h := Real.log_le_sub_one_of_pos (div_pos hx hM)
  rw [Real.log_div hx.ne' hM.ne'] at h
  linarith

lemma log_replica_comparison {c Z J J' a a' v M : ℝ}
    (hc : 0 < c) (hZ : 0 < Z) (hJ : 0 < J) (hJ' : 0 < J')
    (ha : 0 < a) (ha' : 0 < a') (hv : 0 < v) (hM : 0 < M) (k m : ℕ) :
    Real.log (c*J⁻¹^k*a⁻¹^m) - Real.log (c*Z⁻¹*J'⁻¹^k*a'⁻¹^m) ≤
      Real.log Z + (k:ℝ)*Real.log (J'/J) + (m:ℝ)*Real.log v +
        (m:ℝ)*(Real.log M + (a'*a⁻¹*v⁻¹)/M - 1) := by
  have hr := log_tangent (mul_pos (mul_pos ha' (inv_pos.mpr ha)) (inv_pos.mpr hv)) hM
  simp only [Real.log_mul (mul_pos ha' (inv_pos.mpr ha)).ne' (inv_pos.mpr hv).ne',
    Real.log_mul ha'.ne' (inv_pos.mpr ha).ne',Real.log_inv] at hr
  have he : Real.log (c*J⁻¹^k*a⁻¹^m) - Real.log (c*Z⁻¹*J'⁻¹^k*a'⁻¹^m) =
      Real.log Z + (k:ℝ)*Real.log (J'/J)+(m:ℝ)*(Real.log a'-Real.log a) := by
    rw [Real.log_mul (mul_pos hc (pow_pos (inv_pos.mpr hJ) _)).ne' (pow_pos (inv_pos.mpr ha) _).ne',
      Real.log_mul hc.ne' (pow_pos (inv_pos.mpr hJ) _).ne',
      Real.log_mul (mul_pos (mul_pos hc (inv_pos.mpr hZ)) (pow_pos (inv_pos.mpr hJ') _)).ne'
        (pow_pos (inv_pos.mpr ha') _).ne',
      Real.log_mul (mul_pos hc (inv_pos.mpr hZ)).ne' (pow_pos (inv_pos.mpr hJ') _).ne',
      Real.log_mul hc.ne' (inv_pos.mpr hZ).ne',Real.log_div hJ'.ne' hJ.ne']
    simp only [Real.log_pow,Real.log_inv]
    ring
  rw [he]
  nlinarith [mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg (α := ℝ) m)]

lemma entropy_loss_envelope {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hkl : klDiv μ ν ≠ ∞) {ψ : X → Y} (hψ : Measurable ψ)
    {g : Y → ℝ} (hg : Measurable g)
    (he : Integrable (fun y => Real.exp (g y)) (ν.map ψ))
    (hmean : (∫ y, Real.exp (g y) ∂ν.map ψ) ≤ 1)
    {F : X → ℝ} (hF : Integrable F μ)
    (hbound : ∀ᵐ x ∂μ, llr μ ν x - g (ψ x) ≤ F x) :
    (klDiv μ ν).toReal ≤ (klDiv (μ.map ψ) (ν.map ψ)).toReal + ∫ x, F x ∂μ := by
  have herr : Integrable (fun x => max (llr μ ν x - g (ψ x)) 0) μ := by
    apply hF.norm.mono' ((measurable_llr μ ν).sub (hg.comp hψ) |>.max measurable_const |>.aestronglyMeasurable)
    filter_upwards [hbound] with x hx
    rw [Real.norm_eq_abs,abs_of_nonneg (le_max_right _ 0),Real.norm_eq_abs]
    exact max_le (hx.trans (le_abs_self _)) (abs_nonneg _)
  obtain ⟨_,hi,h⟩ := entropy_loss_test μ ν hkl hψ hg he hmean herr
  exact h.trans (add_le_add le_rfl (integral_mono_ae hi hF hbound))

end PosteriorReplicas
end

end OAI

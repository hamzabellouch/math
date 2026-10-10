import Mathlib
import OAI.Analysis.AffineBernstein.MassUpper
import OAI.Analysis.AffineBernstein.MassIntegral

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/- The determinant interpolation controls the genuine tube mass with inverse
trace weight after using only the normalized positive support-height bound. -/
lemma lintegral_weighted_tube_mass_le {n : ℕ} (hn : 1 ≤ n)
    {h B Q t : X → ℝ} (hB : AEMeasurable B μ) (hQ : AEMeasurable Q μ)
    (ht : AEMeasurable t μ) (hBp : ∀ᵐ x ∂μ, 0 < B x)
    (hQp : ∀ᵐ x ∂μ, 0 < Q x) (htp : ∀ᵐ x ∂μ, 0 < t x)
    {r : ℝ} (hr : 0 < r) (hbound : ∀ᵐ x ∂μ, r ≤ h x) :
    (∫⁻ x, ENNReal.ofReal (tubeMeasureCoefficient n (h x) (B x) (Q x)*t x) ∂μ) ≤
      ENNReal.ofReal (r^(-(n:ℝ)/2)) *
      (∫⁻ x, ENNReal.ofReal (B x ^ (1/((n:ℝ)+2)) * Q x ^ (1-1/((n:ℝ)+2))*t x) ∂μ) ^
        (((n:ℝ)+2)/(2*((n:ℝ)+1))) *
      (∫⁻ x, ENNReal.ofReal (B x*t x) ∂μ) ^ (1-((n:ℝ)+2)/(2*((n:ℝ)+1))) := by
  have hI := lintegral_weighted_tube_interpolation hn hB hQ ht hBp hQp htp
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (r^(-(n:ℝ)/2))*
        ENNReal.ofReal (Real.sqrt (B x*Q x)*t x) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hbound,htp] with x hx htx
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hr.le _)]
      apply ENNReal.ofReal_le_ofReal
      unfold tubeMeasureCoefficient
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg (Real.sqrt_nonneg _) htx.le)
      exact Real.rpow_le_rpow_of_nonpos hr hx
        (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg n)) (by norm_num))
    _ = ENNReal.ofReal (r^(-(n:ℝ)/2))*
        ∫⁻ x, ENNReal.ofReal (Real.sqrt (B x*Q x)*t x) ∂μ := by
      rw [lintegral_const_mul']
      exact ENNReal.ofReal_ne_top
    _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_right hI (ENNReal.ofReal (r^(-(n:ℝ)/2)))

/- Full sigma mass estimate. The inputs are the source determinant, fiber
area, cap inverse-energy, and principal-minor integrals, not an assumed sigma
bound. This is manuscript bounds.tex322–351 before geometric normalization. -/
lemma lintegral_sigma_mass_le {n : ℕ} (hn : 1 ≤ n)
    {h B Q t W : X → ℝ} (hh : AEMeasurable h μ)
    (hB : AEMeasurable B μ) (hQ : AEMeasurable Q μ) (ht : AEMeasurable t μ)
    (hBp : ∀ᵐ x ∂μ, 0 < B x) (hQp : ∀ᵐ x ∂μ, 0 < Q x)
    (htp : ∀ᵐ x ∂μ, 0 < t x)
    {r K : ℝ} (hr : 0 < r) (hK : 0 ≤ K)
    (hbound : ∀ᵐ x ∂μ, r ≤ h x) (hW : ∀ᵐ x ∂μ, W x ≤ 1+K*t x) :
    (∫⁻ x, ENNReal.ofReal (tubeMeasureCoefficient n (h x) (B x) (Q x)*W x) ∂μ) ≤
      ENNReal.ofReal (r^(-(n:ℝ)/2)) *
        (∫⁻ x, ENNReal.ofReal (B x) ∂μ)^(1/(2:ℝ)) *
        (∫⁻ x, ENNReal.ofReal (Q x) ∂μ)^(1/(2:ℝ)) +
      ENNReal.ofReal K * (ENNReal.ofReal (r^(-(n:ℝ)/2)) *
        (∫⁻ x, ENNReal.ofReal (B x ^ (1/((n:ℝ)+2)) * Q x ^ (1-1/((n:ℝ)+2))*t x) ∂μ) ^
          (((n:ℝ)+2)/(2*((n:ℝ)+1))) *
        (∫⁻ x, ENNReal.ofReal (B x*t x) ∂μ) ^ (1-((n:ℝ)+2)/(2*((n:ℝ)+1)))) := by
  let F : X → ℝ := fun x => tubeMeasureCoefficient n (h x) (B x) (Q x)
  have hF : AEMeasurable F μ := (hh.pow_const _).mul ((hB.mul hQ).sqrt)
  have hFp : ∀ᵐ x ∂μ, 0 ≤ F x := by
    filter_upwards [hbound,hBp,hQp] with x hx hb hq
    exact (tubeMeasureCoefficient_pos (hr.trans_le hx) hb hq).le
  have he : (∫⁻ x, ENNReal.ofReal (F x)* (1+ENNReal.ofReal K*ENNReal.ofReal (t x)) ∂μ) =
      (∫⁻ x, ENNReal.ofReal (F x) ∂μ)+ENNReal.ofReal K*(∫⁻ x, ENNReal.ofReal (F x*t x) ∂μ) := by
    simp_rw [mul_add,mul_one,mul_left_comm (ENNReal.ofReal (F _)) (ENNReal.ofReal K)]
    rw [lintegral_add_left' (hF.ennreal_ofReal),lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 2
    apply lintegral_congr_ae
    filter_upwards [hFp] with x hx
    exact (ENNReal.ofReal_mul hx).symm
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (F x)*(1+ENNReal.ofReal K*ENNReal.ofReal (t x)) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hFp,htp,hW] with x hf ht hw
      rw [← ENNReal.ofReal_mul hK]
      rw [← ENNReal.ofReal_one]
      rw [← ENNReal.ofReal_add zero_le_one (mul_nonneg hK ht.le),
        ← ENNReal.ofReal_mul hf]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hw hf)
    _ = _ := he
    _ ≤ _ := add_le_add (lintegral_tube_mass_le hB hQ (hBp.mono fun _ hx => hx.le) hr hbound)
      (mul_le_mul_right (lintegral_weighted_tube_mass_le hn hB hQ ht hBp hQp htp hr hbound) _)

end AffineBernstein
end

end OAI

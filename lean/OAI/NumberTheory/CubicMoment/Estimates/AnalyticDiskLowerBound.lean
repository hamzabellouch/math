import OAI.NumberTheory.CubicMoment.Estimates.AnalyticDiskLogDerivative

namespace OAI

/-! The real lower bound obtained by retaining one zero in the local
logarithmic-derivative expansion. All other zero terms have nonnegative
real part on the zero-free right half-plane. -/
noncomputable section
open scoped BigOperators
namespace CubicFirstMoment

lemma reciprocal_real_nonneg {z w : ℂ} (hw : w.re ≤ z.re) :
    0 ≤ ((z-w)⁻¹).re := by
  rw [Complex.inv_re]
  exact div_nonneg (by simpa using sub_nonneg.mpr hw) (Complex.normSq_nonneg _)

theorem normalized_disk_logDeriv_real_lower_bound (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) (hf0 : f 0=1) {B : ℝ} (hB : 1 < B)
    (hb : ∀ z : ℂ, ‖z‖ ≤ (7/8:ℝ) → ‖f z‖ ≤ B)
    {z : ℂ} (hz : ‖z‖ ≤ (1/2:ℝ)) (hfz : f z ≠ 0)
    (hleft : ∀ w : ℂ, f w=0 → w.re ≤ z.re) :
    -(diskLogDerivativeConstant*Real.log B) ≤ (logDeriv f z).re := by
  classical
  obtain ⟨Z,hZ,herr⟩ := normalized_disk_logDeriv f hf hf0 hB hb
  have hpos (w : ℂ) (hw : w ∈ Z) :
      0 ≤ (((analyticOrderAt f w).toNat:ℂ)/(z-w)).re := by
    simp only [div_eq_mul_inv,Complex.mul_re,Complex.natCast_re,Complex.natCast_im,
      zero_mul,sub_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (reciprocal_real_nonneg (hleft w (hZ w |>.mp hw).2))
  have hsum := Finset.sum_nonneg hpos
  have he := (Complex.abs_re_le_norm _).trans (herr z hz hfz)
  rw [Complex.sub_re,Complex.re_sum] at he
  linarith [(abs_le.mp he).1]

theorem normalized_disk_logDeriv_lower_bound (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) (hf0 : f 0=1) {B : ℝ} (hB : 1 < B)
    (hb : ∀ z : ℂ, ‖z‖ ≤ (7/8:ℝ) → ‖f z‖ ≤ B)
    {z ρ : ℂ} (hz : ‖z‖ ≤ (1/2:ℝ)) (hfz : f z ≠ 0)
    (hρ : ‖ρ‖ ≤ (3/4:ℝ)) (hfρ : f ρ=0)
    (hleft : ∀ w : ℂ, f w=0 → w.re ≤ z.re) :
    ((analyticOrderAt f ρ).toNat:ℝ)*((z-ρ)⁻¹).re-
      diskLogDerivativeConstant*Real.log B ≤ (logDeriv f z).re := by
  classical
  obtain ⟨Z,hZ,herr⟩ := normalized_disk_logDeriv f hf hf0 hB hb
  have hmem : ρ ∈ Z := (hZ ρ).mpr ⟨hρ,hfρ⟩
  have hpos (w : ℂ) (hw : w ∈ Z) :
      0 ≤ (((analyticOrderAt f w).toNat:ℂ)/(z-w)).re := by
    simp only [div_eq_mul_inv,Complex.mul_re,Complex.natCast_re,Complex.natCast_im,
      zero_mul,sub_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (reciprocal_real_nonneg (hleft w (hZ w |>.mp hw).2))
  have hsingle := Finset.single_le_sum hpos hmem
  have he := (Complex.abs_re_le_norm _).trans (herr z hz hfz)
  rw [Complex.sub_re,Complex.re_sum] at he
  have hm : (((analyticOrderAt f ρ).toNat:ℂ)/(z-ρ)).re=
      ((analyticOrderAt f ρ).toNat:ℝ)*((z-ρ)⁻¹).re := by
    simp only [div_eq_mul_inv,Complex.mul_re,Complex.natCast_re,Complex.natCast_im,
      zero_mul,sub_zero]
  rw [hm] at hsingle
  linarith [(abs_le.mp he).1]

end CubicFirstMoment

end

end OAI

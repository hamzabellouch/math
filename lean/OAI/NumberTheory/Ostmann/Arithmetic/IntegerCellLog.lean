import OAI.NumberTheory.Ostmann.Arithmetic.IntegerCellAbel

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.IntegerCell
open scoped BigOperators
open Set MeasureTheory

theorem log_weight_hasDerivAt (φ ψ : ℝ → ℝ) (G : ℝ)
    (hφ : ∀ t, HasDerivAt φ (ψ t) t) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y => φ (Real.log y-G)) (ψ (Real.log x-G)/x) x := by
  simpa only [div_eq_mul_inv, Function.comp_def] using
    (hφ (Real.log x-G)).comp x ((Real.hasDerivAt_log hx.ne').sub_const G)

theorem log_weight_derivative_continuous (ψ : ℝ → ℝ) (G lo hi : ℝ)
    (hψ : Continuous ψ) :
    ContinuousOn (fun x => ψ (Real.log x-G)/x) (Icc (Real.exp lo) (Real.exp hi)) := by
  intro x hx
  apply ContinuousAt.continuousWithinAt
  have hx0 : x ≠ 0 := ne_of_gt ((Real.exp_pos lo).trans_le hx.1)
  fun_prop (disch := simp [hx0])

theorem log_weight_variation_le (ψ : ℝ → ℝ) (G lo hi D : ℝ)
    (hlohi : lo ≤ hi) (hψ : Continuous ψ)
    (hD : ∀ t ∈ Icc lo hi, |ψ (t-G)| ≤ D) :
    (∫ x in Real.exp lo..Real.exp hi, |ψ (Real.log x-G)/x|) ≤ D*(hi-lo) := by
  have hAB : Real.exp lo ≤ Real.exp hi := Real.exp_le_exp.mpr hlohi
  have hiD : IntervalIntegrable (fun x => |ψ (Real.log x-G)/x|) volume
      (Real.exp lo) (Real.exp hi) :=
    (log_weight_derivative_continuous ψ G lo hi hψ).abs.intervalIntegrable_of_Icc hAB
  have hiInv : IntervalIntegrable (fun x : ℝ => D*x⁻¹) volume (Real.exp lo) (Real.exp hi) := by
    apply ContinuousOn.intervalIntegrable_of_Icc hAB
    intro x hx
    apply ContinuousAt.continuousWithinAt
    have hx0 : x ≠ 0 := ne_of_gt ((Real.exp_pos lo).trans_le hx.1)
    fun_prop (disch := simp [hx0])
  calc
    _ ≤ ∫ x in Real.exp lo..Real.exp hi, D*x⁻¹ := by
      apply intervalIntegral.integral_mono_on hAB hiD hiInv
      intro x hx
      have hxp : 0 < x := (Real.exp_pos lo).trans_le hx.1
      have hlog : Real.log x ∈ Icc lo hi :=
        ⟨(Real.le_log_iff_exp_le hxp).mpr hx.1, (Real.log_le_iff_le_exp hxp).mpr hx.2⟩
      rw [abs_div, abs_of_pos hxp, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (hD _ hlog) (inv_nonneg.mpr hxp.le)
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, integral_inv_of_pos (Real.exp_pos lo) (Real.exp_pos hi),
        Real.log_div (Real.exp_ne_zero hi) (Real.exp_ne_zero lo), Real.log_exp, Real.log_exp]

theorem log_density_integral (φ : ℝ → ℝ) (G lo hi : ℝ) (hφ : Continuous φ) :
    Real.exp (-G)*(∫ x in Real.exp lo..Real.exp hi, φ (Real.log x-G)) =
      ∫ t in lo..hi, Real.exp (t-G)*φ (t-G) := by
  have hc : ContinuousOn (fun x => φ (Real.log x-G)) (Real.exp '' uIcc lo hi) := by
    rintro x ⟨t, ht, rfl⟩
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := exact Real.exp_ne_zero _)
  have hsub := intervalIntegral.integral_comp_mul_deriv'
    (f := Real.exp) (f' := Real.exp) (g := fun x => φ (Real.log x-G))
    (fun t _ => Real.hasDerivAt_exp t) Real.continuous_exp.continuousOn hc
  simp only [Function.comp_def, Real.log_exp] at hsub
  rw [← hsub, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [Real.exp_sub, Real.exp_neg]
  ring

theorem open_log_residue_error (M : ℕ) [NeZero M] (a : ZMod M)
    (φ ψ : ℝ → ℝ) (G lo hi B D : ℝ) (hlohi : lo ≤ hi)
    (hφ : ∀ t, HasDerivAt φ (ψ t) t) (hψ : Continuous ψ)
    (hB : ∀ t ∈ Icc lo hi, |φ (t-G)| ≤ B)
    (hD : ∀ t ∈ Icc lo hi, |ψ (t-G)| ≤ D) :
    |Real.exp (-G)*(∑ n ∈ Finset.Ioc ⌊Real.exp lo⌋₊ ⌊Real.exp hi⌋₊,
        φ (Real.log n-G)*residueIndicator M a n) -
      (∫ t in lo..hi, Real.exp (t-G)*φ (t-G))/(M : ℝ)| ≤
        Real.exp (-G)*(4*B+2*D*(hi-lo)) := by
  have hAB : Real.exp lo ≤ Real.exp hi := Real.exp_le_exp.mpr hlohi
  have hf := smooth_residue_error_bound M a (fun x => φ (Real.log x-G))
    (fun x => ψ (Real.log x-G)/x) (Real.exp_pos lo).le hAB
    (fun x hx => log_weight_hasDerivAt φ ψ G hφ ((Real.exp_pos lo).trans_le hx.1))
    (log_weight_derivative_continuous ψ G lo hi hψ)
  have hv := log_weight_variation_le ψ G lo hi D hlohi hψ hD
  have hcφ : Continuous φ := continuous_iff_continuousAt.mpr (fun t => (hφ t).continuousAt)
  rw [← log_density_integral φ G lo hi hcφ]
  rw [mul_div_assoc, ← mul_sub, abs_mul, abs_of_pos (Real.exp_pos (-G))]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos (-G)).le
  apply hf.trans
  simp only [Real.log_exp]
  have hBlo := hB lo ⟨le_rfl, hlohi⟩
  have hBhi := hB hi ⟨hlohi, le_rfl⟩
  linarith

end Ostmann.Arithmetic.IntegerCell
end

end OAI

import OAI.MathematicalPhysics.DefocusingNLS.Spectrum.SpectralRegularKernel
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace OAI

/-! A Gaussian weight makes the regular-origin Volterra operator contractive on any finite radius. -/

open Set MeasureTheory
namespace DefocusingNLS

theorem spectralRegularAverage_weighted_bound (d : ℕ) (h R α M r : ℝ)
    (hα : 0 ≤ α) (hM : 0 ≤ M) (hr : r ∈ Icc 0 R) (f : ℝ → ℂ)
    (hf : ∀ s ∈ Icc 0 R, ‖f s‖ ≤ M*Real.exp (α*s^2)) :
    ‖spectralRegularAverage d h f r‖ ≤ M*Real.exp (α*r^2) := by
  apply spectralRegularAverage_bound d h r _ r f ⟨hr.1,le_rfl⟩ (by positivity)
  intro s hs
  apply (hf s ⟨hs.1,hs.2.trans hr.2⟩).trans
  apply mul_le_mul_of_nonneg_left _ hM
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_left (by nlinarith [hs.1,hs.2]) hα

theorem integral_mul_exp_square (α r : ℝ) (hα : α ≠ 0) :
    (∫ s in (0 : ℝ)..r, s*Real.exp (α*s^2))=(Real.exp (α*r^2)-1)/(2*α) := by
  have hd (s : ℝ) : HasDerivAt (fun s : ℝ => Real.exp (α*s^2)/(2*α))
      (s*Real.exp (α*s^2)) s := by
    convert! ((((hasDerivAt_id s).pow 2).const_mul α).exp.div_const (2*α)) using 1
    simp only [Pi.pow_apply,id_eq]
    field_simp [hα]
    ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
    (show IntervalIntegrable (fun s : ℝ => s*Real.exp (α*s^2)) volume 0 r from
      (by fun_prop : Continuous (fun s : ℝ => s*Real.exp (α*s^2))).intervalIntegrable _ _)
  simpa only [zero_pow (by norm_num : 2 ≠ 0),mul_zero,Real.exp_zero,sub_div] using hi

theorem spectralRegularPrimitive_weighted_bound (d : ℕ) (h R α M r : ℝ)
    (hα : 0 < α) (hM : 0 ≤ M) (hr : r ∈ Icc 0 R) (f : ℝ → ℂ)
    (hf : ∀ s ∈ Icc 0 R, ‖f s‖ ≤ M*Real.exp (α*s^2)) :
    ‖spectralRegularPrimitive d h f r‖ ≤ M*Real.exp (α*r^2)/(2*α) := by
  have hi := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) hr.1
    (f := fun s : ℝ => (s : ℂ)*spectralRegularAverage d h f s)
    (g := fun s : ℝ => M*(s*Real.exp (α*s^2)))
    (Filter.Eventually.of_forall (fun s hs => ?_))
    ((by fun_prop : Continuous (fun s : ℝ => M*(s*Real.exp (α*s^2)))).intervalIntegrable 0 r)
  · change ‖spectralRegularPrimitive d h f r‖ ≤ _ at hi
    rw [intervalIntegral.integral_const_mul,integral_mul_exp_square α r hα.ne'] at hi
    apply hi.trans
    rw [mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ hM
    exact div_le_div_of_nonneg_right (sub_le_self _ zero_le_one) (by positivity)
  · have hs' : s ∈ Icc 0 R := ⟨hs.1.le,hs.2.trans hr.2⟩
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hs'.1]
    calc
      _ ≤ s*(M*Real.exp (α*s^2)) := mul_le_mul_of_nonneg_left
        (spectralRegularAverage_weighted_bound d h R α M s hα.le hM hs' f hf) hs'.1
      _ = _ := by ring

end DefocusingNLS

end OAI

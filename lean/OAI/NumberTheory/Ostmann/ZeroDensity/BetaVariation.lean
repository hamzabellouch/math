import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace OAI

open scoped BigOperators RealInnerProductSpace
open Set MeasureTheory

namespace Ostmann.ZeroDensity

theorem point_le_base_add_variation (F G : ℝ → ℝ)
    (hG : Continuous G) (hderiv : ∀ x, HasDerivAt F (G x) x)
    {a x b : ℝ} (hax : a ≤ x) (hxb : x ≤ b) :
    F x ≤ F a + ∫ t in a..b, |G t| := by
  have heq : (∫ t in a..x, G t) = F x - F a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
      (hG.intervalIntegrable a x)
  have hbound : F x - F a ≤ ∫ t in a..b, |G t| := by
    calc
      F x - F a ≤ |F x - F a| := le_abs_self _
      _ = |∫ t in a..x, G t| := congrArg abs heq.symm
      _ ≤ ∫ t in a..x, |G t| := intervalIntegral.abs_integral_le_integral_abs hax
      _ ≤ ∫ t in a..b, |G t| :=
        intervalIntegral.integral_mono_interval le_rfl hax hxb
          (Filter.Eventually.of_forall (fun t => abs_nonneg (G t)))
          (hG.abs.intervalIntegrable a b)
  linarith

theorem abs_norm_sq_derivative_le (z w : ℂ) :
    |2 * inner ℝ z w| ≤ ‖z‖ ^ 2 + ‖w‖ ^ 2 := by
  have hinner := abs_real_inner_le_norm z w
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  nlinarith [sq_nonneg (‖z‖ - ‖w‖)]

theorem norm_sq_le_base_add_energy (f g : ℝ → ℂ)
    (hf : Continuous f) (hg : Continuous g)
    (hderiv : ∀ x, HasDerivAt f (g x) x)
    {a x b : ℝ} (hax : a ≤ x) (hxb : x ≤ b) :
    ‖f x‖ ^ 2 ≤ ‖f a‖ ^ 2 + ∫ t in a..b, (‖f t‖ ^ 2 + ‖g t‖ ^ 2) := by
  have hG : Continuous (fun t => 2 * inner ℝ (f t) (g t)) := by
    exact continuous_const.mul (hf.inner hg)
  have h := point_le_base_add_variation (fun t => ‖f t‖ ^ 2)
    (fun t => 2 * inner ℝ (f t) (g t)) hG (fun t => (hderiv t).norm_sq) hax hxb
  apply h.trans
  apply add_le_add_right
  exact intervalIntegral.integral_mono_on (hax.trans hxb)
    (hG.abs.intervalIntegrable a b)
    (((hf.norm.pow 2).add (hg.norm.pow 2)).intervalIntegrable a b)
    (fun t _ => abs_norm_sq_derivative_le (f t) (g t))

theorem sum_norm_sq_varying_parameter_le {ι : Type*} (samples : Finset ι)
    (f g : ι → ℝ → ℂ) (β : ι → ℝ) {a b : ℝ}
    (hβ : ∀ i ∈ samples, β i ∈ Icc a b)
    (hf : ∀ i ∈ samples, Continuous (f i)) (hg : ∀ i ∈ samples, Continuous (g i))
    (hderiv : ∀ i ∈ samples, ∀ t, HasDerivAt (f i) (g i t) t) :
    (∑ i ∈ samples, ‖f i (β i)‖ ^ 2) ≤
      (∑ i ∈ samples, ‖f i a‖ ^ 2) +
        ∫ t in a..b, ∑ i ∈ samples, (‖f i t‖ ^ 2 + ‖g i t‖ ^ 2) := by
  calc
    (∑ i ∈ samples, ‖f i (β i)‖ ^ 2) ≤
        ∑ i ∈ samples, (‖f i a‖ ^ 2 +
          ∫ t in a..b, (‖f i t‖ ^ 2 + ‖g i t‖ ^ 2)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact norm_sq_le_base_add_energy (f i) (g i) (hf i hi) (hg i hi)
        (hderiv i hi) (hβ i hi).1 (hβ i hi).2
    _ = _ := by
      rw [Finset.sum_add_distrib, intervalIntegral.integral_finsetSum]
      intro i hi
      exact ((hf i hi).norm.pow 2 |>.add ((hg i hi).norm.pow 2)).intervalIntegrable a b

theorem sum_norm_sq_varying_parameter_le_of_uniform {ι : Type*} (samples : Finset ι)
    (f g : ι → ℝ → ℂ) (β : ι → ℝ) {a b B₀ B₁ : ℝ}
    (hab : a ≤ b) (hlen : b - a ≤ 1) (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁)
    (hβ : ∀ i ∈ samples, β i ∈ Icc a b)
    (hf : ∀ i ∈ samples, Continuous (f i)) (hg : ∀ i ∈ samples, Continuous (g i))
    (hderiv : ∀ i ∈ samples, ∀ t, HasDerivAt (f i) (g i t) t)
    (hbound₀ : ∀ t ∈ Icc a b, (∑ i ∈ samples, ‖f i t‖ ^ 2) ≤ B₀)
    (hbound₁ : ∀ t ∈ Icc a b, (∑ i ∈ samples, ‖g i t‖ ^ 2) ≤ B₁) :
    (∑ i ∈ samples, ‖f i (β i)‖ ^ 2) ≤ 2 * B₀ + B₁ := by
  have hbase := hbound₀ a ⟨le_rfl, hab⟩
  have hc : Continuous (fun t => ∑ i ∈ samples, (‖f i t‖ ^ 2 + ‖g i t‖ ^ 2)) :=
    continuous_finsetSum samples fun i hi => (hf i hi).norm.pow 2 |>.add ((hg i hi).norm.pow 2)
  have hint : (∫ t in a..b, ∑ i ∈ samples, (‖f i t‖ ^ 2 + ‖g i t‖ ^ 2)) ≤
      B₀ + B₁ := by
    calc
      _ ≤ ∫ t in a..b, (B₀ + B₁) := by
        apply intervalIntegral.integral_mono_on hab (hc.intervalIntegrable a b)
          (intervalIntegrable_const)
        intro t ht
        rw [Finset.sum_add_distrib]
        exact add_le_add (hbound₀ t ht) (hbound₁ t ht)
      _ = (b - a) * (B₀ + B₁) := by simp [mul_add]
      _ ≤ B₀ + B₁ := by nlinarith
  have h := sum_norm_sq_varying_parameter_le samples f g β hβ hf hg hderiv
  linarith

end Ostmann.ZeroDensity

end OAI

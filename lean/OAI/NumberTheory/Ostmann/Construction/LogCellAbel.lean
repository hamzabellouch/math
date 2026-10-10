import Mathlib

namespace OAI

open MeasureTheory
namespace Ostmann.Construction

lemma smooth_prime_sum_error_identity (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (f g : ℝ → ℝ) (hf : ∀ t ∈ Set.Icc a b, HasDerivAt f (g t) t)
    (hg : ContinuousOn g (Set.Icc a b)) (hfa : f a = 0) (hfb : f b = 0) :
    (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊ with n.Prime, f n * Real.log n) -
      (∫ t in a..b, f t) = -(∫ t in a..b, g t*(Chebyshev.theta t-t)) := by
  let c : ℕ → ℝ := fun n => if n.Prime then Real.log n else 0
  have hc (t : ℝ) : (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n) = Chebyshev.theta t := by
    rw [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter]
  have hfc : ContinuousOn f (Set.Icc a b) :=
    fun t ht => (hf t ht).continuousAt.continuousWithinAt
  have hgi : IntegrableOn g (Set.Icc a b) := hg.integrableOn_Icc
  have hdi : IntegrableOn (deriv f) (Set.Icc a b) :=
    hgi.congr_fun (fun t ht => (hf t ht).deriv.symm) measurableSet_Icc
  have hAbel := sum_mul_eq_sub_sub_integral_mul c ha hab
    (fun t ht => (hf t ht).differentiableAt) hdi
  have hsum : (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, f n*c n) =
      ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊ with n.Prime, f n*Real.log n := by
    simp only [c, mul_ite, mul_zero, Finset.sum_filter]
  rw [hsum, hfa, hfb] at hAbel
  simp only [zero_mul, sub_self, zero_sub, hc] at hAbel
  have hInt : (∫ t in Set.Ioc a b, deriv f t * Chebyshev.theta t) =
      ∫ t in a..b, g t * Chebyshev.theta t := by
    rw [intervalIntegral.integral_of_le hab]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    dsimp only
    rw [(hf t ⟨ht.1.le,ht.2⟩).deriv]
  rw [hInt] at hAbel
  have hcontf : ContinuousOn f (Set.uIcc a b) := by rwa [Set.uIcc_of_le hab]
  have hcontg : ContinuousOn g (Set.uIcc a b) := by rwa [Set.uIcc_of_le hab]
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (u := fun t : ℝ => t) (v := f) (u' := fun _ => (1:ℝ)) (v' := g)
    continuous_id.continuousOn hcontf (fun t _ => hasDerivAt_id t)
    (fun t ht => hf t (by simpa only [min_eq_left hab, max_eq_right hab] using
      (show t ∈ Set.Icc (min a b) (max a b) from ⟨ht.1.le,ht.2.le⟩)))
    intervalIntegrable_const hcontg.intervalIntegrable
  simp only [hfa,hfb,mul_zero,sub_self,zero_sub,one_mul] at hparts
  have hprefix : IntervalIntegrable (fun t => g t*Chebyshev.theta t) volume a b := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
    simpa only [hc] using integrableOn_mul_sum_Icc c ha hgi (m := 0)
  have hid : IntervalIntegrable (fun t => t*g t) volume a b :=
    (continuous_id.continuousOn.mul hcontg).intervalIntegrable
  rw [hAbel, ← neg_inj, neg_sub]
  rw [show (fun t => g t*(Chebyshev.theta t-t)) =
    (fun t => g t*Chebyshev.theta t - t*g t) by funext t; ring,
    intervalIntegral.integral_sub hprefix hid, hparts]
  ring

end Ostmann.Construction

end OAI

import OAI.NumberTheory.Ostmann.Arithmetic.PrimeProgression
import OAI.NumberTheory.Ostmann.Dirichlet.PrimeCountAbelDefinitions

namespace OAI

open Set MeasureTheory
open Ostmann.Dirichlet.PrimeCountAbel (logarithmicIntegral)
namespace Ostmann.Arithmetic.PrimeProgression

lemma continuousOn_log_inv {A B : ℝ} (hA : 1 < A) :
    ContinuousOn (fun t : ℝ => (Real.log t)⁻¹) (Icc A B) := by
  intro t ht
  have ht1 : 1 < t := hA.trans_le ht.1
  have ht0 : t ≠ 0 := ne_of_gt (by linarith)
  have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht1)
  apply ContinuousAt.continuousWithinAt
  fun_prop (disch := simp [ht0, hlog])

theorem logarithmicIntegral_hasDerivAt {x : ℝ} (hx : 2 ≤ x) :
    HasDerivAt logarithmicIntegral (Real.log x)⁻¹ x := by
  have hi : IntervalIntegrable (fun t : ℝ => (Real.log t)⁻¹) volume 2 x :=
    (continuousOn_log_inv (by norm_num : (1 : ℝ) < 2)).intervalIntegrable_of_Icc hx
  have hm : Measurable (fun t : ℝ => (Real.log t)⁻¹) := by measurability
  have hc : ContinuousAt (fun t : ℝ => (Real.log t)⁻¹) x := by
    have hx0 : x ≠ 0 := ne_of_gt (by linarith)
    have hl : Real.log x ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
    fun_prop (disch := simp [hx0, hl])
  unfold logarithmicIntegral
  simp only [one_div]
  exact intervalIntegral.integral_hasDerivAt_right hi hm.stronglyMeasurable.stronglyMeasurableAtFilter hc

theorem progression_main_hasDerivAt (M : ℕ) {x : ℝ} (hx : 2 ≤ x) :
    HasDerivAt (fun t => logarithmicIntegral t / (M.totient : ℝ))
      ((M.totient : ℝ)⁻¹ / Real.log x) x := by
  convert (logarithmicIntegral_hasDerivAt hx).div_const (M.totient : ℝ) using 1
  ring

theorem progression_main_integral_eq (M : ℕ) {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 < hi) :
    (∫ t in Real.exp lo..Real.exp hi, t⁻¹ * ((M.totient : ℝ)⁻¹ / Real.log t)) =
      harmonicIntegral M lo hi := by
  have ha : 1 < Real.exp lo := Real.one_lt_exp_iff.mpr hlo
  have hb : 1 < Real.exp hi := Real.one_lt_exp_iff.mpr hhi
  have heq : (fun t : ℝ => t⁻¹ * ((M.totient : ℝ)⁻¹ / Real.log t)) =
      fun t => (M.totient : ℝ)⁻¹ * (t⁻¹ / Real.log t) := by
    ext t
    ring
  rw [heq, intervalIntegral.integral_const_mul, integral_inv_div_log ha hb]
  rw [harmonicIntegral, integral_inv_of_pos hlo hhi, Real.log_div hhi.ne' hlo.ne']
  simp only [Real.log_exp]

end Ostmann.Arithmetic.PrimeProgression

end OAI

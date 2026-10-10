import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTLargeValues
import OAI.NumberTheory.TwoPoint.ShortIntervals.MRTRestrictedEnergy

namespace OAI

/-! Continuous large-value measure bounds for actual prime polynomials.
They also control a bounded cofactor on the same measurable set. -/

namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

lemma mrt_bounded_square_set_energy (G : ℝ → ℂ) (hG : Continuous G)
    {T B : ℝ} (hT : 0 ≤ T) {E : Set ℝ} (hE : MeasurableSet E)
    (hET : E ⊆ Set.Ioc (-T) T) (hbound : ∀ t ∈ E, ‖G t‖^2 ≤ B) :
    (∫ t in E, ‖G t‖^2) ≤ B*(∫ _t in E, (1:ℝ)) := by
  have hi1 : IntegrableOn (fun _ : ℝ => (1:ℝ)) E := by
    have hh := mrt_continuous_square_integrable
      (F := fun _ : ℝ => (1:ℂ)) continuous_const hT hET
    simpa only [norm_one, one_pow] using hh
  calc
    _ ≤ ∫ t in E, B*(1:ℝ) :=
      setIntegral_mono_on (mrt_continuous_square_integrable hG hT hET)
        (hi1.const_mul _) hE (fun t ht => by simpa only [mul_one] using hbound t ht)
    _ = _ := integral_const_mul _ _

theorem mrt_prime_large_set_measure (P : Finset ℕ) (a : ℕ → ℂ)
    (N r : ℕ) (hP : ∀ p ∈ P, p.Prime) (hN : ∀ p ∈ P, p ≤ N)
    {T V : ℝ} (hT : 0 < T) (hV : 0 < V) {E : Set ℝ}
    (hE : MeasurableSet E) (hET : E ⊆ Set.Ioc (-T) T)
    (hlarge : ∀ t ∈ E, V ≤
      ‖mrtExponentialPolynomial P a (fun p => -Real.log (p:ℝ)) t‖) :
    (∫ _t in E, (1:ℝ)) ≤
      (8*Real.exp 1*(T+(N^r:ℕ))*(r.factorial:ℝ)*(∑ p ∈ P, ‖a p‖^2)^r)/V^(2*r) := by
  let f := mrtExponentialPolynomial P a (fun p => -Real.log (p:ℝ))
  have hf : Continuous f := mrtExponentialPolynomial_continuous _ _ _
  have hi : IntegrableOn (fun t => ‖f t‖^(2*r)) (Set.Ioc (-T) T) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp
      ((hf.norm.pow _).intervalIntegrable _ _)
  have hi1 : IntegrableOn (fun _ : ℝ => (1:ℝ)) E := by
    have hh := mrt_continuous_square_integrable
      (F := fun _ : ℝ => (1:ℂ)) continuous_const hT.le hET
    simpa only [norm_one, one_pow] using hh
  apply (le_div_iff₀ (pow_pos hV _)).mpr
  calc
    _ = ∫ t in E, V^(2*r)*(1:ℝ) := by rw [integral_const_mul]; ring
    _ ≤ ∫ t in E, ‖f t‖^(2*r) := by
      apply setIntegral_mono_on (hi1.const_mul _) (hi.mono_set hET) hE
      intro t ht
      simpa only [mul_one] using pow_le_pow_left₀ hV.le (hlarge t ht) _
    _ ≤ ∫ t in -T..T, ‖f t‖^(2*r) := by
      rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
      exact setIntegral_mono_set hi (Filter.Eventually.of_forall (fun _ => by positivity))
        (Filter.Eventually.of_forall hET)
    _ ≤ _ := mrt_prime_polynomial_moment P a N r hP hN hT

theorem mrt_prime_large_set_weighted_energy (P : Finset ℕ) (a : ℕ → ℂ)
    (N r : ℕ) (hP : ∀ p ∈ P, p.Prime) (hN : ∀ p ∈ P, p ≤ N)
    {T V B : ℝ} (hT : 0 < T) (hV : 0 < V) (hB : 0 ≤ B)
    {E : Set ℝ} (hE : MeasurableSet E) (hET : E ⊆ Set.Ioc (-T) T)
    (hlarge : ∀ t ∈ E, V ≤
      ‖mrtExponentialPolynomial P a (fun p => -Real.log (p:ℝ)) t‖)
    (G : ℝ → ℂ) (hG : Continuous G) (hbound : ∀ t ∈ E, ‖G t‖^2 ≤ B) :
    (∫ t in E, ‖G t‖^2) ≤ B *
      ((8*Real.exp 1*(T+(N^r:ℕ))*(r.factorial:ℝ)*(∑ p ∈ P, ‖a p‖^2)^r)/V^(2*r)) := by
  have hi1 : IntegrableOn (fun _ : ℝ => (1:ℝ)) E := by
    have hh := mrt_continuous_square_integrable
      (F := fun _ : ℝ => (1:ℂ)) continuous_const hT.le hET
    simpa only [norm_one, one_pow] using hh
  calc
    _ ≤ ∫ t in E, B*(1:ℝ) :=
      setIntegral_mono_on (mrt_continuous_square_integrable hG hT.le hET)
        (hi1.const_mul _) hE (fun t ht => by simpa only [mul_one] using hbound t ht)
    _ = B*(∫ _t in E, (1:ℝ)) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (mrt_prime_large_set_measure P a N r hP hN hT hV hE hET hlarge) hB

end TwoPointCorrelations

end OAI

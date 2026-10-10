import OAI.NumberTheory.DirichletL.Detector.SixthFrequency
import OAI.NumberTheory.DirichletL.Detector.PhysicalLocalEuler

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CanonicalRowCompletion CanonicalQuadraticSieve CubicEisenstein
open CompletedGauss ConcreteTraceCRT GaussianShiftedPartition CenteredMomentCommonSupport
open CenteredMomentSupportedCorrelation ConcretePrimeRowBridge ProbePrimePower ProbeLocal ProbeEuler
local notation "O" => ActualEisensteinCubic.O

lemma finite_fourier_unit_scale {R : Type*} [CommRing R] [Fintype R]
    (F : R → ℂ) (ψ : AddChar R ℂ) (u : Rˣ) (c : ℂ) (hc : c ≠ 0)
    (hF : ∀ x, F ((u : R) * x) = c * F x) (H : R) :
    (∑ x, F x * ψ (((u : R) * H) * x)) = c⁻¹ * ∑ x, F x * ψ (H*x) := by
  have he : (∑ x, F x * ψ (H*x)) = c * ∑ x, F x * ψ (((u : R)*H)*x) := by
    rw [← Equiv.sum_comp u.mulLeft (fun x => F x * ψ (H*x))]
    simp only [Units.mulLeft_apply, hF, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [show H*((u : R)*x) = ((u : R)*H)*x by ring]
    ring
  rw [he, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

theorem barePhysicalFourier_unit_frequency (A s : O)
    (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s}))
    (b H : O) (hcop : IsCoprime b (A*s)) :
    barePhysicalFourier A s (supportedElement_ne_zero A hA)
        (supportedElement_ne_zero s hs) (b*H) =
      ((idealRowHom b (Ideal.span {A}))⁻¹ * idealRowHom b (Ideal.span {s})) *
        barePhysicalFourier A s (supportedElement_ne_zero A hA)
          (supportedElement_ne_zero s hs) H := by
  have hAs := mul_ne_zero (supportedElement_ne_zero A hA) (supportedElement_ne_zero s hs)
  let := finite_quotient_span hAs
  let : Fintype (Residue (A*s)) := Fintype.ofFinite _
  let u := residueUnit (A*s) b hcop.symm
  have hcA := idealRowHom_ne_zero_of_coprime A b hA hcop.of_mul_right_left.symm
  have hcs := idealRowHom_ne_zero_of_coprime s b hs hcop.of_mul_right_right.symm
  have hF (x : Residue (A*s)) :
      movingQuotient A s (supportedElement_ne_zero s hs) ((u : Residue (A*s))*x) =
        (idealRowHom b (Ideal.span {A}) * (idealRowHom b (Ideal.span {s}))⁻¹) *
          movingQuotient A s (supportedElement_ne_zero s hs) x := by
    exact movingQuotient_unit_scale A s hs b hcop.of_mul_right_right x
  have he := finite_fourier_unit_scale (movingQuotient A s (supportedElement_ne_zero s hs))
    (quotientTrace (A*s) hAs) u _ (mul_ne_zero hcA (inv_ne_zero hcs)) hF
    (Ideal.Quotient.mk _ H)
  unfold barePhysicalFourier elementFourier
  simp only [tsum_fintype]
  change (∑ x, movingQuotient A s (supportedElement_ne_zero s hs) x *
    quotientTrace (A*s) hAs (Ideal.Quotient.mk _ (b*H)*x)) =
      _ * ∑ x, movingQuotient A s (supportedElement_ne_zero s hs) x *
        quotientTrace (A*s) hAs (Ideal.Quotient.mk _ H*x)
  simpa only [u, residueUnit_coe, map_mul, mul_inv_rev, inv_inv, mul_comm] using he

theorem bareCongruenceCoefficient_unit_frequency (A s : O)
    (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s}))
    (b H : O) (hcop : IsCoprime b (A*s)) :
    bareCongruenceCoefficient A s (supportedElement_ne_zero A hA) (b*H) =
      ((idealRowHom b (Ideal.span {A}))⁻¹ * idealRowHom b (Ideal.span {s})) *
        bareCongruenceCoefficient A s (supportedElement_ne_zero A hA) H := by
  have he := barePhysicalFourier_unit_frequency A s hA hs b H hcop
  simp only [barePhysicalFourier_eq] at he
  have hn : (Ideal.absNorm (Ideal.span {s}) : ℂ) ≠ 0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr (supportedElement_ne_zero s hs))
  apply mul_left_cancel₀ hn
  rw [he]
  ring

lemma idealRowHom_norm_one_of_coprime (s b : O)
    (hs : Supported (Ideal.span {s})) (hcop : IsCoprime b s) :
    ‖idealRowHom b (Ideal.span {s})‖ = 1 := by
  have h6 := idealRowHom_sixth_mask b (Ideal.span {s}) hs
  rw [idealRowHom_argument_pow _ _ _ hs,
    ite_eq_left ((Ideal.isCoprime_span_singleton_iff s b).mpr hcop.symm)] at h6
  exact Complex.norm_eq_one_of_pow_eq_one h6 (by decide : (6 : ℕ) ≠ 0)

theorem bareCongruenceCoefficient_unit_frequency_norm (A s : O)
    (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s}))
    (b H : O) (hcop : IsCoprime b (A*s)) :
    ‖bareCongruenceCoefficient A s (supportedElement_ne_zero A hA) (b*H)‖ =
      ‖bareCongruenceCoefficient A s (supportedElement_ne_zero A hA) H‖ := by
  rw [bareCongruenceCoefficient_unit_frequency A s hA hs b H hcop,
    norm_mul, norm_mul, norm_inv,
    idealRowHom_norm_one_of_coprime A b hA hcop.of_mul_right_left,
    idealRowHom_norm_one_of_coprime s b hs hcop.of_mul_right_right,
    inv_one, one_mul, one_mul]

theorem bareCongruenceCoefficient_unit_frequency_eq_zero_iff (A s : O)
    (hA : Supported (Ideal.span {A})) (hs : Supported (Ideal.span {s}))
    (b H : O) (hcop : IsCoprime b (A*s)) :
    bareCongruenceCoefficient A s (supportedElement_ne_zero A hA) (b*H) = 0 ↔
      bareCongruenceCoefficient A s (supportedElement_ne_zero A hA) H = 0 := by
  rw [← norm_eq_zero, bareCongruenceCoefficient_unit_frequency_norm A s hA hs b H hcop,
    norm_eq_zero]

lemma supported_element_power (p : O) (hs : Supported (Ideal.span {p})) (n : ℕ) :
    Supported (Ideal.span {p^n}) := by
  rw [← Ideal.span_singleton_pow]
  exact supported_pow hs n

lemma idealRowHom_prime_power_value (p b : O) [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (n : ℕ) :
    idealRowHom b (Ideal.span {p^n}) =
      (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^n := by
  rw [← Ideal.span_singleton_pow, map_pow, idealRowHom_prime _ _ hg]

lemma actualSextic_unit_power_ne_zero (p b : O) [(Ideal.span {p} : Ideal O).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hcop : IsCoprime b p) (t : ℕ) :
    (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^t ≠ 0 := by
  apply pow_ne_zero
  exact (actualSextic (Ideal.span {p}) hg).apply_ne_zero_iff.mpr
    ((isUnit_quotient_span_iff p b).mpr hcop.symm)

theorem bareCongruenceCoefficient_prime_power_unit_frequency (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal] (hs : Supported (Ideal.span {p}))
    (hg : goodLambda ∉ Ideal.span {p}) (b : O) (hcop : IsCoprime b p) (t k j : ℕ) :
    bareCongruenceCoefficient (p^t) (p^k) (pow_ne_zero _ hp.ne_zero) (b*p^j) =
      ((actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^k /
        (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^t) *
          bareCongruenceCoefficient (p^t) (p^k) (pow_ne_zero _ hp.ne_zero) (p^j) := by
  have he := bareCongruenceCoefficient_unit_frequency (p^t) (p^k)
    (supported_element_power p hs t) (supported_element_power p hs k) b (p^j)
    (hcop.pow_right.mul_right hcop.pow_right)
  simpa only [idealRowHom_prime_power_value p b hg, div_eq_mul_inv, mul_comm] using he

theorem bareCongruenceCoefficient_all_prime_powers_unit (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal] (hs : Supported (Ideal.span {p}))
    (hg : goodLambda ∉ Ideal.span {p}) (b : O) (hcop : IsCoprime b p) (t k j : ℕ) :
    bareCongruenceCoefficient (p^t) (p^k) (pow_ne_zero _ hp.ne_zero) (b*p^j) =
      ((actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^k /
        (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^t) *
          sourceScalar p hp hg t k j := by
  rw [bareCongruenceCoefficient_prime_power_unit_frequency p hp hs hg b hcop t k j,
    bareCongruenceCoefficient_all_prime_powers p hp hg t k j]

theorem barePhysicalFourier_all_prime_powers_unit (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal] (hs : Supported (Ideal.span {p}))
    (hg : goodLambda ∉ Ideal.span {p}) (b : O) (hcop : IsCoprime b p) (t k j : ℕ) :
    barePhysicalFourier (p^t) (p^k) (pow_ne_zero _ hp.ne_zero)
        (pow_ne_zero _ hp.ne_zero) (b*p^j) =
      (Ideal.absNorm (Ideal.span {p^k}) : ℂ) *
        (((actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^k /
          (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ b))^t) *
            sourceScalar p hp hg t k j) := by
  rw [barePhysicalFourier_eq,
    bareCongruenceCoefficient_all_prime_powers_unit p hp hs hg b hcop t k j]

theorem bareCongruenceCoefficient_all_prime_powers_unit_norm (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal] (hs : Supported (Ideal.span {p}))
    (hg : goodLambda ∉ Ideal.span {p}) (b : O) (hcop : IsCoprime b p) (t k j : ℕ) :
    ‖bareCongruenceCoefficient (p^t) (p^k) (pow_ne_zero _ hp.ne_zero) (b*p^j)‖ =
      ‖sourceScalar p hp hg t k j‖ := by
  have he := bareCongruenceCoefficient_unit_frequency_norm (p^t) (p^k)
    (supported_element_power p hs t) (supported_element_power p hs k) b (p^j)
    (hcop.pow_right.mul_right hcop.pow_right)
  rw [bareCongruenceCoefficient_all_prime_powers p hp hg t k j] at he
  exact he

end SevenEighths.ProbePhysical
end

end OAI

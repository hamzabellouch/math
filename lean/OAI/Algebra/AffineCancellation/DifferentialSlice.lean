import OAI.Algebra.AffineCancellation.Model

namespace OAI

noncomputable section

namespace ComplexCancellation.DifferentialSlice
open Polynomial
variable {k K : Type*} [CommRing k] [Field K] [CharZero K] [Algebra k K]

/-- The field of constants of a derivation on a field. -/
def constants (D : Derivation k K K) : Subfield K where
  carrier := {r | D r = 0}
  zero_mem' := map_zero D
  one_mem' := D.map_one_eq_zero
  add_mem' := by
    intro r s hr hs
    change D r = 0 at hr
    change D s = 0 at hs
    change D (r+s) = 0
    rw [map_add, hr, hs, add_zero]
  mul_mem' := by
    intro r s hr hs
    change D r = 0 at hr
    change D s = 0 at hs
    change D (r*s) = 0
    rw [Derivation.leibniz, hr, hs, smul_zero, smul_zero, add_zero]
  neg_mem' := by
    intro r hr
    change D r = 0 at hr
    change D (-r) = 0
    rw [map_neg, hr, neg_zero]
  inv_mem' := by
    intro r hr
    change D r = 0 at hr
    change D r⁻¹ = 0
    rw [Derivation.leibniz_inv, hr, smul_zero]

omit [CharZero K] in
lemma derivative_eval (D : Derivation k K K) {t : K} (ht : D t = 1)
    (p : Polynomial (constants D)) :
    D (aeval t p) = aeval t p.derivative := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial n c =>
    simp only [aeval_monomial, derivative_monomial, map_mul, map_natCast,
      aeval_monomial, Derivation.leibniz, Derivation.leibniz_pow, ht, smul_eq_mul, nsmul_eq_mul]
    have hc : D (c : K) = 0 := c.property
    change (c:K) * ((n:K) * (t^(n-1) * 1)) + t^n * D (c:K) =
      (c:K) * (n:K) * t^(n-1)
    rw [hc]
    ring

lemma eval_injective (D : Derivation k K K) {t : K} (ht : D t = 1) :
    Function.Injective (aeval t : Polynomial (constants D) →ₐ[constants D] K) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro p
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with
  | h n ih =>
    intro hp
    by_cases hdeg : p.natDegree = 0
    · rw [eq_C_of_natDegree_eq_zero hdeg] at hp ⊢
      simp only [aeval_C, map_eq_zero] at hp ⊢
      exact hp
    · have hder : p.derivative = 0 := ih p.derivative.natDegree (by rw [← hn]; exact natDegree_derivative_lt hdeg) p.derivative rfl (by
        rw [← derivative_eval D ht, hp, map_zero])
      have hc := eq_C_of_derivative_eq_zero hder
      rw [hc] at hp ⊢
      simp only [aeval_C, map_eq_zero] at hp ⊢
      exact hp

lemma exists_antiderivative {F : Type*} [Field F] [CharZero F] (p : Polynomial F) :
    ∃ q : Polynomial F, q.derivative = p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨p', hp'⟩ := hp
    obtain ⟨q', hq'⟩ := hq
    exact ⟨p'+q', by rw [derivative_add, hp', hq']⟩
  | monomial n c =>
    refine ⟨monomial (n+1) (c / (n+1)), ?_⟩
    rw [derivative_monomial]
    have hn : (n:F)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    simp [hn]

lemma nilpotent_is_polynomial (D : Derivation k K K) {t r : K} (ht : D t = 1)
    (hr : ∃ n : ℕ, (D : K → K)^[n] r = 0) :
    ∃ p : Polynomial (constants D), aeval t p = r := by
  obtain ⟨n, hr⟩ := hr
  induction n generalizing r with
  | zero => exact ⟨0, by simpa using hr.symm⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply] at hr
    obtain ⟨p, hp⟩ := ih hr
    obtain ⟨q, hqp⟩ := exists_antiderivative p
    have hq : D (aeval t q) = D r := by
      rw [derivative_eval D ht]
      rw [hqp, hp]
    let c : constants D := ⟨r - aeval t q, by change D (r-aeval t q) = 0; rw [map_sub, hq, sub_self]⟩
    refine ⟨q + C c, ?_⟩
    simp only [map_add, aeval_C]
    change aeval t q + (r - aeval t q) = r
    ring

end ComplexCancellation.DifferentialSlice

end

end OAI

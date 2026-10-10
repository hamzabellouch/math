import OAI.NumberTheory.TotientAsymptotic.OrderedFactorizations
import OAI.NumberTheory.TotientAsymptotic.ResidualFactorCount

namespace OAI

/-! Removing one designated prime from a factorization and reconstructing it. -/
noncomputable section
open scoped BigOperators
namespace TotientAsymptotic

def divideFactor {k : ℕ} (i : Fin k) (q : ℕ) (f : Fin k → ℕ) : Fin k → ℕ :=
  Function.update f i (f i/q)

lemma multiply_divideFactor {k : ℕ} (i : Fin k) (q : ℕ) (f : Fin k → ℕ)
    (hq : q ∣ f i) : multiplyFactor i q (divideFactor i q f)=f := by
  funext j
  by_cases hj : j=i
  · subst j
    simp [multiplyFactor,divideFactor,Nat.mul_div_cancel' hq]
  · simp [multiplyFactor,divideFactor,hj]

lemma prod_divideFactor {k : ℕ} (i : Fin k) (q : ℕ) (f : Fin k → ℕ)
    (hq : q ∣ f i) : q*(∏ j,divideFactor i q f j)=∏ j,f j := by
  rw [← prod_multiplyFactor,multiply_divideFactor i q f hq]

lemma divideFactor_prod_dvd {k : ℕ} (i : Fin k) (q : ℕ) (f : Fin k → ℕ)
    (hq : q ∣ f i) : (∏ j,divideFactor i q f j) ∣ ∏ j,f j :=
  ⟨q,by rw [mul_comm,prod_divideFactor i q f hq]⟩

lemma divideFactor_prod_pos {k : ℕ} (i : Fin k) (q : ℕ) (f : Fin k → ℕ)
    (hq : q ∣ f i) (hf : 0 < ∏ j,f j) : 0 < ∏ j,divideFactor i q f j := by
  have hh := prod_divideFactor i q f hq
  rw [← hh] at hf
  by_contra h
  have hz := Nat.eq_zero_of_not_pos h
  simp only [hz,mul_zero,lt_self_iff_false] at hf

lemma divideFactor_prod_omega_le {k : ℕ} (i : Fin k) (q : ℕ) (f : Fin k → ℕ)
    (hq : q ∣ f i) (hf : 0 < ∏ j,f j) :
    (∏ j,divideFactor i q f j).primeFactorsList.length ≤ (∏ j,f j).primeFactorsList.length :=
  (Nat.primeFactorsList_sublist_of_dvd (divideFactor_prod_dvd i q f hq) hf.ne').length_le

lemma divideFactor_prod_factors {k : ℕ} (i : Fin k) (q : ℕ) (f : Fin k → ℕ)
    (hq : q ∣ f i) (hf : 0 < ∏ j,f j) :
    (∏ j,divideFactor i q f j).primeFactorsList ⊆ (∏ j,f j).primeFactorsList :=
  Nat.primeFactorsList_subset_of_dvd (divideFactor_prod_dvd i q f hq) hf.ne'

end TotientAsymptotic

end

end OAI

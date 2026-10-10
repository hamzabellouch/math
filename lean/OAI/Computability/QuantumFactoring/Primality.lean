import Mathlib

namespace OAI

section


/-! Necessary exact primality component of Appendix A.  The tests are polynomial
congruences, not a primality oracle.  These lemmas start the appendix's actual
root-count proof; no polynomial-time implementation is assumed here. -/
namespace ExactQuantumFactoring.Primality
open Polynomial
open scoped BigOperators

/-- The evaluation form of an introspective exponent modulo X^s-1. -/
def Introspective {F : Type*} [CommRing F] (s k : ℕ) (f : F[X]) : Prop :=
  ∀ z : F, z^s = 1 → (f.eval z)^k = f.eval (z^k)

lemma Introspective.one {F : Type*} [CommRing F] (s : ℕ) (f : F[X]) :
    Introspective s 1 f := by intro z _; simp

lemma Introspective.mul_exp {F : Type*} [CommRing F] {s k l : ℕ} {f : F[X]}
    (hk : Introspective s k f) (hl : Introspective s l f) :
    Introspective s (k*l) f := by
  intro z hz
  rw [pow_mul, hk z hz, hl]
  · rw [pow_mul]
  · rw [← pow_mul, Nat.mul_comm, pow_mul, hz, one_pow]

lemma Introspective.pow_exp {F : Type*} [CommRing F] {s k : ℕ} {f : F[X]}
    (hk : Introspective s k f) (u : ℕ) : Introspective s (k^u) f := by
  induction u with
  | zero => simpa using Introspective.one s f
  | succ u hu => simpa [pow_succ] using hu.mul_exp hk

lemma Introspective.mul_poly {F : Type*} [CommRing F] {s k : ℕ} {f g : F[X]}
    (hf : Introspective s k f) (hg : Introspective s k g) :
    Introspective s k (f*g) := by
  intro z hz
  simp only [eval_mul, mul_pow]
  rw [hf z hz, hg z hz]

lemma Introspective.prod {F ι : Type*} [CommRing F] {s k : ℕ}
    (S : Finset ι) (f : ι → F[X]) (hf : ∀ i ∈ S, Introspective s k (f i)) :
    Introspective s k (∏ i ∈ S, f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => intro z _; simp
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).mul_poly
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

/-- A successful congruence test implies the evaluation identity at every
s-th root. This implication includes the zero polynomial case correctly. -/
lemma introspective_of_congruence {F : Type*} [CommRing F] {s k : ℕ} {f : F[X]}
    (h : X^s - 1 ∣ f^k - f.comp (X^k)) : Introspective s k f := by
  intro z hz
  obtain ⟨q, hq⟩ := h
  have hzq := congrArg (Polynomial.eval z) hq
  simpa [hz, sub_eq_zero] using hzq

lemma natCast_frobenius {F : Type*} [CommRing F] (p : ℕ) [Fact p.Prime] [CharP F p]
    (a : ℕ) : (a : F)^p = (a : F) := by
  exact map_natCast (frobenius F p) a

lemma linear_frobenius {F : Type*} [CommRing F] (p : ℕ) [Fact p.Prime] [CharP F p]
    (s a : ℕ) : Introspective s p (X + C (a : F)) := by
  intro z _
  simp only [eval_add, eval_X, eval_C]
  rw [add_pow_char, natCast_frobenius]

/-- Every product tested in the root count propagates along m^u p^v, precisely
as in equation (A.4); no division by its value at a root is involved. -/
lemma propagate {F ι : Type*} [CommRing F] (p : ℕ) [Fact p.Prime] [CharP F p]
    (s m : ℕ) (S : Finset ι) (a : ι → ℕ)
    (htest : ∀ i ∈ S, Introspective s m (X+C (a i : F))) (u v : ℕ) :
    Introspective s (m^u*p^v) (∏ i ∈ S, (X+C (a i : F))) := by
  apply Introspective.mul_exp
  · exact (Introspective.prod S _ htest).pow_exp u
  · exact (Introspective.prod S _ (fun i _ => linear_frobenius p s (a i))).pow_exp v

end ExactQuantumFactoring.Primality


end

end OAI

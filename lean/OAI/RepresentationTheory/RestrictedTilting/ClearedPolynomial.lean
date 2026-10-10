import Mathlib

namespace OAI

namespace FiberFunctorProof
open scoped BigOperators
section
variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
 

def clearedPolynomial (p : Polynomial k) (a b : R) (d : ℕ) : R :=
  ∑ n ∈ Finset.range (d+1), algebraMap k R (p.coeff n) * a^n * b^(d-n)

lemma map_clearedPolynomial {S : Type*} [CommRing S] [Algebra k S]
    (f : R →ₐ[k] S) (p : Polynomial k) (a b : R) (d : ℕ) :
    f (clearedPolynomial p a b d) = clearedPolynomial p (f a) (f b) d := by
  simp only [clearedPolynomial, map_sum, map_mul, map_pow, AlgHom.commutes]

lemma clearedPolynomial_eval {L : Type*} [Field L] [Algebra k L]
    (f : R →ₐ[k] L) (p : Polynomial k) (a b : R) (d : ℕ)
    (hd : p.natDegree ≤ d) (hb : f b ≠ 0) :
    f (clearedPolynomial p a b d) = f b ^ d * Polynomial.aeval (f a * (f b)⁻¹) p := by
  rw [Polynomial.aeval_eq_sum_range' (Nat.lt_succ_of_le hd), Finset.mul_sum]
  simp only [clearedPolynomial, map_sum, map_mul, map_pow, AlgHom.commutes]
  apply Finset.sum_congr rfl
  intro n hn
  rw [pow_sub₀ _ hb (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)), mul_pow, inv_pow]
  simp only [Algebra.smul_def]
  ring
end

section
variable (k : Type*) [Field k]
noncomputable def linePolynomial : MvPolynomial (Fin 2) k →ₐ[k] Polynomial k :=
  MvPolynomial.aeval (fun i => if i = 0 then Polynomial.X else 0)

@[simp] lemma linePolynomial_eval (a : k) (P : MvPolynomial (Fin 2) k) :
    (linePolynomial k P).eval a = MvPolynomial.eval (fun i => if i = 0 then a else 0) P := by
  change (Polynomial.aeval a).comp (linePolynomial k) P = _
  have he : (Polynomial.aeval a).comp (linePolynomial k) =
      MvPolynomial.aeval (fun i => if i = 0 then a else 0) := by
    ext i
    simp only [AlgHom.comp_apply, linePolynomial, MvPolynomial.aeval_X]
    split_ifs <;> simp
  rw [he]
  rfl

noncomputable def clearedLineAction (p : Polynomial k) (t : k) (d : ℕ) : Polynomial k :=
  clearedPolynomial p (Polynomial.C t) ((Polynomial.X : Polynomial k)^2) d

lemma clearedLineAction_eval (p : Polynomial k) (t a : k) (d : ℕ)
    (hd : p.natDegree ≤ d) (ha : a ≠ 0) :
    (clearedLineAction k p t d).eval a = a^(2*d) * p.eval (t / a^2) := by
  have h := clearedPolynomial_eval (Polynomial.aeval a) p
    (Polynomial.C t) ((Polynomial.X : Polynomial k)^2) d hd (by simpa using pow_ne_zero 2 ha)
  simpa [clearedLineAction, Polynomial.aeval_def, Algebra.algebraMap_self,
    ← pow_mul, div_eq_mul_inv] using h
end
end FiberFunctorProof

end OAI

import OAI.NumberTheory.Jacobsthal.Estimates.LineSubstitution

namespace OAI

namespace Erdos970

section

namespace ErdosAuxiliaryPolynomial

theorem lineSub_eval {R : Type*} [CommRing R] (φ : ℤ →+* R) (a s z : R)
    (Q : MvPolynomial (Fin 2) ℤ) :
    (lineSub φ a s Q).eval z = MvPolynomial.eval₂Hom φ ![z,a-s*z] Q := by
  have he : (Polynomial.evalRingHom z).comp (lineSub φ a s) =
      MvPolynomial.eval₂Hom φ ![z,a-s*z] := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [lineSub]
    · intro i
      fin_cases i <;> simp [lineSub]
  exact congrArg (fun f : MvPolynomial (Fin 2) ℤ →+* R => f Q) he

theorem eval_integer_cast {R : Type*} [CommRing R] (Q : MvPolynomial (Fin 2) ℤ) (x y : ℤ) :
    MvPolynomial.eval₂Hom (Int.castRingHom R) ![(x : R),(y : R)] Q =
      (MvPolynomial.eval ![x,y] Q : R) := by
  have he : (Int.castRingHom R) ∘ (![x,y] : Fin 2 → ℤ) = ![(x : R),(y : R)] := by
    funext i
    fin_cases i <;> rfl
  have h := MvPolynomial.eval₂_comp (Int.castRingHom R) ![x,y] Q
  rw [he] at h
  exact h.symm

theorem divides_of_line_incidence (p : ℕ) (Q : MvPolynomial (Fin 2) ℤ) (a s : ZMod p)
    (x y : ℤ) (hline : lineSub (Int.castRingHom (ZMod p)) a s Q = 0)
    (hinc : (y : ZMod p) = a-s*(x : ZMod p)) : (p : ℤ) ∣ MvPolynomial.eval ![x,y] Q := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
  rw [← eval_integer_cast,hinc,← lineSub_eval,hline,Polynomial.eval_zero]

theorem zero_of_prime_product_large (n : ℤ) (I : Finset ℕ)
    (hprime : ∀ p ∈ I, Nat.Prime p) (hdiv : ∀ p ∈ I, (p : ℤ) ∣ n)
    (hlarge : |(n : ℝ)| < ((∏ p ∈ I, p : ℕ) : ℝ)) : n = 0 := by
  by_contra hn
  have hd : (∏ p ∈ I, p) ∣ n.natAbs :=
    Finset.prod_primes_dvd n.natAbs (fun p hp => (hprime p hp).prime)
      (fun p hp => Int.natCast_dvd.mp (hdiv p hp))
  have hle : (∏ p ∈ I, p) ≤ n.natAbs := Nat.le_of_dvd (Int.natAbs_pos.mpr hn) hd
  have habs : (n.natAbs : ℝ) = |(n : ℝ)| := by rw [Nat.cast_natAbs,Int.cast_abs]
  have hleR : ((∏ p ∈ I, p : ℕ) : ℝ) ≤ |(n : ℝ)| := by
    rw [← habs]
    exact_mod_cast hle
  exact (not_lt_of_ge hleR) hlarge

theorem value_zero_of_incident_prime_product (Q : MvPolynomial (Fin 2) ℤ) (D H : ℕ)
    (hD : Q.totalDegree ≤ D) (hH : ∀ m : Fin 2 →₀ ℕ, |Q.coeff m| ≤ (H : ℤ))
    (S : ℝ) (x y : ℤ) (hx : 0 ≤ (x : ℝ) ∧ (x : ℝ) ≤ S) (hy : 0 ≤ (y : ℝ) ∧ (y : ℝ) ≤ S)
    (I : Finset ℕ) (hprime : ∀ p ∈ I, Nat.Prime p)
    (a s : ∀ p : I, ZMod p.val)
    (hline : ∀ p : I, lineSub (Int.castRingHom (ZMod p.val)) (a p) (s p) Q = 0)
    (hinc : ∀ p : I, (y : ZMod p.val) = a p-s p*(x : ZMod p.val))
    (hlarge : ((D+2).choose 2 : ℝ)*(H : ℝ)*(max 1 S)^D < ((∏ p ∈ I, p : ℕ) : ℝ)) :
    MvPolynomial.eval ![x,y] Q = 0 := by
  apply zero_of_prime_product_large _ I hprime
  · intro p hp
    exact divides_of_line_incidence p Q (a ⟨p,hp⟩) (s ⟨p,hp⟩) x y (hline ⟨p,hp⟩) (hinc ⟨p,hp⟩)
  · exact (polynomial_value_bound Q D H hD hH S x y hx hy).trans_lt hlarge

end ErdosAuxiliaryPolynomial

end

end Erdos970

end OAI

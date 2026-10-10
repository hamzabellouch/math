import OAI.NumberTheory.Jacobsthal.Estimates.FactorDividesAbscissa

namespace OAI

namespace Erdos970

section

namespace ErdosPrimitiveIntercept
open ErdosRichLine ErdosInverseAlignment

theorem InterceptReduction.prime_alignment {l : PrimitiveIntegerLine} (r : InterceptReduction l)
    (a : ℕ → ℤ) (p : ℤ × ℤ) (hp : l.Contains p) (ell : ℕ) (hell : Nat.Prime ell)
    (hx : (ell : ℤ) ∣ p.1) (hclass : (p.2 : ZMod ell) = (a ell : ZMod ell))
    (hfactor : ¬ell ∣ r.factor) : aligns a r.rational ell := by
  let : Fact (Nat.Prime ell) := ⟨hell⟩
  have hg : (r.factor : ZMod ell) ≠ 0 := (ZMod.natCast_eq_zero_iff _ _).not.mpr hfactor
  have hx0 : (p.1 : ZMod ell) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hx
  unfold PrimitiveIntegerLine.Contains at hp
  rw [r.denominator_eq,r.intercept_eq] at hp
  have hh := congrArg (fun n : ℤ => (n : ZMod ell)) hp
  have he : (r.factor : ZMod ell)*((r.rational.den : ZMod ell)*(a ell : ZMod ell)) =
      (r.factor : ZMod ell)*(r.rational.num : ZMod ell) := by
    simpa only [Int.cast_mul,Int.cast_add,Int.cast_natCast,Nat.cast_mul,hx0,
      mul_zero,zero_add,hclass,mul_assoc] using hh
  exact mul_left_cancel₀ hg he

theorem InterceptReduction.nonaligned_prime_dvd_factor {l : PrimitiveIntegerLine}
    (r : InterceptReduction l) (a : ℕ → ℤ) (p : ℤ × ℤ) (hp : l.Contains p)
    (ell : ℕ) (hell : Nat.Prime ell) (hx : (ell : ℤ) ∣ p.1)
    (hclass : (p.2 : ZMod ell) = (a ell : ZMod ell)) (hna : ¬aligns a r.rational ell) :
    ell ∣ r.factor := by
  by_contra hh
  exact hna (r.prime_alignment a p hp ell hell hx hclass hh)

end ErdosPrimitiveIntercept

end

section

namespace ErdosPrimitiveIntercept
open ErdosRichLine ErdosInverseAlignment

noncomputable def badPrimeFactors (a : ℕ → ℤ) (t : ℚ) (q : ℕ) : Finset ℕ := by
  classical
  exact q.primeFactors.filter (fun ell => ¬aligns a t ell)

noncomputable def badPrimeProduct (a : ℕ → ℤ) (t : ℚ) (q : ℕ) : ℕ :=
  ∏ ell ∈ badPrimeFactors a t q, ell

theorem InterceptReduction.bad_product_dvd_factor {l : PrimitiveIntegerLine}
    (r : InterceptReduction l) (a : ℕ → ℤ) (q : ℕ) (b : ℤ)
    (hp : l.Contains ((q : ℤ),b))
    (hclass : ∀ ell ∈ q.primeFactors, (b : ZMod ell) = (a ell : ZMod ell)) :
    badPrimeProduct a r.rational q ∣ r.factor := by
  classical
  apply Finset.prod_primes_dvd r.factor
  · intro ell hell
    exact (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hell).1).prime
  · intro ell hell
    obtain ⟨hfactor,hna⟩ := Finset.mem_filter.mp hell
    have he := Nat.mem_primeFactors.mp hfactor
    exact r.nonaligned_prime_dvd_factor a ((q : ℤ),b) hp ell he.1
      (by change (ell : ℤ) ∣ (q : ℤ);exact_mod_cast he.2.1) (hclass ell hfactor) hna

theorem InterceptReduction.structure_bound {l : PrimitiveIntegerLine}
    (r : InterceptReduction l) (a : ℕ → ℤ) (q : ℕ) (b : ℤ)
    (hp : l.Contains ((q : ℤ),b))
    (hclass : ∀ ell ∈ q.primeFactors, (b : ZMod ell) = (a ell : ZMod ell)) :
    r.rational.den*badPrimeProduct a r.rational q ≤ l.denominator := by
  have hle := Nat.le_of_dvd r.factor_pos (r.bad_product_dvd_factor a q b hp hclass)
  calc
    _ ≤ r.rational.den*r.factor := Nat.mul_le_mul_left _ hle
    _ = l.denominator := by rw [r.denominator_eq,mul_comm]

end ErdosPrimitiveIntercept

end

end Erdos970

end OAI

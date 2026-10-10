import Mathlib.RingTheory.Coprime.Lemmas
import OAI.Analysis.Laughlin.Polynomial.BracketCoprime
import OAI.Analysis.Laughlin.Polynomial.Polynomial

namespace OAI

namespace Laughlin
open scoped BigOperators

def orderedPairs (N : ℕ) : Finset (Fin N × Fin N) :=
  Finset.univ.filter (fun ij => ij.1 < ij.2)

theorem laughlinPolynomial_eq_orderedProduct (N : ℕ) :
    laughlinPolynomial N = ∏ ij ∈ orderedPairs N, bracket ij.1 ij.2 ^ 3 := by
  unfold laughlinPolynomial orderedPairs
  rw [Finset.prod_filter, Fintype.prod_prod_type]

theorem laughlinPolynomial_dvd_of_pair_cubes {N : ℕ}
    (P : MvPolynomial (SpinorVariables N) ℂ)
    (h : ∀ i j : Fin N, i < j → bracket i j ^ 3 ∣ P) :
    laughlinPolynomial N ∣ P := by
  rw [laughlinPolynomial_eq_orderedProduct]
  apply Finset.prod_dvd_of_isRelPrime
  · rintro ⟨i,j⟩ hij ⟨k,l⟩ hkl hne
    exact (bracket_isRelPrime i j k l (Finset.mem_filter.mp hij).2
      (Finset.mem_filter.mp hkl).2 hne).pow
  · rintro ⟨i,j⟩ hij
    exact h i j (Finset.mem_filter.mp hij).2

theorem laughlinPolynomial_dvd_iff_pair_cubes {N : ℕ}
    (P : MvPolynomial (SpinorVariables N) ℂ) :
    laughlinPolynomial N ∣ P ↔ ∀ i j : Fin N, i < j → bracket i j ^ 3 ∣ P := by
  constructor
  · intro h i j hij
    exact (bracket_cube_dvd_laughlin hij).trans h
  · exact laughlinPolynomial_dvd_of_pair_cubes P

end Laughlin

end OAI

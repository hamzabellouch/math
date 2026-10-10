import OAI.NumberTheory.PiExponent.LocalAlgebra.ColonHilbertStep
import OAI.NumberTheory.PiExponent.LocalAlgebra.PositiveDimensionalHilbert

namespace OAI

namespace PiExponentJets.W64

attribute [local instance] MvPolynomial.gradedAlgebra
variable {k σ : Type*} [Field k] [Finite σ]

noncomputable def shiftHilbertPolynomial (p : Polynomial ℚ) (d : ℕ) : Polynomial ℚ :=
  p.comp (Polynomial.X - Polynomial.C (d : ℚ))

@[simp] theorem shiftHilbertPolynomial_eval (p : Polynomial ℚ) (d n : ℕ)
    (hdn : d ≤ n) :
    (shiftHilbertPolynomial p d).eval (n : ℚ) = p.eval ((n-d : ℕ) : ℚ) := by
  simp [shiftHilbertPolynomial, Polynomial.eval_comp, Nat.cast_sub hdn]

@[simp] theorem shiftHilbertPolynomial_natDegree (p : Polynomial ℚ) (d : ℕ) :
    (shiftHilbertPolynomial p d).natDegree = p.natDegree := by
  rw [shiftHilbertPolynomial, Polynomial.natDegree_comp,
    Polynomial.natDegree_X_sub_C, mul_one]

@[simp] theorem shiftHilbertPolynomial_leadingCoeff (p : Polynomial ℚ) (d : ℕ) :
    (shiftHilbertPolynomial p d).leadingCoeff = p.leadingCoeff := by
  rw [shiftHilbertPolynomial, Polynomial.leadingCoeff_comp]
  · rw [Polynomial.leadingCoeff_X_sub_C, one_pow, mul_one]
  · rw [Polynomial.natDegree_X_sub_C]
    exact one_ne_zero

theorem shiftHilbertPolynomial_top_coeff (p : Polynomial ℚ) (d t : ℕ)
    (hp : p.natDegree ≤ t) :
    (shiftHilbertPolynomial p d).coeff t = p.coeff t := by
  by_cases he : p.natDegree = t
  · rw [← he]
    calc
      (shiftHilbertPolynomial p d).coeff p.natDegree =
          (shiftHilbertPolynomial p d).coeff (shiftHilbertPolynomial p d).natDegree := by
            rw [shiftHilbertPolynomial_natDegree]
      _ = (shiftHilbertPolynomial p d).leadingCoeff := Polynomial.coeff_natDegree
      _ = p.leadingCoeff := shiftHilbertPolynomial_leadingCoeff p d
      _ = p.coeff p.natDegree := Polynomial.coeff_natDegree.symm
  · have ht : p.natDegree < t := lt_of_le_of_ne hp he
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt
      (by simpa using ht : (shiftHilbertPolynomial p d).natDegree < t),
      Polynomial.coeff_eq_zero_of_natDegree_lt ht]

theorem hilbertMultiplicity_shift (p : Polynomial ℚ) (d r : ℕ)
    (hp : p.natDegree ≤ r-1) :
    hilbertMultiplicity (shiftHilbertPolynomial p d) r = hilbertMultiplicity p r := by
  unfold hilbertMultiplicity
  rw [shiftHilbertPolynomial_top_coeff p d (r-1) hp]

theorem hilbertMultiplicity_add (p q : Polynomial ℚ) (r : ℕ) :
    hilbertMultiplicity (p+q) r = hilbertMultiplicity p r + hilbertMultiplicity q r := by
  simp [hilbertMultiplicity, add_mul]

theorem colon_hilbert_polynomial_eventually
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d)
    (pJ pP : Polynomial ℚ) (NJ NP : ℕ)
    (hJ : ∀ n : ℕ, NJ < n →
      (Module.finrank k (quotientSection (Ideal.span {f} ⊔ I) n) : ℚ) = pJ.eval (n : ℚ))
    (hP : ∀ n : ℕ, NP < n →
      (Module.finrank k (quotientSection (I.colon {f}) n) : ℚ) = pP.eval (n : ℚ)) :
    ∀ n : ℕ, NJ + NP + d < n →
      (Module.finrank k (quotientSection I n) : ℚ) =
        (pJ + shiftHilbertPolynomial pP d).eval (n : ℚ) := by
  intro n hn
  have hdn : d ≤ n := by omega
  have hnJ : NJ < n := by omega
  have hnP : NP < n-d := by omega
  have h := colon_hilbert_step I hI f hf (n-d)
  rw [Nat.sub_add_cancel hdn] at h
  have hc : (Module.finrank k (quotientSection I n) : ℚ) =
      (Module.finrank k (quotientSection (Ideal.span {f} ⊔ I) n) : ℚ) +
      (Module.finrank k (quotientSection (I.colon {f}) (n-d)) : ℚ) := by
    exact_mod_cast h.symm
  rw [hc, hJ n hnJ, hP (n-d) hnP,
    Polynomial.eval_add, shiftHilbertPolynomial_eval pP d n hdn]

theorem colon_hilbert_polynomial_multiplicity
    (pJ pP : Polynomial ℚ) (d r : ℕ) (hP : pP.natDegree ≤ r-1) :
    hilbertMultiplicity (pJ + shiftHilbertPolynomial pP d) r =
      hilbertMultiplicity pJ r + hilbertMultiplicity pP r := by
  rw [hilbertMultiplicity_add, hilbertMultiplicity_shift pP d r hP]

end PiExponentJets.W64

end OAI

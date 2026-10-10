import OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertDifferenceDegree
import OAI.NumberTheory.PiExponent.Polynomials.ColonHilbertPolynomial

namespace OAI

namespace PiExponentJets.W64

attribute [local instance] MvPolynomial.gradedAlgebra
variable {k σ : Type*} [Field k] [Finite σ]

omit [Finite σ] in
theorem prime_quotient_right_regular (P : Ideal (MvPolynomial σ k)) [P.IsPrime]
    (f : MvPolynomial σ k) (hfP : f ∉ P) :
    IsRightRegular (Ideal.Quotient.mk P f) := by
  have hf0 : Ideal.Quotient.mk P f ≠ 0 := by
    intro hz
    exact hfP (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  intro x y hxy
  exact mul_right_cancel₀ hf0 hxy

theorem regular_hypersurface_polynomial_eventually
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d)
    (hreg : IsRightRegular (Ideal.Quotient.mk I f))
    (p : Polynomial ℚ) (N : ℕ)
    (hP : ∀ n : ℕ, N < n →
      (Module.finrank k (quotientSection I n) : ℚ) = p.eval (n : ℚ)) :
    ∀ n : ℕ, N+d < n →
      (Module.finrank k (quotientSection (Ideal.span {f} ⊔ I) n) : ℚ) =
        (p-shiftHilbertPolynomial p d).eval (n : ℚ) := by
  intro n hn
  have hdn : d ≤ n := by omega
  have hnP : N < n := by omega
  have hnshift : N < n-d := by omega
  have h := regular_hilbert_step I hI f hf hreg (n-d)
  rw [Nat.sub_add_cancel hdn] at h
  have hc : (Module.finrank k (quotientSection (Ideal.span {f} ⊔ I) n) : ℚ) +
      (Module.finrank k (quotientSection I (n-d)) : ℚ) =
      (Module.finrank k (quotientSection I n) : ℚ) := by
    exact_mod_cast h
  rw [hP n hnP, hP (n-d) hnshift] at hc
  rw [Polynomial.eval_sub, shiftHilbertPolynomial_eval p d n hdn]
  exact eq_sub_of_add_eq hc

theorem prime_hypersurface_actual_hilbert_degree
    (P : Ideal (MvPolynomial σ k)) [P.IsPrime]
    (hP : P.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d)
    (hfP : f ∉ P) (hd : 0 < d)
    (p : Polynomial ℚ) (N s : ℕ)
    (hp : ∀ n : ℕ, N < n →
      (Module.finrank k (quotientSection P n) : ℚ) = p.eval (n : ℚ))
    (hdegree : p.natDegree = s+1) :
    ∃ q : Polynomial ℚ,
      (∃ M : ℕ, ∀ n : ℕ, M < n →
        (Module.finrank k (quotientSection (Ideal.span {f} ⊔ P) n) : ℚ) = q.eval (n : ℚ)) ∧
      q.natDegree = s ∧
      q.leadingCoeff * (q.natDegree.factorial : ℚ) =
        (d : ℚ) * (p.leadingCoeff * (p.natDegree.factorial : ℚ)) := by
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  refine ⟨p-Polynomial.taylor (-(d : ℚ)) p, ⟨N+d, ?_⟩,
    (PiExponentJets.W27.backward_difference_degree_and_leading p s hdegree (d : ℚ) hdq).1,
    PiExponentJets.W27.backward_difference_multiplicity p s hdegree (d : ℚ) hdq⟩
  intro n hn
  rw [PiExponentJets.W27.backward_difference_eq_comp]
  exact regular_hypersurface_polynomial_eventually P hP f hf
    (prime_quotient_right_regular P f hfP) p N hp n hn

end PiExponentJets.W64

end OAI

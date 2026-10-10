import Mathlib.Algebra.Polynomial.Roots
import OAI.NumberTheory.PiExponent.LocalAlgebra.HilbertGrowthComparison
import OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeDegreeExistence
import OAI.NumberTheory.PiExponent.Polynomials.ColonHilbertPolynomial
import OAI.NumberTheory.PiExponent.Polynomials.HomogeneousHilbertPolynomial
import OAI.NumberTheory.PiExponent.Polynomials.HomogeneousPrimeFactor

namespace OAI

namespace PiExponentJets.W22

open PiExponentJets.W64
attribute [local instance] MvPolynomial.gradedAlgebra

variable {k σ : Type*} [Field k] [Fintype σ]

theorem polynomial_eq_of_nat_tail (p q : Polynomial ℚ) (N : ℕ)
    (h : ∀ n : ℕ, N < n → p.eval (n : ℚ) = q.eval (n : ℚ)) : p = q := by
  have hinj : Function.Injective (fun n : ℕ => ((N + 1 + n : ℕ) : ℚ)) := by
    intro a b hab
    change ((N + 1 + a : ℕ) : ℚ) = ((N + 1 + b : ℕ) : ℚ) at hab
    have hab' : N + 1 + a = N + 1 + b := by exact_mod_cast hab
    omega
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective hinj).mono
  rintro x ⟨n, rfl⟩
  exact h _ (by omega)

noncomputable def actualHP (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) : Polynomial ℚ :=
  (exists_homogeneous_hilbert_polynomial σ I hI).choose

theorem actualHP_eventually (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) :
    ∃ N : ℕ, ∀ n : ℕ, N < n →
      (Module.finrank k (quotientSection I n) : ℚ) = (actualHP I hI).eval (n : ℚ) :=
  (exists_homogeneous_hilbert_polynomial σ I hI).choose_spec

theorem actualHP_unique (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (p : Polynomial ℚ) (N : ℕ)
    (hp : ∀ n : ℕ, N < n →
      (Module.finrank k (quotientSection I n) : ℚ) = p.eval (n : ℚ)) :
    actualHP I hI = p := by
  obtain ⟨M, hM⟩ := actualHP_eventually I hI
  apply polynomial_eq_of_nat_tail _ _ (M + N)
  intro n hn
  exact (hM n (by omega)).symm.trans (hp n (by omega))

theorem actualHP_congr {I J : Ideal (MvPolynomial σ k)}
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) (h : I = J) :
    actualHP I hI = actualHP J hJ := by
  subst J
  rfl

theorem actualHP_top
    (h : (⊤ : Ideal (MvPolynomial σ k)).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule σ k)) : actualHP ⊤ h = 0 := by
  apply actualHP_unique _ h 0 0
  intro n _
  have hz : Module.finrank k (quotientSection (⊤ : Ideal (MvPolynomial σ k)) n) = 0 :=
    Module.finrank_eq_zero_of_subsingleton k _
  simp only [hz, Nat.cast_zero, Polynomial.eval_zero]

theorem actualHP_leadingCoeff_nonneg (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) :
    0 ≤ (actualHP I hI).leadingCoeff := by
  obtain ⟨N, hN⟩ := actualHP_eventually I hI
  apply W27.polynomial_leadingCoeff_nonneg_of_eventually_nonneg _ (N + 1)
  intro n hn
  rw [← hN n (by omega)]
  positivity

theorem actualHP_natDegree_antitone {I J : Ideal (MvPolynomial σ k)}
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (hJ : J.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) (hIJ : I ≤ J) :
    (actualHP J hJ).natDegree ≤ (actualHP I hI).natDegree := by
  by_cases hz : actualHP J hJ = 0
  · simp only [hz, Polynomial.natDegree_zero, Nat.zero_le]
  have hpos : 0 < (actualHP J hJ).leadingCoeff :=
    lt_of_le_of_ne (actualHP_leadingCoeff_nonneg J hJ)
      (Ne.symm (Polynomial.leadingCoeff_ne_zero.mpr hz))
  obtain ⟨NI, hNI⟩ := actualHP_eventually I hI
  obtain ⟨NJ, hNJ⟩ := actualHP_eventually J hJ
  apply W24.natDegree_le_of_eventual_polynomial_le _ _ hpos (NI + NJ + 1)
  intro n hn
  rw [← hNI n (by omega), ← hNJ n (by omega)]
  have hdim := (quotientSectionFactor I J hIJ n).finrank_range_le
  rw [LinearMap.range_eq_top.mpr (quotientSectionFactor_surjective I J hIJ n),
    finrank_top] at hdim
  exact_mod_cast hdim

theorem actualHP_colon_step (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d)
    (hJ : (Ideal.span {f} ⊔ I).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (hP : (I.colon {f}).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)) :
    actualHP I hI = actualHP (Ideal.span {f} ⊔ I) hJ +
      shiftHilbertPolynomial (actualHP (I.colon {f}) hP) d := by
  obtain ⟨NJ, hNJ⟩ := actualHP_eventually (Ideal.span {f} ⊔ I) hJ
  obtain ⟨NP, hNP⟩ := actualHP_eventually (I.colon {f}) hP
  apply actualHP_unique I hI _ (NJ + NP + d)
  exact colon_hilbert_polynomial_eventually I hI f hf _ _ NJ NP hNJ hNP

end PiExponentJets.W22

end OAI

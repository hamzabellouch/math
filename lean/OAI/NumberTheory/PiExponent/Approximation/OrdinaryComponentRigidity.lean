import OAI.NumberTheory.PiExponent.Approximation.GenericFibreRigidity
import OAI.NumberTheory.PiExponent.Jets.OrdinaryDerivativeIdeals
import OAI.NumberTheory.PiExponent.Jets.PrimeNormalCotangent

namespace OAI

noncomputable section
namespace PiExponent.OrdinaryComponentRigidity

open scoped BigOperators
open NormalBasisRigidity DerivativeIdeals

def NormalProductComparison {n : ℕ} (Q : Ideal (OrdinaryDerivatives.Polynomial n)) [Q.IsPrime]
    (w cost : Fin n → ℝ) (M : ℝ) : Prop :=
  ∀ A B : Finset (Fin n),
    IsNormalBasis (K := Q.ResidueField) (genericCoordinateNormals (primeResidueMap Q) Q) A →
    IsNormalBasis (K := Q.ResidueField) (genericCoordinateNormals (primeResidueMap Q) Q) B →
    (∏ j ∈ A, w j) ≤ M * ∏ j ∈ B, cost j

def PersistentNormalComparison {n : ℕ} (w cost : Fin n → ℝ) (M delta : ℝ)
    (f : OrdinaryDerivatives.Polynomial n) (d : ℕ)
    (P : Ideal (OrdinaryDerivatives.Polynomial n)) : Prop :=
  ∀ r : ℕ, r < d + 2 → ∀ Q : Ideal (OrdinaryDerivatives.Polynomial n), ∀ hQ : Q.IsPrime,
    Q ≤ P →
    Q ∈ (OrdinaryDerivatives.ideal n cost ((r : ℝ) * delta) f).minimalPrimes →
    Q ∈ (OrdinaryDerivatives.ideal n cost (((r : ℝ) + 1) * delta) f).minimalPrimes →
    1 ≤ Q.height → Q.height ≤ d →
    (∀ p ∈ OrdinaryDerivatives.ideal n cost ((r : ℝ) * delta) f,
      ∀ l : List (Fin n), wordCost cost l ≤ delta → OrdinaryDerivatives.word n l p ∈ Q) →
    @NormalProductComparison n Q hQ w cost M

theorem coordinate_constant_of_persistent_comparison {n : ℕ}
    (w cost : Fin n → ℝ) (M delta : ℝ) (hcost : ∀ i, 0 ≤ cost i) (hdelta : 0 ≤ delta)
    (f : OrdinaryDerivatives.Polynomial n) (hf : f ≠ 0) (d : ℕ)
    (P : Ideal (OrdinaryDerivatives.Polynomial n)) (hP : P.IsPrime) (hheight : P.height ≤ d)
    (hvanish : ∀ l : List (Fin n), wordCost cost l ≤ ((d : ℝ) + 2) * delta →
      OrdinaryDerivatives.word n l f ∈ P)
    (hcomparison : PersistentNormalComparison w cost M delta f d P)
    (hseparated : ∀ A B : Finset (Fin n), A.card = B.card →
      ∀ i, i ∈ A → i ∉ B → (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      M * (∏ j ∈ B, cost j) < ∏ j ∈ A, w j) :
    ∃ i : Fin n, ∃ c : ℂ, MvPolynomial.X i - MvPolynomial.C c ∈ P := by
  obtain ⟨r, hr, Q, hQr, hQnext, hQP, hQlo, hQhi, hpersist⟩ :=
    OrdinaryDerivatives.exists_persistent_component cost hcost delta hdelta f hf
      d P hP hheight hvanish
  let : Q.IsPrime := hQr.isPrime
  let : Algebra.EssFiniteType ℂ Q.ResidueField :=
    Algebra.EssFiniteType.comp ℂ (OrdinaryDerivatives.Polynomial n) Q.ResidueField
  have hfQ : f ∈ Q := hQr.le
    (self_mem_derivativeIdeal (OrdinaryDerivatives.partialFrame n) cost ((r : ℝ) * delta) f
      (mul_nonneg (Nat.cast_nonneg r) hdelta))
  have hQ0 : Q ≠ ⊥ := by
    intro h
    exact hf (by simpa only [h, Ideal.mem_bot] using hfQ)
  have hcomp := hcomparison r hr Q inferInstance hQP hQr hQnext hQlo hQhi hpersist
  have hker (p : OrdinaryDerivatives.Polynomial n) : primeResidueMap Q p = 0 ↔ p ∈ Q :=
    Ideal.algebraMap_residueField_eq_zero
  obtain ⟨i, c, hc⟩ := coordinate_constant_of_generic_normal_weight_comparison
    (primeResidueMap Q) Q hker hQ0 w cost M hcomp hseparated
  exact ⟨i, c, hQP hc⟩

theorem at_most_one_center_of_persistent_comparison {n : ℕ}
    (w cost : Fin n → ℝ) (M delta : ℝ) (hcost : ∀ i, 0 ≤ cost i) (hdelta : 0 ≤ delta)
    (f : OrdinaryDerivatives.Polynomial n) (hf : f ≠ 0) (d : ℕ)
    (P : Ideal (OrdinaryDerivatives.Polynomial n)) (hP : P.IsPrime) (hheight : P.height ≤ d)
    (hvanish : ∀ l : List (Fin n), wordCost cost l ≤ ((d : ℝ) + 2) * delta →
      OrdinaryDerivatives.word n l f ∈ P)
    (hcomparison : PersistentNormalComparison w cost M delta f d P)
    (hseparated : ∀ A B : Finset (Fin n), A.card = B.card →
      ∀ i, i ∈ A → i ∉ B → (∀ j, i < j → (j ∈ A ↔ j ∈ B)) →
      M * (∏ j ∈ B, cost j) < ∏ j ∈ A, w j)
    {J : Type*} (centers : J → Fin n → ℂ)
    (hinj : ∀ i, Function.Injective (fun j => centers j i))
    (j l : J) (hj : ∀ p ∈ P, MvPolynomial.eval (centers j) p = 0)
    (hl : ∀ p ∈ P, MvPolynomial.eval (centers l) p = 0) : j = l := by
  obtain ⟨i, c, hc⟩ := coordinate_constant_of_persistent_comparison
    w cost M delta hcost hdelta f hf d P hP hheight hvanish hcomparison hseparated
  have hjc := hj _ hc
  have hlc := hl _ hc
  simp only [MvPolynomial.eval_sub, MvPolynomial.eval_X, MvPolynomial.eval_C, sub_eq_zero] at hjc hlc
  exact hinj i (hjc.trans hlc.symm)

end PiExponent.OrdinaryComponentRigidity
end

end OAI

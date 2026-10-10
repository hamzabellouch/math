import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Basic.Complex.Basic
import OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree
import OAI.NumberTheory.PiExponent.Jets.DerivativeIdeals

namespace OAI

noncomputable section
namespace PiExponent.OrdinaryDerivatives

open scoped BigOperators
open DerivativeIdeals

abbrev Polynomial (n : ℕ) := MvPolynomial (Fin n) ℂ

def partialFrame (n : ℕ) (i : Fin n) : Derivation ℚ (Polynomial n) (Polynomial n) :=
  (MvPolynomial.pderiv i).restrictScalars ℚ

@[simp] theorem partialFrame_apply (n : ℕ) (i : Fin n) (p : Polynomial n) :
    partialFrame n i p = MvPolynomial.pderiv i p := rfl

theorem partialFrame_commute (n : ℕ) (i j : Fin n) :
    Commute (partialFrame n i).toLinearMap (partialFrame n j).toLinearMap := by
  apply LinearMap.ext
  intro p
  change MvPolynomial.pderiv i (MvPolynomial.pderiv j p) =
    MvPolynomial.pderiv j (MvPolynomial.pderiv i p)
  by_cases hij : i = j
  · subst j
    rfl
  · apply MvPolynomial.ext
    intro d
    simp only [MvPolynomial.coeff_pderiv, Finsupp.add_apply,
      Finsupp.single_apply, ite_eq_right hij, ite_eq_right (Ne.symm hij), add_zero]
    rw [show d + Finsupp.single i 1 + Finsupp.single j 1 =
      d + Finsupp.single j 1 + Finsupp.single i 1 by ac_rfl]
    ring

def word (n : ℕ) (l : List (Fin n)) (p : Polynomial n) : Polynomial n :=
  wordDerivative (partialFrame n) l p

@[simp] theorem word_nil (n : ℕ) (p : Polynomial n) : word n [] p = p := rfl
@[simp] theorem word_cons (n : ℕ) (i : Fin n) (l : List (Fin n)) (p : Polynomial n) :
    word n (i :: l) p = MvPolynomial.pderiv i (word n l p) := rfl

def ideal (n : ℕ) (cost : Fin n → ℝ) (bound : ℝ) (p : Polynomial n) : Ideal (Polynomial n) :=
  derivativeIdeal (partialFrame n) cost bound p

theorem supportBound_pderiv {n : ℕ} (W : Fin n → ℝ) (N : ℝ)
    (p : Polynomial n) (hp : WeightedSliceDegree.SupportBound W N p) (i : Fin n) :
    WeightedSliceDegree.SupportBound W (N - W i) (MvPolynomial.pderiv i p) := by
  intro d hd
  have hshift : d + Finsupp.single i 1 ∈ p.support := by
    apply MvPolynomial.mem_support_iff.mpr
    intro hz
    have hh := MvPolynomial.mem_support_iff.mp hd
    apply hh
    rw [MvPolynomial.coeff_pderiv, hz, zero_mul]
  apply (le_sub_iff_add_le).mpr
  have h := hp _ hshift
  simpa only [map_add, Finsupp.weight_single, one_smul] using h

theorem supportBound_word {n : ℕ} (W : Fin n → ℝ) (N : ℝ)
    (p : Polynomial n) (hp : WeightedSliceDegree.SupportBound W N p)
    (hW : ∀ i, 0 ≤ W i) (l : List (Fin n)) :
    WeightedSliceDegree.SupportBound W N (word n l p) := by
  induction l with
  | nil => exact hp
  | cons i l ih =>
    exact (supportBound_pderiv W N (word n l p) ih i).mono (sub_le_self N (hW i))

abbrev BoundedWords {n : ℕ} (cost : Fin n → ℝ) (bound : ℝ) :=
  {l : List (Fin n) // wordCost cost l ≤ bound}

def equations {n : ℕ} (cost : Fin n → ℝ) (bound : ℝ) (p : Polynomial n) :
    BoundedWords cost bound → Polynomial n := fun l => word n l.1 p

theorem span_equations {n : ℕ} (cost : Fin n → ℝ) (bound : ℝ) (p : Polynomial n) :
    Ideal.span (Set.range (equations cost bound p)) = ideal n cost bound p := by
  unfold ideal derivativeIdeal
  congr 1
  ext g
  constructor
  · rintro ⟨l, rfl⟩
    exact ⟨l.1, l.2, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨⟨l, hl⟩, rfl⟩

theorem equation_supportBound {n : ℕ} (cost W : Fin n → ℝ) (bound N : ℝ)
    (p : Polynomial n) (hp : WeightedSliceDegree.SupportBound W N p)
    (hW : ∀ i, 0 ≤ W i) (l : BoundedWords cost bound) :
    WeightedSliceDegree.SupportBound W N (equations cost bound p l) :=
  supportBound_word W N p hp hW l.1

theorem exists_persistent_component {n : ℕ}
    (cost : Fin n → ℝ) (hcost : ∀ i, 0 ≤ cost i)
    (delta : ℝ) (hdelta : 0 ≤ delta) (p : Polynomial n) (hp : p ≠ 0)
    (d : ℕ) (P : Ideal (Polynomial n)) (hP : P.IsPrime) (hheight : P.height ≤ d)
    (hvanish : ∀ l : List (Fin n), wordCost cost l ≤ ((d : ℝ) + 2) * delta → word n l p ∈ P) :
    ∃ r < d + 2, ∃ Q : Ideal (Polynomial n),
      Q ∈ (ideal n cost ((r : ℝ) * delta) p).minimalPrimes ∧
      Q ∈ (ideal n cost (((r : ℝ) + 1) * delta) p).minimalPrimes ∧
      Q ≤ P ∧ 1 ≤ Q.height ∧ Q.height ≤ d ∧
      ∀ g ∈ ideal n cost ((r : ℝ) * delta) p,
        ∀ l : List (Fin n), wordCost cost l ≤ delta → word n l g ∈ Q :=
  exists_persistent_derivative_component (partialFrame n) cost hcost delta hdelta p hp
    d P hP hheight hvanish

end PiExponent.OrdinaryDerivatives
end

end OAI

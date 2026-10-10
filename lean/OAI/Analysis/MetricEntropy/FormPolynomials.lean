import OAI.Analysis.MetricEntropy.SymmetricForms
import OAI.Analysis.MetricEntropy.SymmetricMultiplicity
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Algebra.Field.ZMod

namespace OAI

universe uK

/-!
# Actual polynomials of symmetric forms

The definitions sum over ordered basis tuples, exactly as the multilinear
form evaluation does. The diagonal coefficient of a basis multiset is its
ordered-tuple fiber cardinality times the value of the form. This coefficient
is nonzero in characteristic greater than the degree. Renaming every vector
block to the same coordinate proves nonvanishing for every index tuple,
including tuples with repeated indices.
-/

noncomputable section

namespace MetricEntropyDuality

open scoped BigOperators
open MvPolynomial

/-- The exponent vector of a multiset of basis indices. -/
def symExponent {r h : ℕ} (s : Sym (Fin r) h) : Fin r →₀ ℕ :=
  (s : Multiset (Fin r)).toFinsupp

theorem symExponent_injective {r h : ℕ} :
    Function.Injective (@symExponent r h) := by
  intro s t hst
  apply Subtype.ext
  exact Multiset.toFinsupp.injective hst

@[simp] theorem symExponent_eq_iff {r h : ℕ} (s t : Sym (Fin r) h) :
    symExponent s = symExponent t ↔ s = t :=
  symExponent_injective.eq_iff

/-- Every multiset exponent has precisely the prescribed total weight. -/
theorem symExponent_weight {r h : ℕ} (s : Sym (Fin r) h) :
    (symExponent s).sum (fun _ d => d) = h := by
  change ((s : Multiset (Fin r)).toFinsupp.sum (fun _ => id)) = h
  exact (Multiset.toFinsupp_sum_eq _).trans s.property

/-- Passing from an ordered tuple to a monomial counts each occurrence. -/
theorem symExponent_tupleSym {r h : ℕ} (b : Fin h → Fin r) :
    symExponent (tupleSym b) = ∑ j : Fin h, Finsupp.single (b j) 1 := by
  simp only [symExponent, coe_tupleSym]
  induction h with
  | zero => simp
  | succ h ih =>
      rw [List.ofFn_succ, ← Multiset.cons_coe, ← Multiset.singleton_add,
        Multiset.toFinsupp_add, Multiset.toFinsupp_singleton, Fin.sum_univ_succ, ih]

/-- The diagonal polynomial, formed from the actual ordered-tuple expansion. -/
def diagonalPolynomial {K : Type uK} [CommSemiring K] {r h : ℕ}
    (F : SymmetricForm K r h) : MvPolynomial (Fin r) K :=
  ∑ b : Fin h → Fin r, C (F (tupleSym b)) * ∏ j : Fin h, X (b j)

/-- The actual symbolic evaluation on a tuple of vector blocks. -/
def tuplePolynomial {K : Type uK} [CommSemiring K] {r h u : ℕ}
    (F : SymmetricForm K r h) (a : Fin h → Fin u) :
    MvPolynomial (Fin u × Fin r) K :=
  ∑ b : Fin h → Fin r, C (F (tupleSym b)) * ∏ j : Fin h, X (a j, b j)

theorem eval_diagonalPolynomial {K : Type uK} [CommSemiring K] {r h : ℕ}
    (F : SymmetricForm K r h) (x : Fin r → K) :
    MvPolynomial.eval x (diagonalPolynomial F) =
      SymmetricForm.eval F (fun _ => x) := by
  simp [diagonalPolynomial, SymmetricForm.eval, eval_mul]

theorem eval_tuplePolynomial {K : Type uK} [CommSemiring K] {r h u : ℕ}
    (F : SymmetricForm K r h) (a : Fin h → Fin u) (t : Fin u → Fin r → K) :
    MvPolynomial.eval (fun z => t z.1 z.2) (tuplePolynomial F a) =
      SymmetricForm.eval F (fun j => t (a j)) := by
  simp [tuplePolynomial, SymmetricForm.eval, eval_mul]

/-- Identifying all blocks with one vector gives the diagonal polynomial. -/
theorem rename_tuplePolynomial {K : Type uK} [CommSemiring K] {r h u : ℕ}
    (F : SymmetricForm K r h) (a : Fin h → Fin u) :
    MvPolynomial.rename Prod.snd (tuplePolynomial F a) = diagonalPolynomial F := by
  simp [tuplePolynomial, diagonalPolynomial, map_sum, map_prod]

theorem totalDegree_tuplePolynomial_le {K : Type uK} [CommSemiring K] [Nontrivial K]
    {r h u : ℕ} (F : SymmetricForm K r h) (a : Fin h → Fin u) :
    (tuplePolynomial F a).totalDegree ≤ h := by
  unfold tuplePolynomial
  apply totalDegree_finsetSum_le
  intro b _
  calc
    (C (F (tupleSym b)) * ∏ j : Fin h, X (a j, b j)).totalDegree ≤
        (C (F (tupleSym b)) : MvPolynomial (Fin u × Fin r) K).totalDegree +
          (∏ j : Fin h, (X (a j, b j) : MvPolynomial (Fin u × Fin r) K)).totalDegree :=
      totalDegree_mul _ _
    _ = (∏ j : Fin h, (X (a j, b j) : MvPolynomial (Fin u × Fin r) K)).totalDegree := by
      simp
    _ ≤ ∑ j : Fin h, (X (a j, b j) : MvPolynomial (Fin u × Fin r) K).totalDegree :=
      totalDegree_finsetProd _ _
    _ = h := by simp

theorem totalDegree_diagonalPolynomial_le {K : Type uK} [CommSemiring K] [Nontrivial K]
    {r h : ℕ} (F : SymmetricForm K r h) :
    (diagonalPolynomial F).totalDegree ≤ h := by
  let a : Fin h → Fin 1 := fun _ => 0
  calc
    (diagonalPolynomial F).totalDegree =
        (MvPolynomial.rename Prod.snd (tuplePolynomial F a)).totalDegree := by
      rw [rename_tuplePolynomial]
    _ ≤ (tuplePolynomial F a).totalDegree := totalDegree_rename_le _ _
    _ ≤ h := totalDegree_tuplePolynomial_le F a

private theorem diagonal_term_eq_monomial {K : Type uK} [CommSemiring K] {r h : ℕ}
    (F : SymmetricForm K r h) (b : Fin h → Fin r) :
    C (F (tupleSym b)) * (∏ j : Fin h, X (b j) : MvPolynomial (Fin r) K) =
      monomial (symExponent (tupleSym b)) (F (tupleSym b)) := by
  rw [symExponent_tupleSym]
  simpa only [MvPolynomial.X] using
    (monomial_sum_index (Finset.univ : Finset (Fin h))
      (fun j => Finsupp.single (b j) 1) (F (tupleSym b))).symm

/-- Distinct basis multisets yield distinct monomials. The coefficient is
exactly the ordered-tuple multiplicity, including every repeated basis index. -/
theorem coeff_diagonalPolynomial {K : Type uK} [CommSemiring K] {r h : ℕ}
    (F : SymmetricForm K r h) (s : Sym (Fin r) h) :
    (diagonalPolynomial F).coeff (symExponent s) = (symFiberCard s : K) * F s := by
  classical
  unfold diagonalPolynomial
  rw [coeff_sum]
  simp_rw [diagonal_term_eq_monomial, coeff_monomial, symExponent_eq_iff]
  calc
    (∑ b : Fin h → Fin r, if tupleSym b = s then F (tupleSym b) else 0) =
        ∑ b ∈ Finset.univ.filter (fun b : Fin h → Fin r => tupleSym b = s), F s := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : tupleSym b = s <;> simp [hb]
    _ = (symFiberCard s : K) * F s := by
      simp only [Finset.sum_const, nsmul_eq_mul, symFiberCard, Fintype.card_subtype]

/-- Characteristic greater than the degree prevents diagonal cancellation. -/
theorem diagonalPolynomial_ne_zero {p r h : ℕ} [Fact p.Prime]
    (hp : h < p) (F : SymmetricForm (ZMod p) r h) (hF : F ≠ 0) :
    diagonalPolynomial F ≠ 0 := by
  intro hz
  apply hF
  funext s
  have hc := congrArg (fun polynomial => polynomial.coeff (symExponent s)) hz
  simp only [coeff_diagonalPolynomial, AddMonoidAlgebra.coeff_zero,
    Finsupp.zero_apply] at hc
  exact (mul_eq_zero.mp hc).resolve_left (symFiberCard_cast_ne_zero s (Fact.out : p.Prime) hp)

/-- Every symbolic tuple evaluation is nonzero, with no distinct-index
hypothesis. The proof includes all repeated-index patterns. -/
theorem tuplePolynomial_ne_zero {p r h u : ℕ} [Fact p.Prime]
    (hp : h < p) (F : SymmetricForm (ZMod p) r h) (hF : F ≠ 0)
    (a : Fin h → Fin u) : tuplePolynomial F a ≠ 0 := by
  intro hz
  apply diagonalPolynomial_ne_zero hp F hF
  rw [← rename_tuplePolynomial F a, hz, map_zero]

/-- The diagonal degree is exactly the form degree, including degree zero. -/
theorem totalDegree_diagonalPolynomial {p r h : ℕ} [Fact p.Prime]
    (hp : h < p) (F : SymmetricForm (ZMod p) r h) (hF : F ≠ 0) :
    (diagonalPolynomial F).totalDegree = h := by
  classical
  obtain ⟨s, hs⟩ := Function.ne_iff.mp hF
  have hc : (diagonalPolynomial F).coeff (symExponent s) ≠ 0 := by
    rw [coeff_diagonalPolynomial]
    exact mul_ne_zero (symFiberCard_cast_ne_zero s (Fact.out : p.Prime) hp) hs
  apply le_antisymm (totalDegree_diagonalPolynomial_le F)
  simpa only [symExponent_weight] using
    (le_totalDegree (mem_support_iff.mpr hc))

/-- Identifying vector blocks cannot increase degree, so every tuple has
exactly degree `h`, even when its indices repeat. -/
theorem totalDegree_tuplePolynomial {p r h u : ℕ} [Fact p.Prime]
    (hp : h < p) (F : SymmetricForm (ZMod p) r h) (hF : F ≠ 0)
    (a : Fin h → Fin u) : (tuplePolynomial F a).totalDegree = h := by
  apply le_antisymm (totalDegree_tuplePolynomial_le F a)
  have hle := totalDegree_rename_le Prod.snd (tuplePolynomial F a)
  rw [rename_tuplePolynomial, totalDegree_diagonalPolynomial hp F hF] at hle
  exact hle

end MetricEntropyDuality

end

end OAI
